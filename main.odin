package cycle_refcount

import "core:fmt"
import "core:io"
import "core:os"
import "core:slice"
import "core:slice/heap"
import "core:strconv"
import "core:strings"
import "core:sys/posix"
import "core:sys/windows"

Symbol  :: Gc_Ref(string)
Number  :: int

Closure :: struct {
	env: Gc_Ref(Env),
	params: []Symbol,
	ops: []Operation,
}

Value :: union {
	Symbol,
	Number,
	Gc_Ref(Closure),
}

Assoc :: struct {
	var: Symbol,
	val: Value,
}
assoc_less :: proc(a, b: Assoc) -> bool {
	return a.var.ptr^ < b.var.ptr^
}
assoc_lookup :: proc(heap: []Assoc, key: Symbol, start_at := 0) -> (idx: int, ok: bool) {
	if start_at >= len(heap) do return -1, false

	if heap[start_at].var.ptr^ == key.ptr^ do return start_at, true
	else if heap[start_at].var.ptr^ < key.ptr^ do return -1, false

	lidx := start_at*2 + 1
	ridx := start_at*2 + 2

	if idx, ok = assoc_lookup(heap, key, lidx); ok do return idx, ok
	else do return assoc_lookup(heap, key, ridx)
}
Env :: struct {
	parent: Gc_Ref(Env),

	assocs: [dynamic]Assoc,
}

Operation_Type :: enum {
	Invalid = 0,

	Set_Var, // var = val
	Inc_Var, // var++
	Dec_Var, // var--

	Eq_Skip, // if var == val skip line
	Ne_Skip, // if var != val skip line
	Lt_Skip, // if var <  val skip line
	Le_Skip, // if var <= val skip line
	Gt_Skip, // if var >  val skip line
	Ge_Skip, // if var >= val skip line

	Enter, // create enclosing environment
	Exit,  // leave top environment

	Collect_Cycles, // do a cycle collection
	Gc_Stats,       // display GC stats
	Inspect_Env,    // display the current environment

	Help, // display help

	// TODO: Call, // call closure
	End, // end closure definition def

	Quit, // quit program / closure
}

Operation :: struct {
	type: Operation_Type,

	var: Symbol,
	val: Value,
}

sym_destroy :: proc(sym: any) {
	sym := any_to_ptr(sym, string)
	delete(sym^)
	free(sym)
}
sym_new :: proc(from: string) -> Symbol {
	// TODO: handle allocator error
	res, _ := gc_new_clone(strings.clone(from), sym_destroy, nil)
	return ref_of(res, string)
}

cls_destroy :: proc(cls: any) {
	cls := any_to_ptr(cls, Closure)
	if cls.env.ptr != nil do ref_drop(cls.env)
	for param in cls.params {
		ref_drop(param)
	}
	delete(cls.params)
	for op in cls.ops {
		op_delete(op)
	}
	delete(cls.ops)
	free(cls)
}
cls_visit :: proc(cls: any) -> Gc_Visitor {
	return transmute(Gc_Visitor) Gc_Visitor_Typed(Closure) {
		this = any_to_ptr(cls, Closure),
		index = 0,
		next = next,
	}

	next :: proc(
		visitor: ^Gc_Visitor_Typed(Closure),
	) -> (handle: Gc_Handle, ok: bool) {
		if visitor.index < 0 do return {}, false
		// defer doesn't seem to work??
		//defer visitor.index += 1
		this := visitor.this

		if visitor.index == 0 {
			visitor.index += 1
			if this.env.ptr != nil do return this.env, true
			else do return next(visitor)
		}
		if visitor.index <= len(this.params) {
			res := this.params[visitor.index-1]
			visitor.index += 1
			return res, true
		}

		op_idx := visitor.index - len(this.params) - 1
		visitor.index += 1
		if op_idx/2 >= len(this.ops) do return {}, false
		op := this.ops[op_idx/2]

		if op_idx%2 == 0 do #partial switch op.type {
		case .Set_Var, .Inc_Var, .Dec_Var: fallthrough
		case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip:
			return op.var, true
		case: return next(visitor)
		} else do #partial switch op.type {
		case .Set_Var: fallthrough
		case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip:
			switch val in op.val {
			case Symbol: return val, true
			case Number: return next(visitor)
			case Gc_Ref(Closure): return val, true
			case: panic("unreachable")
			}
		case: return next(visitor)
		}
	}
}
cls_new :: proc() -> Gc_Ref(Closure) {
	// TODO: handle allocator error
	res, _ := gc_new(Closure, cls_destroy, cls_visit)
	return ref_of(res, Closure)
}

val_copy :: proc(val: Value) -> Value {
	switch val in val {
	case Symbol: ref_copy(val)
	case Number:
	case Gc_Ref(Closure): ref_copy(val)
	}
	return val
}
val_drop :: proc(val: Value) {
	switch val in val {
	case Symbol: ref_drop(val)
	case Number:
	case Gc_Ref(Closure): ref_drop(val)
	}
}

env_destroy :: proc(env: any) {
	env := any_to_ptr(env, Env)
	if env.parent.ptr != nil do ref_drop(env.parent)
	for assoc in env.assocs {
		ref_drop(assoc.var)
		val_drop(assoc.val)
	}
	delete(env.assocs)
	free(env)
}
env_visit :: proc(env: any) -> Gc_Visitor {
	return transmute(Gc_Visitor) Gc_Visitor_Typed(Env) {
		this = any_to_ptr(env, Env),
		index = 0,
		next = next,
	}

	next :: proc(
		visitor: ^Gc_Visitor_Typed(Env),
	) -> (handle: Gc_Handle, ok: bool) {
		if visitor.index < 0 do return {}, false
		// defer doesn't seem to work??
		//defer visitor.index += 1
		this := visitor.this

		if visitor.index == 0 {
			visitor.index += 1
			if this.parent.ptr != nil do return this.parent, true
			else do return next(visitor)
		}
		idx := visitor.index - 1
		visitor.index += 1
		if idx/2 < len(this.assocs) {
			assoc := this.assocs[idx/2]

			if idx%2 == 0 do return assoc.var, true
			else do switch val in assoc.val {
			case Symbol: return val, true
			case Number: next(visitor)
			case Gc_Ref(Closure): return val, true
			}
		}

		return {}, false
	}
}
env_new :: proc() -> Gc_Ref(Env) {
	// TODO: handle allocator error
	res, _ := gc_new(Env, env_destroy, env_visit)
	return ref_of(res, Env)
}

env_get :: proc(env: Gc_Ref(Env), sym: Symbol) -> (val: ^Value, has_val: bool) {
	idx, ok := assoc_lookup(env.ptr.assocs[:], sym)
	if ok do return &env.ptr.assocs[idx].val, true
	else if env.ptr.parent.ptr != nil do return env_get(env.ptr.parent, sym)
	else do return nil, false
}
// WARN: env_insert does not do *any* gc management
env_insert :: proc(env: Gc_Ref(Env), sym: Symbol, val: Value) {
	append(&env.ptr.assocs, { sym, val })
	heap.push(env.ptr.assocs[:], assoc_less)
}

env_display :: proc(env: Gc_Ref(Env)) {
	if env.ptr.parent.ptr != nil do env_display(env.ptr.parent)

	fmt.printfln("{{ env {}#{}", env.index, env.generation)

	for assoc in env.ptr.assocs {
		var_info := _gc_get_handle(assoc.var)
		fmt.printf("  {}%q: ", var_info.refcount, assoc.var.ptr^)
		switch val in assoc.val {
		case Symbol:
			val_info := _gc_get_handle(val)
			fmt.printfln("{}%q", val_info.refcount, val.ptr^)
		case Number: fmt.println(val)
		case Gc_Ref(Closure):
			val_info := _gc_get_handle(val)
			fmt.printfln(
				"{}<closure over env {}#{}>",
				val_info.refcount,
				val.ptr.env.index,
				val.ptr.env.generation,
			)
		case: panic("unreachable")
		}
	}

	fmt.println("}")
}

op_delete :: proc(op: Operation) {
	#partial switch op.type {
	case .Set_Var, .Inc_Var, .Dec_Var: fallthrough
	case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip:
		ref_drop(op.var)
	}
	#partial switch op.type {
	case .Set_Var: fallthrough
	case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip:
		val_drop(op.val)
	}
}
op_copy :: proc(op: Operation) {
	#partial switch op.type {
	case .Set_Var, .Inc_Var, .Dec_Var: fallthrough
	case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip:
		ref_copy(op.var)
	}
	#partial switch op.type {
	case .Set_Var: fallthrough
	case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip:
		val_copy(op.val)
	}
}

Op_Type_Mapping :: struct {
	mnemonic: [3]byte,
	type: Operation_Type,
	full_name: string,
}
op_type_map := [?] Op_Type_Mapping {
	{ "set", .Set_Var, "set" },
	{ "inc", .Inc_Var, "increment" },
	{ "dec", .Dec_Var, "decrement" },

	{ "eq-", .Eq_Skip, "eq-skip" },
	{ "ne-", .Ne_Skip, "ne-skip" },
	{ "lt-", .Lt_Skip, "lt-skip" },
	{ "le-", .Le_Skip, "le-skip" },
	{ "gt-", .Gt_Skip, "gt-skip" },
	{ "ge-", .Ge_Skip, "ge-skip" },

	{ "ent", .Enter, "enter" },
	{ "exi", .Exit, "exit" },

	{ "col", .Collect_Cycles, "collect-cycles" },
	{ "gc-", .Gc_Stats, "gc-stats" },
	{ "ins", .Inspect_Env, "inspect-environment" },

	{ "hel", .Help, "help" },

	// TODO: { "cal", .Call, "call" },
	{ "end", .End, "end" },

	{ "qui", .Quit, "quit" },
}
op_type_str :: proc(op_type: Operation_Type) -> string {
	for mapping in op_type_map {
		if mapping.type == op_type do return mapping.full_name
	}

	return "invalid"
}

// NOTE: line needs to be pre-trimmed!
parse_val :: proc(line: string) -> (val: Value, ok: bool) {
	line := line

	val_str, has_val := strings.split_iterator(&line, " ")
	assert(has_val)

	if val_str == ":" {
		// closure

		params: [dynamic]string
		found_end := false
		for part in strings.split_iterator(&line, " ") {
			if part == "->" {
				found_end = true
				break
			} else if '0' <= part[0] && part[0] <= '9' {
				fmt.eprintln("error: a number %q is not a valid closure argument", part)
				delete(params)
				return {}, false
			} else if part == ":" {
				fmt.eprintln("error: \":\" is not a valid closure argument")
				delete(params)
				return {}, false
			}

			append(&params, part)
		}

		if !found_end {
			fmt.eprintln("error: a closure's parameter list should end with `->`")
			delete(params)
			return {}, false
		} else if len(line) != 0 {
			fmt.eprintln("error: nothing should occur after `->` on the first line of a closure definition")
			delete(params)
			return {}, false
		}

		body: [dynamic]Operation

		for {
			line := read_line("... ", 1024)
			_full_line := line
			defer delete(_full_line)

			line = strings.trim(line, " \t")
			if len(line) == 0 do continue

			op, has_op := parse_op(line)
			if !has_op {
				delete(params)
				for op in body do op_delete(op)
				delete(body)
				return {}, false
			}

			if op.type == .End {
				op_delete(op)
				break
			}

			append(&body, op)
		}

		cls := cls_new()
		cls.ptr.params = make([]Symbol, len(params))
		for param, ix in params do cls.ptr.params[ix] = sym_new(param)
		delete(params)
		cls.ptr.ops = body[:]

		return cls, true
	} else if '0' <= val_str[0] && val_str[0] <= '9' {
		// number

		if len(line) != 0 {
			fmt.eprintln("warning: junk was left after parsing value")
		}

		val, ok := strconv.parse_int(val_str)
		if !ok {
			fmt.eprintfln("error: invalid integer %q", val_str)
			return {}, false
		}
		return val, true
	} else {
		// identifier

		if len(line) != 0 {
			fmt.eprintln("warning: junk was left after parsing value")
		}

		return sym_new(val_str), true
	}
}

// NOTE: line needs to be pre-trimmed!
parse_op :: proc(line: string) -> (op: Operation, ok: bool) {
	line := line

	name, has_name := strings.split_iterator(&line, " ")
	assert(has_name)
	if len(name) < 3 {
		fmt.eprintfln("error: an operation name should be at least three characters long, got %q", name)
		return {}, false
	}

	type := Operation_Type.Invalid
	for &mapping in op_type_map {
		if name[:3] == transmute(string) mapping.mnemonic[:] {
			type = mapping.type
			break
		}
	}
	if type == .Invalid {
		fmt.eprintfln("error: invalid operation name %q, enter `help` to get a list of operations", name)
		return {}, false
	}

	switch type {
	case .Set_Var: fallthrough
	case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip:
		sym, has_sym := strings.split_iterator(&line, " ")
		if !has_sym {
			fmt.eprintfln("error: operation %q (%s) takes two arguments, none provided", name, op_type_str(type))
			return {}, false
		}

		if len(line) == 0 {
			fmt.eprintfln("error: operation %q (%s) takes two arguments, one provided", name, op_type_str(type))
			return {}, false
		}
		val := parse_val(line) or_return

		return { type, sym_new(sym), val }, true

	case .Inc_Var, .Dec_Var:
		sym, has_sym := strings.split_iterator(&line, " ")
		if !has_sym {
			fmt.eprintfln("error: operation %q (%s) takes one argument, none provided", name, op_type_str(type))
			return {}, false
		}

		if len(line) != 0 {
			fmt.eprintln("warning: operation %q (%s) takes only one argument, but junk was left after parsing variable name", name, op_type_str(type))
		}

		return { type, sym_new(sym), {} }, true

	// TODO: case .Call: ...

	case .Enter, .Exit: fallthrough
	case .Collect_Cycles, .Gc_Stats, .Inspect_Env: fallthrough
	case .Help: fallthrough
	case .End: fallthrough
	case .Quit:
		if len(line) != 0 {
			fmt.eprintln("warning: operation %q (%s) does not take any arguments, but junk was left after parsing operation name", name, op_type_str(type))
		}

		return { type, {}, {} }, true

	case .Invalid: fallthrough
	case: panic("unreachable")
	}
}

resolve_val :: proc(env: Gc_Ref(Env), raw_val: Value) -> (val: Value, ok: bool) {
	switch val in raw_val {
	case Symbol:
		var_val, has_val := env_get(env, val)
		if !has_val {
			fmt.eprintfln("error: variable %q is not defined in the current scope", val)
			return {}, false
		}
		return val_copy(var_val^), true
	case Number:
		return val, true
	case Gc_Ref(Closure):
		res := cls_new()
		res.ptr^ = val.ptr^
		for param in res.ptr.params {
			ref_copy(param)
		}
		for op in res.ptr.ops {
			op_copy(op)
		}
		res.ptr.env = ref_copy(env)
		return res, true
	case: panic("unreachable")
	}
}

main :: proc() {
	root_env := env_new()

	fmt.println("== Cycle-Collecting Refcount-Based GC Demo ==")
	fmt.println("Enter `help` to get a quick overview of available commands")

	cur_env := root_env

	for {
		line := read_line("> ", 1024)
		_full_line := line
		defer delete(_full_line)

		line = strings.trim(line, " \t")
		if len(line) == 0 do continue

		op, has_op := parse_op(line)
		if !has_op do continue
		defer op_delete(op)

		switch op.type {
		case .Set_Var:
			val, ok := resolve_val(cur_env, op.val)
			if !ok do break

			if var_val, ok := env_get(cur_env, op.var); ok {
				val_drop(var_val^)
				var_val^ = val
			} else {
				env_insert(cur_env, ref_copy(op.var), val)
			}
		case .Inc_Var: panic("TODO")
		case .Dec_Var: panic("TODO")

		case .Eq_Skip: panic("TODO")
		case .Ne_Skip: panic("TODO")
		case .Lt_Skip: panic("TODO")
		case .Le_Skip: panic("TODO")
		case .Gt_Skip: panic("TODO")
		case .Ge_Skip: panic("TODO")

		case .Enter:
			new_env := env_new()
			new_env.ptr.parent = ref_copy(cur_env)
			cur_env = new_env
		case .Exit:
			if cur_env == root_env {
				fmt.eprintln("error: cannot exit from root environment")
			} else {
				old_env := cur_env
				cur_env = old_env.ptr.parent
				ref_drop(old_env)
			}

		case .Collect_Cycles:
			fmt.println("running cycle collection...")
			gc_mark(root_env)
			gc_stats()
			gc_sweep()
			fmt.println("done!")
		case .Gc_Stats:
			// TODO: mark before & unmark after?
			gc_stats()
		case .Inspect_Env:
			env_display(cur_env)

		case .Help:
			fmt.println("The following commands are registered:")
			for mapping in op_type_map {
				fmt.printfln(" - {}", mapping.full_name)
			}
			fmt.println("Enter a command that takes no arguments like so:")
			fmt.println("  name")
			fmt.println("Enter a command that only takes a variable like so:")
			fmt.println("  name variable")
			fmt.println("Enter a command that takes a variable and a value like so:")
			fmt.println("(value being a number)")
			fmt.println("  name variable 123")
			fmt.println("(value being the value of a variable)")
			fmt.println("  name variable other_variable")
			fmt.println("(value being a closure definition)")
			fmt.println("  name variable : arg1 arg2 ->")
			fmt.println("  ... cmd1")
			fmt.println("  ... cmd2")
			fmt.println("  ... end")
			fmt.println("To quit the program, call the `quit` command")
			fmt.println("Only the first three letters of a command's name are significant")

		case .End:
			fmt.eprintfln("Invalid command %s -- %s should only be called to finish a closure definition", op_type_str(.End), op_type_str(.End))

		case .Quit: return

		case .Invalid: panic("unreachable")
		}
	}
}

read_line :: proc(
	prompt: string,
	max_len: int,
	passwd := false,
	allocator := context.allocator,
) -> string {
	res := make([dynamic]u8, 0, max_len)

	when ODIN_OS == .Linux || ODIN_OS == .Darwin || ODIN_OS == .FreeBSD || ODIN_OS == .OpenBSD || ODIN_OS == .NetBSD {
		old_termios, new_termios: posix.termios
		if passwd {
			ensure(posix.tcgetattr(
				posix.STDIN_FILENO,
				&old_termios,
			) == .OK)
			new_termios = old_termios
			new_termios.c_lflag -= { .ECHO, .ECHONL }
			ensure(posix.tcsetattr(
				posix.STDIN_FILENO,
				.TCSAFLUSH,
				&new_termios,
			) == .OK)
		}
		defer if passwd {
			ensure(posix.tcsetattr(
				posix.STDIN_FILENO,
				.TCSAFLUSH,
				&old_termios,
			) == .OK)
		}
	} else when ODIN_OS == .Windows {
		old_mode, new_mode: u32
		if passwd {
			ensure(windows.GetConsoleMode(
				windows.STD_INPUT_HANDLE,
				&old_mode,
			) == windows.TRUE)
			new_mode = old_mode & ~windows.ENABLE_ECHO_INPUT
			ensure(windows.SetConsoleMode(
				windows.STD_INPUT_HANDLE,
				new_mode,
			) == windows.TRUE)
		}
		defer if passwd {
			ensure(windows.SetConsoleMode(
				windows.STD_INPUT_HANDLE,
				old_mode,
			) == windows.TRUE)
		}
	} else do #panic("Unsupported OS")

	fmt.print(prompt)
	os.flush(os.stdout)
	inp := os.to_reader(os.stdin)
	for {
		b, err := io.read_byte(inp)
		if err == .EOF do break
		else if err != nil do fmt.panicf("{}", err)
		if b == '\n' do break

		if len(res) == max_len {
			fmt.eprintfln("\nERROR: Input should be at most {} characters long!",
				max_len,
			)
			fmt.print(prompt)
			os.flush(os.stdout)
			clear(&res)

			for {
				b, err = io.read_byte(inp)
				if err == .EOF do break
				else if err != nil do fmt.panicf("{}", err)
				if b == '\n' do break
			}
		} else do append(&res, b)
	}

	if passwd do fmt.println()

	return transmute(string) res[:]
}
