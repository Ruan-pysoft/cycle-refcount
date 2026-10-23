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

	Local, // create local variable

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

	Call,  // call var args..
	End,   // end closure definition
	Tail,  // rerun closure from the start
	Spill, // run closure in current environment

	Remark, // comment

	Quit, // quit program / closure
}

Operation :: struct {
	type: Operation_Type,

	var: Symbol,
	val: Value,
	args: []Value,
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

		idx := visitor.index - len(this.params) - 1
		visitor.index += 1

		for op in this.ops {
			vlen := op_visit_len(op)
			if vlen <= idx {
				idx -= vlen
				continue
			}

			if idx == 0 do return op.var, true
			else if idx == 1 do #partial switch op.type {
			case .Set_Var: fallthrough
			case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip:
				switch val in op.val {
				case Symbol: return val, true
				case Number: return next(visitor)
				case Gc_Ref(Closure): return val, true
				case: panic("unreachable")
				}

			case .Call:
				switch val in op.args[0] {
				case Symbol: return val, true
				case Number: return next(visitor)
				case Gc_Ref(Closure): return val, true
				case: panic("unreachable")
				}

			case: panic("unreachable")
			} else {
				ensure(op.type == .Call)
				switch val in op.args[idx-1] {
				case Symbol: return val, true
				case Number: return next(visitor)
				case Gc_Ref(Closure): return val, true
				case: panic("unreachable")
				}
			}
		}

		return {}, false
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
			case Number: return next(visitor)
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
	case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip: fallthrough
	case .Local: fallthrough
	case .Call, .Spill:
		ref_drop(op.var)
	}
	#partial switch op.type {
	case .Set_Var: fallthrough
	case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip:
		val_drop(op.val)
	}
	if op.type == .Call {
		for arg in op.args do val_drop(arg)
		delete(op.args)
	}
}
op_copy :: proc(op: Operation) -> Operation {
	#partial switch op.type {
	case .Set_Var, .Inc_Var, .Dec_Var: fallthrough
	case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip: fallthrough
	case .Local: fallthrough
	case .Call, .Spill:
		ref_copy(op.var)
	}
	#partial switch op.type {
	case .Set_Var: fallthrough
	case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip:
		val_copy(op.val)
	}
	if op.type == .Call {
		res := op
		res.args = make([]Value, len(op.args))
		for arg, idx in op.args do res.args[idx] = val_copy(arg)
		return res
	} else do return op
}

op_visit_len :: proc(op: Operation) -> int {
	switch op.type {
	case .Invalid: return 0

	case .Enter, .Exit: fallthrough
	case .Collect_Cycles, .Gc_Stats, .Inspect_Env: fallthrough
	case .Help: fallthrough
	case .End, .Tail: fallthrough
	case .Remark: fallthrough
	case .Quit:
		return 0

	case .Inc_Var, .Dec_Var: fallthrough
	case .Local: fallthrough
	case .Spill:
		return 1

	case .Set_Var: fallthrough
	case .Eq_Skip, .Ne_Skip, .Lt_Skip, .Le_Skip, .Gt_Skip, .Ge_Skip:
		return 2

	case .Call:
		return 1 + len(op.args)

	case: return 0
	}
}

Op_Type_Mapping :: struct {
	mnemonic: [3]byte,
	type: Operation_Type,
	full_name: string,
	docs: string,
}
op_type_map := [?] Op_Type_Mapping {
	{ "set", .Set_Var, "set",
		"sets a variable to the provided value; creates the variable in the current scope if it doesn't exist yet",
	},
	{ "inc", .Inc_Var, "increment",
		"increments the provided variable by one; the variable has to exist and contain a number",
	},
	{ "dec", .Dec_Var, "decrement",
		"decrements the provided variable by one; the variable has to exist and contain a number",
	},

	{ "eq-", .Eq_Skip, "eq-skip",
		"skips the following line if the provided variable is equal to the provided value",
	},
	{ "ne-", .Ne_Skip, "ne-skip",
		"skips the following line if the provided variable is not equal to the provided value",
	},
	{ "lt-", .Lt_Skip, "lt-skip",
		"skips the following line if the provided variable is less than the provided value",
	},
	{ "le-", .Le_Skip, "le-skip",
		"skips the following line if the provided variable is less than or equal to the provided value",
	},
	{ "gt-", .Gt_Skip, "gt-skip",
		"skips the following line if the provided variable is greater than the provided value",
	},
	{ "ge-", .Ge_Skip, "ge-skip",
		"skips the following line if the provided variable is greater than or equal to the provided value",
	},

	{ "eq?", .Eq_Skip, "eq?", "see eq-skip" },
	{ "ne?", .Ne_Skip, "ne?", "see ne-skip" },
	{ "lt?", .Lt_Skip, "lt?", "see lt-skip" },
	{ "le?", .Le_Skip, "le?", "see le-skip" },
	{ "gt?", .Gt_Skip, "gt?", "see gt-skip" },
	{ "ge?", .Ge_Skip, "ge?", "see ge-skip" },

	{ "loc", .Local, "local",
		"if the provided variable does not exist in the current scope, create it in the current scope and initialise it to zero",
	},

	{ "ent", .Enter, "enter",
		"enter a new sub-scope; roughly equivalent to { in C",
	},
	{ "exi", .Exit, "exit",
		"exit the current scope; roughly equivalent to } in C",
	},

	{ "col", .Collect_Cycles, "collect-cycles",
		"run cycle collection to free up any memory cycles",
	},
	{ "gc-", .Gc_Stats, "gc-stats",
		"print GC statistics (no of objects currently allocated)",
	},
	{ "ins", .Inspect_Env, "inspect-environment",
		"dump the contents of the current environment (scope) and all ancestors",
	},

	{ "hel", .Help, "help",
		"display this help text",
	},

	{ "cal", .Call, "call",
		"call the provided function with the provided arguments",
	},
	{ "end", .End, "end",
		"end a function definition",
	},
	{ "tai", .Tail, "tail",
		"begin execution of a function from the start again, keeping the current environment/scope (perform a tail call)",
	},
	{ "spi", .Spill, "spill",
		"call the provided function, but run it in the current scope rather than in its closed-over environment; note that you must set the arguments manually first!",
	},

	{ "rem", .Remark, "remark",
		"write a comment; you may put any text after the command and before the newline and it will be ignored",
	},

	{ "qui", .Quit, "quit",
		"quit out of the program or the current function",
	},
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
				fmt.eprintfln("error: a number %q is not a valid closure argument", part)
				delete(params)
				return {}, false
			} else if part == ":" {
				fmt.eprintfln("error: \":\" is not a valid closure argument")
				delete(params)
				return {}, false
			}

			append(&params, part)
		}

		if !found_end {
			fmt.eprintfln("error: a closure's parameter list should end with `->`")
			delete(params)
			return {}, false
		} else if len(line) != 0 {
			fmt.eprintfln("error: nothing should occur after `->` on the first line of a closure definition")
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

		return { type, sym_new(sym), val, {} }, true

	case .Inc_Var, .Dec_Var: fallthrough
	case .Local: fallthrough
	case .Spill:
		sym, has_sym := strings.split_iterator(&line, " ")
		if !has_sym {
			fmt.eprintfln("error: operation %q (%s) takes one argument, none provided", name, op_type_str(type))
			return {}, false
		}

		if len(line) != 0 {
			fmt.eprintfln("warning: operation %q (%s) takes only one argument, but junk was left after parsing variable name", name, op_type_str(type))
		}

		return { type, sym_new(sym), {}, {} }, true

	case .Call:
		sym, has_sym := strings.split_iterator(&line, " ")
		if !has_sym {
			fmt.eprintfln("error: operation %q (%s) takes at least one argument, but only one provided", name, op_type_str(type))
			return {}, false
		}

		args: [dynamic]Value
		for part in strings.split_iterator(&line, " ") {
			if part == ":" {
				fmt.eprintfln("error: encountered \":\" while parsing call command; cannot pass a closure directly, assign it to a variable first")
				for arg in args do val_drop(arg)
				delete(args)
				return {}, false
			}

			if '0' <= part[0] && part[0] <= '9' {
				val, ok := strconv.parse_int(part)
				if !ok {
					fmt.eprintfln("error: invalid integer %q", part)
					for arg in args do val_drop(arg)
					delete(args)
					return {}, false
				}
				append(&args, val)
			} else {
				append(&args, sym_new(part))
			}
		}

		return { type, sym_new(sym), {}, args[:] }, true

	case .Enter, .Exit: fallthrough
	case .Collect_Cycles, .Gc_Stats, .Inspect_Env: fallthrough
	case .Help: fallthrough
	case .End, .Tail: fallthrough
	case .Quit:
		if len(line) != 0 {
			fmt.eprintfln("warning: operation %q (%s) does not take any arguments, but junk was left after parsing operation name", name, op_type_str(type))
		}

		return { type, {}, {}, {} }, true

	case .Remark: return { type, {}, {}, {} }, true

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
		res.ptr.params = make([]Symbol, len(val.ptr.params))
		for param, idx in val.ptr.params {
			res.ptr.params[idx] = ref_copy(param)
		}
		res.ptr.ops = make([]Operation, len(val.ptr.ops))
		for op, idx in val.ptr.ops {
			res.ptr.ops[idx] = op_copy(op)
		}
		res.ptr.env = ref_copy(env)
		return res, true
	case: panic("unreachable")
	}
}

op_set_var :: proc(env: Gc_Ref(Env), var: Symbol, val: Value) {
	val, ok := resolve_val(env, val)
	if !ok do return

	if var_val, ok := env_get(env, var); ok {
		val_drop(var_val^)
		var_val^ = val
	} else {
		env_insert(env, ref_copy(var), val)
	}
}
op_inc_var :: proc(env: Gc_Ref(Env), var: Symbol) {
	if val, ok := env_get(env, var); ok do switch &v in val^ {
	case Symbol: fmt.eprintln("error: can only increment integer variables")
	case Number: v += 1
	case Gc_Ref(Closure): fmt.eprintln("error: can only increment integer variables")
	} else {
		fmt.eprintfln("error: variable %q doesn't exist", var.ptr^)
	}
}
op_dec_var :: proc(env: Gc_Ref(Env), var: Symbol) {
	if val, ok := env_get(env, var); ok do switch &v in val^ {
	case Symbol: fmt.eprintln("error: can only decrement integer variables")
	case Number: v -= 1
	case Gc_Ref(Closure): fmt.eprintln("error: can only decrement integer variables")
	} else {
		fmt.eprintfln("error: variable %q doesn't exist", var.ptr^)
	}
}
op_local :: proc(env: Gc_Ref(Env), var: Symbol) {
	_, var_in_env := assoc_lookup(env.ptr.assocs[:], var)
	if !var_in_env do env_insert(env, ref_copy(var), 0)
}
op_collect_cycles :: proc(envs: ..Gc_Ref(Env)) {
	fmt.println("running cycle collection...")
	for env in envs do gc_mark(env)
	gc_stats()
	gc_sweep()
	fmt.println("done!")
}
op_help :: proc() {
	fmt.println("The following commands are registered:")
	for mapping in op_type_map {
		fmt.printfln(" - {}", mapping.full_name)
		fmt.printfln("   : {}", mapping.docs)
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
	fmt.println("Call a closure like so:")
	fmt.println("  call closure_name arg1 arg2 arg3 ...")
	fmt.println("To quit the program, call the `quit` command")
	fmt.println("Only the first three letters of a command's name are significant")
}
op_call :: proc(env: Gc_Ref(Env), var: Symbol, args: []Value) {
	cls_val, has_cls := env_get(env, var)
	if !has_cls {
		fmt.eprintfln("error: variable %q doesn't exist", var.ptr^)
		return
	}

	cls, cls_is_cls := cls_val^.(Gc_Ref(Closure))
	if !cls_is_cls {
		fmt.eprintfln("error: cannot call non-closure value")
		return
	}

	if len(args) != len(cls.ptr.params) {
		fmt.eprintfln("error: mismatched argument count, expected {} got {}", len(cls.ptr.params), len(args))
		return
	}

	cls_env := env_new()
	cls_env.ptr.parent = ref_copy(cls.ptr.env)
	// fmt.eprintln(cls.ptr.params)
	for i in 0..<len(args) {
		val, ok := resolve_val(env, args[i])
		if !ok {
			ref_drop(cls_env)
			return
		}

		env_insert(cls_env, ref_copy(cls.ptr.params[i]), val)
	}

	cur_env := cls_env
	op_skip := false

	run_loop: for idx := 0; idx < len(cls.ptr.ops); idx += 1 {
		op := cls.ptr.ops[idx]

		if !op_skip do switch op.type {
		case .Set_Var: op_set_var(cur_env, op.var, op.val)
		case .Inc_Var: op_inc_var(cur_env, op.var)
		case .Dec_Var: op_dec_var(cur_env, op.var)

		case .Eq_Skip: op_skip = op_eq_skip(cur_env, op.var, op.val)
		case .Ne_Skip: op_skip = op_ne_skip(cur_env, op.var, op.val)
		case .Lt_Skip: op_skip = op_lt_skip(cur_env, op.var, op.val)
		case .Le_Skip: op_skip = op_le_skip(cur_env, op.var, op.val)
		case .Gt_Skip: op_skip = op_gt_skip(cur_env, op.var, op.val)
		case .Ge_Skip: op_skip = op_ge_skip(cur_env, op.var, op.val)

		case .Local: op_local(cur_env, op.var)

		case .Enter:
			new_env := env_new()
			new_env.ptr.parent = ref_copy(cur_env)
			cur_env = new_env
		case .Exit:
			if cur_env == cls_env {
				fmt.eprintln("error: cannot exit from closure's arguments environment")
			} else {
				old_env := cur_env
				cur_env = old_env.ptr.parent
				ref_drop(old_env)
			}

		case .Collect_Cycles: op_collect_cycles(cur_env, env)
		case .Gc_Stats:
			// TODO: mark before & unmark after?
			gc_stats()
		case .Inspect_Env: env_display(cur_env)

		case .Help: op_help()

		case .Call: op_call(cur_env, op.var, op.args)
		case .End:
			fmt.eprintfln("Invalid command %s (THIS IS A BUG, THIS CODE PATH SHOULD BE UNREACHABLE)", op_type_str(.End))
		case .Tail: idx = -1
		case .Spill: op_spill(cur_env, op.var)

		case .Remark: _ = 0

		case .Quit: break run_loop

		case .Invalid: panic("unreachable")
		}
		else do op_skip = false
	}

	if cur_env != cls_env {
		fmt.eprintln("warning: a closure should exit out from any extra environments it creates")
	}
	for cur_env != cls.ptr.env {
		old_env := cur_env
		cur_env = old_env.ptr.parent
		ref_drop(old_env)
	}
}
op_spill :: proc(env: Gc_Ref(Env), var: Symbol) {
	cls_val, has_cls := env_get(env, var)
	if !has_cls {
		fmt.eprintfln("error: variable %q doesn't exist", var.ptr^)
		return
	}

	cls, cls_is_cls := cls_val^.(Gc_Ref(Closure))
	if !cls_is_cls {
		fmt.eprintfln("error: cannot call non-closure value")
		return
	}

	cur_env := env
	op_skip := false

	run_loop: for idx := 0; idx < len(cls.ptr.ops); idx += 1 {
		op := cls.ptr.ops[idx]

		if !op_skip do switch op.type {
		case .Set_Var: op_set_var(cur_env, op.var, op.val)
		case .Inc_Var: op_inc_var(cur_env, op.var)
		case .Dec_Var: op_dec_var(cur_env, op.var)

		case .Eq_Skip: op_skip = op_eq_skip(cur_env, op.var, op.val)
		case .Ne_Skip: op_skip = op_ne_skip(cur_env, op.var, op.val)
		case .Lt_Skip: op_skip = op_lt_skip(cur_env, op.var, op.val)
		case .Le_Skip: op_skip = op_le_skip(cur_env, op.var, op.val)
		case .Gt_Skip: op_skip = op_gt_skip(cur_env, op.var, op.val)
		case .Ge_Skip: op_skip = op_ge_skip(cur_env, op.var, op.val)

		case .Local: op_local(cur_env, op.var)

		case .Enter:
			new_env := env_new()
			new_env.ptr.parent = ref_copy(cur_env)
			cur_env = new_env
		case .Exit:
			if cur_env == env {
				fmt.eprintln("error: cannot exit from closure's arguments environment")
			} else {
				old_env := cur_env
				cur_env = old_env.ptr.parent
				ref_drop(old_env)
			}

		case .Collect_Cycles: op_collect_cycles(cur_env, env)
		case .Gc_Stats:
			// TODO: mark before & unmark after?
			gc_stats()
		case .Inspect_Env: env_display(cur_env)

		case .Help: op_help()

		case .Call: op_call(cur_env, op.var, op.args)
		case .End:
			fmt.eprintfln("Invalid command %s (THIS IS A BUG, THIS CODE PATH SHOULD BE UNREACHABLE)", op_type_str(.End))
		case .Tail: idx = -1
		case .Spill: op_spill(cur_env, op.var)

		case .Remark: _ = 0

		case .Quit: break run_loop

		case .Invalid: panic("unreachable")
		}
		else do op_skip = false
	}

	if cur_env != env {
		fmt.eprintln("warning: a closure should exit out from any extra environments it creates")
	}
	for cur_env != env {
		old_env := cur_env
		cur_env = old_env.ptr.parent
		ref_drop(old_env)
	}
}
Cmp_Res :: enum {
	Eq,
	Lt,
	Gt,
	Incomparible,
	Type_Mismatch,
}
val_cmp :: proc(a, b: Value) -> Cmp_Res {
	switch a in a {
	case Symbol:
		b, ok := b.(Symbol)
		if !ok do return .Type_Mismatch
		cmp_res := strings.compare(a.ptr^, b.ptr^)
		return cmp_res == 0 ? .Eq : cmp_res < 0 ? .Lt : .Gt
	case Number:
		b, ok := b.(Number)
		if !ok do return .Type_Mismatch
		return a == b ? .Eq : a < b ? .Lt : .Gt
	case Gc_Ref(Closure):
		b, ok := b.(Gc_Ref(Closure))
		if !ok do return .Type_Mismatch
		return a.ptr == b.ptr ? .Eq : .Incomparible
	case: panic("unreachable")
	}
}
op_eq_skip :: proc(env: Gc_Ref(Env), var: Symbol, val: Value) -> (skip: bool) {
	if var_val, ok := env_get(env, var); ok {
		val, ok := resolve_val(env, val)
		if !ok do return

		skip = val_cmp(var_val^, val) == .Eq
		val_drop(val)
		return skip
	} else {
		fmt.eprintfln("error: variable %q is not defined", var.ptr^)
		return false
	}
}
op_ne_skip :: proc(env: Gc_Ref(Env), var: Symbol, val: Value) -> (skip: bool) {
	if var_val, ok := env_get(env, var); ok {
		val, ok := resolve_val(env, val)
		if !ok do return

		skip = val_cmp(var_val^, val) != .Eq
		val_drop(val)
		return skip
	} else {
		fmt.eprintfln("error: variable %q is not defined", var.ptr^)
		return false
	}
}
op_lt_skip :: proc(env: Gc_Ref(Env), var: Symbol, val: Value) -> (skip: bool) {
	if var_val, ok := env_get(env, var); ok {
		val, ok := resolve_val(env, val)
		if !ok do return

		skip = val_cmp(var_val^, val) == .Lt
		val_drop(val)
		return skip
	} else {
		fmt.eprintfln("error: variable %q is not defined", var.ptr^)
		return false
	}
}
op_le_skip :: proc(env: Gc_Ref(Env), var: Symbol, val: Value) -> (skip: bool) {
	if var_val, ok := env_get(env, var); ok {
		val, ok := resolve_val(env, val)
		if !ok do return

		cmp := val_cmp(var_val^, val)
		skip = cmp == .Lt || cmp == .Eq
		val_drop(val)
		return skip
	} else {
		fmt.eprintfln("error: variable %q is not defined", var.ptr^)
		return false
	}
}
op_gt_skip :: proc(env: Gc_Ref(Env), var: Symbol, val: Value) -> (skip: bool) {
	if var_val, ok := env_get(env, var); ok {
		val, ok := resolve_val(env, val)
		if !ok do return

		skip = val_cmp(var_val^, val) == .Gt
		val_drop(val)
		return skip
	} else {
		fmt.eprintfln("error: variable %q is not defined", var.ptr^)
		return false
	}
}
op_ge_skip :: proc(env: Gc_Ref(Env), var: Symbol, val: Value) -> (skip: bool) {
	if var_val, ok := env_get(env, var); ok {
		val, ok := resolve_val(env, val)
		if !ok do return

		cmp := val_cmp(var_val^, val)
		skip = cmp == .Gt || cmp == .Eq
		val_drop(val)
		return skip
	} else {
		fmt.eprintfln("error: variable %q is not defined", var.ptr^)
		return false
	}
}

main :: proc() {
	root_env := env_new()

	fmt.println("== Cycle-Collecting Refcount-Based GC Demo ==")
	fmt.println("Enter `help` to get a quick overview of available commands")

	cur_env := root_env
	op_skip := false

	run_loop: for {
		line := read_line("> ", 1024)
		_full_line := line
		defer delete(_full_line)

		line = strings.trim(line, " \t")
		if len(line) == 0 do continue

		op, has_op := parse_op(line)
		if !has_op do continue
		defer op_delete(op)

		if !op_skip do switch op.type {
		case .Set_Var: op_set_var(cur_env, op.var, op.val)
		case .Inc_Var: op_inc_var(cur_env, op.var)
		case .Dec_Var: op_dec_var(cur_env, op.var)

		case .Eq_Skip: op_skip = op_eq_skip(cur_env, op.var, op.val)
		case .Ne_Skip: op_skip = op_ne_skip(cur_env, op.var, op.val)
		case .Lt_Skip: op_skip = op_lt_skip(cur_env, op.var, op.val)
		case .Le_Skip: op_skip = op_le_skip(cur_env, op.var, op.val)
		case .Gt_Skip: op_skip = op_gt_skip(cur_env, op.var, op.val)
		case .Ge_Skip: op_skip = op_ge_skip(cur_env, op.var, op.val)

		case .Local: op_local(cur_env, op.var)

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

		case .Collect_Cycles: op_collect_cycles(cur_env)
		case .Gc_Stats:
			// TODO: mark before & unmark after?
			gc_stats()
		case .Inspect_Env:
			env_display(cur_env)

		case .Help: op_help()

		case .Call: op_call(cur_env, op.var, op.args)
		case .End:
			fmt.eprintfln("Invalid command %s -- %s should only be called to finish a closure definition", op_type_str(.End), op_type_str(.End))
		case .Tail:
			fmt.eprintfln("Invalid command %s -- %s should only be called inside of a closure", op_type_str(.Tail), op_type_str(.Tail))
		case .Spill: op_spill(cur_env, op.var)

		case .Remark: _ = 0

		case .Quit: break run_loop

		case .Invalid: panic("unreachable")
		}
		else do op_skip = false
	}

	fmt.eprintln("RUNNING FINAL GC CLEANUP...")
	gc_stats()
	gc_sweep()
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
