package cycle_refcount

import "base:runtime"

import "core:fmt"
import "core:mem"

Gc_Destroy_Proc :: #type proc(ptr: any)
Gc_Visit_Proc :: #type proc(ptr: any) -> Gc_Visitor
Gc_Visitor :: struct {
	this: rawptr,
	index: int,
	next: #type proc(visitor: ^Gc_Visitor) -> (handle: Gc_Handle, ok: bool),
}
Gc_Visitor_Typed :: struct($T: typeid) {
	this: ^T,
	index: int,
	next: #type proc(visitor: ^Gc_Visitor_Typed(T)) -> (handle: Gc_Handle, ok: bool),
}

gc_visitor_typed :: proc"contextless"(
	visitor: ^Gc_Visitor,
	$T: typeid,
) -> ^Gc_Visitor_Typed(T) {
	return cast(^Gc_Visitor_Typed(T)) visitor
}
gc_visitor_untyped :: proc"contextless"(visitor: ^Gc_Visitor_Typed($T)) -> ^Gc_Visitor {
	return cast(^Gc_Visitor) visitor
}

Gc_Info :: struct {
	ptr: any,
	generation: int,
	alive: bool,
	refcount: int,
	destroy: Gc_Destroy_Proc,
	visit: Gc_Visit_Proc,

	_visited: bool,
	_marked: bool,
}

Gc_Handle :: struct {
	index: int,
	generation: int,
	id: typeid,
}

GC_START_SIZE :: #config(GC_START_SIZE, 1024*1024)

_gc_store: [dynamic]Gc_Info
_gc_store_idx: int

@(init)
gc_init :: proc"contextless"() {
	context = runtime.default_context()
	_gc_store = make([dynamic]Gc_Info, GC_START_SIZE)
}

@(fini)
gc_fini :: proc"contextless"() {
	context = runtime.default_context()
	delete(_gc_store)
}

any_to_raw :: #force_inline proc"contextless"(a: any) -> runtime.Raw_Any {
	return transmute(runtime.Raw_Any) a
}
raw_to_any :: #force_inline proc"contextless"(r: runtime.Raw_Any) -> any {
	return transmute(any) r
}
any_raw_data :: #force_inline proc"contextless"(a: any) -> rawptr {
	return any_to_raw(a).data
}
any_to_ptr :: #force_inline proc"contextless"(a: any, $T: typeid) -> ^T {
	_ = a.(T) // trigger type assert
	return cast(^T) any_to_raw(a).data
}
ptr_to_any :: #force_inline proc"contextless"(p: ^$T) -> any {
	return raw_to_any({ p, T })
}

gc_record :: proc(ptr: ^$T, destroy: Gc_Destroy_Proc, visit: Gc_Visit_Proc) -> Gc_Handle {
	ptr := ptr_to_any(ptr)

	for i in _gc_store_idx..<len(_gc_store) {
		if !_gc_store[i].alive {
			_gc_store_idx = i+1

			_gc_store[i].ptr = ptr
			_gc_store[i].generation += 1
			_gc_store[i].alive = true
			_gc_store[i].refcount = 1
			_gc_store[i].destroy = destroy
			_gc_store[i].visit = visit

			assert(_gc_store[i]._visited == false)
			assert(_gc_store[i]._marked == false)

			return { i, _gc_store[i].generation, T }
		}
	}

	for i in 0..<_gc_store_idx {
		if !_gc_store[i].alive {
			_gc_store_idx = i+1

			_gc_store[i].ptr = ptr
			_gc_store[i].generation += 1
			_gc_store[i].alive = true
			_gc_store[i].refcount = 1
			_gc_store[i].destroy = destroy
			_gc_store[i].visit = visit

			assert(_gc_store[i]._visited == false)
			assert(_gc_store[i]._marked == false)

			return { i, _gc_store[i].generation, T }
		}
	}

	index := len(_gc_store)
	_gc_store_idx = len(_gc_store)+1
	append(&_gc_store, { ptr, 1, true, 1, destroy, visit, false, false })
	return { index, 1, T }
}

gc_new :: proc(
	$T: typeid,
	destroy: Gc_Destroy_Proc,
	visit: Gc_Visit_Proc,
	loc := #caller_location,
) -> (
	handle: Gc_Handle,
	err: mem.Allocator_Error,
) {
	return gc_record(mem.new(T, loc=loc) or_return, destroy, visit), nil
}

gc_new_clone :: proc(
	val: $T,
	destroy: Gc_Destroy_Proc,
	visit: Gc_Visit_Proc,
	loc := #caller_location,
) -> (
	handle: Gc_Handle,
	err: mem.Allocator_Error,
) {
	return gc_record(new_clone(val, loc=loc) or_return, destroy, visit), nil
}

_gc_get_handle :: proc(handle: Gc_Handle, loc := #caller_location) -> ^Gc_Info {
	if 0 > handle.index || handle.index >= len(_gc_store) {
		fmt.panicf("corrupt gc handle: {} is not a valid index into the object table", handle.index, loc=loc)
	}
	if handle.generation < 0 || handle.generation > _gc_store[handle.index].generation {
		fmt.panicf("corrupt gc handle: {} is not a valid generation for object slot {}", handle.generation, handle.index, loc=loc)
	}
	if handle.generation < _gc_store[handle.index].generation {
		fmt.panicf("use-after-free: object in slot {} of generation {} has already been freed", handle.index, handle.generation, loc=loc)
	}
	if !_gc_store[handle.index].alive {
		fmt.panicf(
			"use-after-free: object in slot {} of generation {} with type {} has already been freed",
			handle.index, handle.generation,
			any_to_raw(_gc_store[handle.index].ptr).id,
			loc=loc,
		)
	}

	return &_gc_store[handle.index]
}

gc_get :: proc(handle: Gc_Handle, loc := #caller_location) -> any {
	info := _gc_get_handle(handle, loc=loc)
	info.refcount += 1
	return info.ptr
}

gc_get_noref :: proc(handle: Gc_Handle, loc := #caller_location) -> any {
	return _gc_get_handle(handle, loc=loc).ptr
}

gc_get_typed :: proc(handle: Gc_Handle, $T: typeid, loc := #caller_location) -> ^T {
	info := _gc_get_handle(handle, loc=loc)
	_ = info.ptr.(T) // trigger type assert
	info.refcount += 1
	return any_to_ptr(info.ptr)
}

gc_get_typed_noref :: proc(handle: Gc_Handle, $T: typeid, loc := #caller_location) -> ^T {
	info := _gc_get_handle(handle, loc=loc)
	_ = info.ptr.(T) // trigger type assert
	return any_to_ptr(info.ptr, T)
}

gc_ref :: proc(handle: Gc_Handle, loc := #caller_location) {
	_gc_get_handle(handle, loc=loc).refcount += 1
}

gc_unref :: proc(handle: Gc_Handle, loc := #caller_location) {
	info := _gc_get_handle(handle, loc=loc)
	info.refcount -= 1
	if info.refcount == 0 {
		if info.destroy == nil {
			free(any_raw_data(info.ptr))
		} else {
			info.destroy(info.ptr)
		}

		info.alive = false
		info._visited = false
	}
}

gc_visit :: proc(root: Gc_Handle, cb: $C/proc(handle: Gc_Handle) -> (ok: bool)) {
	if !cb(root) do return
	root_info := _gc_get_handle(root)
	if root_info._visited do return
	root_info._visited = true
	defer _gc_get_handle(root)._visited = false

	if root_info.visit != nil {
		visitor := root_info.visit(root_info.ptr)

		for handle in visitor->next() {
			gc_visit(handle, cb)
		}
	}
}
gc_visit_poly :: proc(
	root: Gc_Handle,
	arg: $T,
	cb: $C/proc(handle: Gc_Handle, arg: T) -> (ok: bool),
) {
	if !cb(root, arg) do return
	root_info := _gc_get_handle(root)
	if root_info._visited do return
	root_info._visited = true
	defer _gc_get_handle(root)._visited = false

	if root_info.visit != nil {
		visitor := root_info.visit(root_info.ptr)

		for handle in visitor->next() {
			gc_visit_poly(handle, arg, cb)
		}
	}
}

gc_mark :: proc(root: Gc_Handle) {
	gc_visit(root, proc(handle: Gc_Handle) -> (ok: bool) {
		_gc_get_handle(handle)._marked = true
		return true
	})
}
gc_sweep :: proc() {
	for &info, idx in _gc_store {
		if info.alive && !info._marked {
			gc_unref({ idx, info.generation, nil })
		}
		info._marked = false
	}
}

gc_stats :: proc() {
	objects := 0
	marked  := 0

	for &info, idx in _gc_store {
		if info.alive {
			objects += 1
			if info._marked do marked += 1
		}
	}

	fmt.eprintln()
	fmt.eprintfln("== GC STATS ==")
	fmt.eprintfln("Space for {} objects has been allocated", len(_gc_store))
	fmt.eprintfln("{} objects are currently allocated", objects)
	fmt.eprintfln("{} objects are currently marked", marked)
	fmt.eprintln()
}

Gc_Ref :: struct($T: typeid) {
	using handle: Gc_Handle,
	ptr: ^T,
}

ref_of :: proc(handle: Gc_Handle, $T: typeid, loc := #caller_location) -> Gc_Ref(T) {
	return { handle, gc_get_typed_noref(handle, T, loc=loc) }
}

ref_copy :: proc(ref: Gc_Ref($T), loc := #caller_location) -> Gc_Ref(T) {
	gc_ref(ref, loc=loc)
	return ref
}

ref_drop :: proc(ref: Gc_Ref($T), loc := #caller_location) {
	gc_unref(ref, loc=loc)
}
