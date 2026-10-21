package cycle_refcount

import "core:fmt"

main :: proc() {
	ihandle, _ := gc_new(int, nil, nil)
	answer_handle, _ := gc_new_clone(42, nil, nil)

	fmt.println(ihandle)
	fmt.println(answer_handle)
	fmt.println(gc_get_typed_noref(answer_handle, int)^)
	fmt.println(_gc_store[0])
	fmt.println(_gc_store[0].ptr.(int))
	fmt.println(_gc_store[1])
	fmt.println(_gc_store[1].ptr.(int))

	gc_stats()
	gc_sweep()
	gc_stats()

	fmt.println(_gc_store[1])
	fmt.println(_gc_store[1].ptr.(int))
	fmt.println(answer_handle)
	fmt.println(gc_get_typed_noref(answer_handle, int)^)
}
