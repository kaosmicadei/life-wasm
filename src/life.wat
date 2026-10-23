(module
  (memory (export "memory") 1)  ;; 1 page of memory (64KiB)

  ;; For the moment we fix the size of the game board to 32x32 cells.
  (global $width i32 (i32.const 32))
  (global $height i32 (i32.const 32))

  ;; For the zero-copy access, we use two buffers to hold the state of the game: 
  ;; one for the current state and one for the previous state. After each update
  ;; we swap the pointers to these buffers.
  (global $ptr_a (mut i32) (i32.const 0))
  (global $ptr_b (mut i32) (i32.const 1024))  ;; 32x32 cells, 1 byte per cell

  ;; Initialises the game board and returns the address of the current state buffer.
  (func $init (result i32)
    (local $cell_idx i32)

    (local $base_addr i32)

    global.get $ptr_a
    local.set $base_addr

    ;; --- Add a blinker in the middle of the board. ---
    ;;         #
    ;;  ### -> # -> ### and back
    ;;         #

    ;; Compute the center of the board.
    global.get $width
    global.get $height
    i32.mul              ;; total cells = width * height
    i32.const 2
    i32.div_u            ;; half board
    ;; subtract half the width to get the center cell index
    global.get $width
    i32.const 2
    i32.div_u
    i32.sub
    
    ;; Set the center cell as alive (1).
    local.tee $cell_idx
    local.get $base_addr
    i32.add
    i32.const 1
    i32.store8

    ;; Set the left cell of the blinker as alive (1).
    local.get $cell_idx
    local.get $base_addr
    i32.const -1
    i32.add
    i32.add               ;; ptr_a[cell_idx - 1]

    i32.const 1
    i32.store8

    ;; Set the right cell of the blinker as alive (1).
    local.get $cell_idx
    local.get $base_addr
    i32.const 1
    i32.add
    i32.add               ;; ptr_a[cell_idx + 1]
    
    i32.const 1
    i32.store8

    ;; Return the base address of the current state buffer.
    local.get $base_addr
  )

  (export "init" (func $init))
)
