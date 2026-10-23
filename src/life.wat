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

    ;; --- Draw the blinker ---
    ;;         #
    ;;  ### -> # -> ### and back
    ;;         #

    ;; Add a blinker in the middle of the board.
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

    ;; --- Draw the glider ---
    ;;
    ;;     #
    ;;      #
    ;;    ###
    
    ;; draw the first row
    local.get $base_addr
    i32.const 1
    i32.add
    i32.const 1
    i32.store8 offset=10

    ;; draw the second row
    local.get $base_addr
    global.get $width
    i32.const 2
    i32.add
    i32.add
    i32.const 1
    i32.store8 offset=10

    ;; draw the third row
    local.get $base_addr
    global.get $width
    i32.const 2
    i32.mul
    i32.add
    i32.const 1
    i32.store8 offset=10

    local.get $base_addr
    global.get $width
    i32.const 2
    i32.mul
    i32.add
    i32.const 1
    i32.add
    i32.const 1
    i32.store8 offset=10

    local.get $base_addr
    global.get $width
    i32.const 2
    i32.mul
    i32.add
    i32.const 2
    i32.add
    i32.const 1
    i32.store8 offset=10

    ;; Return the base address of the current state buffer.
    local.get $base_addr
  )

  ;; cell[row][col - 1] -> idx - 1 + (idx % width == 0 ? width : 0)
  (func $move_left (param $idx i32) (result i32)
    local.get $idx
    i32.const 1
    i32.sub

    ;; Ternary condition
    global.get $width     ;; a: cond == 0
    i32.const 0           ;; b: cond != 0

    ;; condition
    local.get $idx
    global.get $width
    i32.rem_u
    i32.eqz

    select               ;; condition ? a : b
    
    i32.add
  )

  ;; cell[row][col + 1] -> idx + 1 - ((idx + 1) % width == 0 ? width : 0)
  (func $move_right (param $idx i32) (result i32)
    local.get $idx
    i32.const 1
    i32.add

    ;; Ternary condition
    global.get $width     ;; a: cond == 0
    i32.const 0           ;; b: cond != 0

    ;; condition
    local.get $idx
    i32.const 1
    i32.add
    global.get $width
    i32.rem_u
    i32.eqz

    select               ;; condition ? a : b

    i32.sub
  )

  ;; Update the game board and return the address of the current state buffer.
  (func $update (result i32)
    (local $read_addr i32)
    (local $write_addr i32)

    (local $total_cells i32)

    ;; In Game of Life, a unit update is composed by 9 cells. The center is
    ;; updated according to its 8 neighbors. Instead of compute all offsets,
    ;; we move three indices together: the current cell, the cell above, and the
    ;; cell below. That makes find the neighbors a matter a single -1 and +1
    ;; shifts.
    ;;
    ;; The above cell is always one row above (cell_idx - width) and the 
    ;; below cell is always one row below (cell_idx + width).
    (local $cell_idx i32)
    (local $above_cell_idx i32)
    (local $below_cell_idx i32)

    ;; Auxiliary variables for neighbour computations.
    (local $aux1 i32)
    (local $aux2 i32)
    (local $sum i32)
    (local $state i32)

    ;; Copy the current state buffer addresses into local variables.
    global.get $ptr_a
    local.set $read_addr

    global.get $ptr_b
    local.set $write_addr

    ;; Compute the total number of cells in the board.
    global.get $width
    global.get $height
    i32.mul
    local.set $total_cells

    ;; --- Initialize the cell indices. ---
    i32.const 0
    local.set $cell_idx

    ;; Initialize the above cell index.
    local.get $total_cells
    global.get $width
    i32.sub
    local.set $above_cell_idx

    ;; Initialize the below cell index.
    local.get $cell_idx
    global.get $width
    i32.add
    local.set $below_cell_idx

    ;; --- Main update loop for each cell. ---
    ;; Update Game of Life rules.
    ;; * A live cell with 2 or 3 live neighbors survives.
    ;; * A dead cell with exactly 3 live neighbors becomes alive.
    ;; * All other cells die or remain dead.
    (loop $update
      ;; --- Compute the sum of live neighbors for the current cell. ---

      ;; Initialise the sum of live neighbors to 0.
      i32.const 0
      local.set $sum

      ;; Compute the partial sum of the neighbours above.
      ;; cell[row - 1][col] -> above_cell_idx
      local.get $read_addr
      local.get $above_cell_idx
      i32.add
      i32.load8_u

      local.get $sum
      i32.add
      local.set $sum

      ;; cell[row - 1][col - 1] -> (move_left above_cell_idx)
      local.get $read_addr
      local.get $above_cell_idx
      call $move_left
      i32.add
      i32.load8_u

      local.get $sum
      i32.add
      local.set $sum

      ;; cell[row - 1][col + 1] -> (move_right above_cell_idx)
      local.get $read_addr
      local.get $above_cell_idx
      call $move_right
      i32.add
      i32.load8_u

      local.get $sum
      i32.add
      local.set $sum

      ;; Compute the partial sum of the neighbours below.
      ;; cell[row + 1][col] -> below_cell_idx
      local.get $read_addr
      local.get $below_cell_idx
      i32.add
      i32.load8_u

      local.get $sum
      i32.add
      local.set $sum

      ;; cell[row + 1][col - 1] -> (move_left below_cell_idx)
      local.get $read_addr
      local.get $below_cell_idx
      call $move_left
      i32.add
      i32.load8_u

      local.get $sum
      i32.add
      local.set $sum

      ;; cell[row + 1][col + 1] -> (move_right below_cell_idx)
      local.get $read_addr
      local.get $below_cell_idx
      call $move_right
      i32.add
      i32.load8_u

      local.get $sum
      i32.add
      local.set $sum

      ;; Compute the partial sum of the neighbours on the same row.
      ;; cell[row][col - 1] -> (move_left cell_idx)
      local.get $read_addr
      local.get $cell_idx
      call $move_left
      i32.add
      i32.load8_u

      local.get $sum
      i32.add
      local.set $sum

      ;; cell[row][col + 1] -> (move_right cell_idx)
      local.get $read_addr
      local.get $cell_idx
      call $move_right
      i32.add
      i32.load8_u

      local.get $sum
      i32.add
      local.set $sum

      ;; --- Update cell state based on the sum of neighbours. ---

      ;; * A cell with 3 neighbours is alive.
      ;; * A cell with 2 neighbours stays in its current state.
      ;; * Every other cell dies.
      ;;
      ;; (sum == 3) || (state && sum == 2)

      ;; Get cell current state
      local.get $read_addr
      local.get $cell_idx
      i32.add
      i32.load8_u
      local.tee $state

      local.get $sum
      i32.const 2
      i32.eq

      i32.and          ;; (state && sum == 2)
      
      local.get $sum
      i32.const 3
      i32.eq
      
      i32.or            ;; ((state && sum == 2) || sum == 3)
      local.set $state

      local.get $write_addr
      local.get $cell_idx
      i32.add
      local.get $state
      i32.store8
      

      ;; --- Increment the cell indices. ---
      ;; Using periodic boundary conditions, increment the cell indices with 
      ;; wrap-around,  (idx + 1) % total_cells
      local.get $above_cell_idx
      i32.const 1
      i32.add
      local.get $total_cells
      i32.rem_u
      local.set $above_cell_idx

      local.get $below_cell_idx
      i32.const 1
      i32.add
      local.get $total_cells
      i32.rem_u
      local.set $below_cell_idx

      ;; loop index
      local.get $cell_idx
      i32.const 1
      i32.add
      ;; Check if we have reached the end of the board.
      local.tee $cell_idx
      local.get $total_cells
      i32.lt_u
      br_if $update
    )

    ;; --- Swap the pointers to the current and previous state buffers. ---
    global.get $ptr_a
    global.get $ptr_b
    global.set $ptr_a    ;; copy without popping
    global.set $ptr_b

    ;; Return the address of the current state buffer.
    global.get $ptr_a
  )

  (export "init" (func $init))
  (export "update" (func $update))
)
