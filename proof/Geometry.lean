/-
In the `life.wat` file, it's use a linear indexing for the 2D grid instead of the
usual 2D indexing. However, since the grid uses periodic boundary conditions,
when updating the status of a cell, we need to wrap around the indices correctly.

For the row index, that wrapper is trivial. The column index, however, requires
careful handling.

The usual wrap-around for the column uses the following rules
* Left shift: grid[row][(col + w - 1) % w]
* Right shift: grid[row][(col + 1) % w]

To obtain the linear index for both shifts we compute:
* Left shift: row * w + (col + w - 1) % w
* Right shift: row * w + (col + 1) % w

Where `row = idx / w` and `col = idx % w`, and `idx` is the linear index of the
cell in the grid.

To avoid multiple divisions and module operations, we can compute the linear
index shifts directly using the following formulas.
* Left shift: idx - 1 + (if idx % w == 0 then w else 0)
* Right shift: idx + 1 - (if (idx + 1) % w == 0 then w else 0)

This file contains the proof that both representations of the left and right
shifts are equivalent.
-/


/- --- Useful lemmas --- -/

theorem div_mul (a b : Nat) : a / b * b = a - a % b := by
  have hle : a % b ≤ a := Nat.mod_le a b
  rw [Nat.mul_comm, ← Nat.add_left_cancel_iff (n := a % b),
      Nat.add_sub_cancel' hle, Nat.mod_add_div]

/--
2D coordinate for a cell in the grid.
-/
structure Coord where
  row : Nat
  col : Nat

/--
Converts a linear index `idx` into a 2D coordinate `Coord` for a grid of width `w`.
-/
def Coord.ofIndex (w idx : Nat) : Coord := { row := idx / w, col := idx % w }


/- --- Move left --- -/

/--
Original specification for moving left in a 2D grid with periodic boundary conditions.
-/
def moveLeftSpec (w idx : Nat) : Nat :=
  let ⟨row, col⟩ := Coord.ofIndex w idx
  row * w + (col + w - 1) % w

/--
Implementation for moving left in a 2D grid with periodic boundary conditions using
linear indexing.
-/
def moveLeftImpl (w idx : Nat) : Nat :=
  idx + (if idx % w == 0 then w else 0) - 1

/--
Proof that specification and implementation for moving left are equivalent.
-/
theorem moveLeftCorrect (w idx : Nat) (hw : 0 < w) :
  moveLeftImpl w idx = moveLeftSpec w idx := by
  unfold moveLeftImpl moveLeftSpec Coord.ofIndex
  simp
  -- Because of the if-else structure, we need to consider two cases:
  -- when idx % w = 0 and when idx % w ≠ 0.
  by_cases h : idx % w = 0
  . -- idx % w = 0
    -- From the definition of `col` in `moveLeftSpec`, we have `col = idx % w`.
    -- Since `idx % w = 0` and `w - 1 < w`, we have:
    have hcol : (idx % w + w - 1) % w = w - 1 := by rw [h]; simp?
    rw [ite_eq_left h, hcol, div_mul idx w, h]
    omega
  . -- idx % w ≠ 0
    -- From the definition of the modulus operation:
    have hle : idx % w ≤ idx := Nat.mod_le idx w
    have hlt : idx % w < w := Nat.mod_lt idx hw
    -- From the definition of `col` in `moveLeftSpec`, we have `col = idx % w`.
    -- For `idx % w ≠ 0`, we have `col = idx % w` and `col - 1 = idx % w - 1`.
    have hcol : (idx % w + w - 1) % w = idx % w - 1 := by
      rw [Nat.add_comm, Nat.add_sub_assoc (by omega), Nat.add_mod]
      simp
      rw [Nat.mod_eq_of_lt (by omega)] -- requires hlt
    rw [ite_eq_right h, hcol, div_mul idx w]
    omega -- requires hle


/- --- Move right --- -/

/--
Original specification for moving right in a 2D grid with periodic boundary conditions.
-/
def moveRightSpec (w idx : Nat) : Nat :=
  let ⟨row, col⟩ := Coord.ofIndex w idx
  row * w + (col + 1) % w

/--
Implementation for moving right in a 2D grid with periodic boundary conditions using
linear indexing.
-/
def moveRightImpl (w idx : Nat) : Nat :=
  idx + 1 - (if (idx + 1) % w == 0 then w else 0)

/--
Proof that specification and implementation for moving right are equivalent.
-/
theorem moveRightCorrect (w idx : Nat) (hw : 0 < w) :
  moveRightImpl w idx = moveRightSpec w idx := by
  unfold moveRightImpl moveRightSpec Coord.ofIndex
  simp
  -- Because of the if-else structure, we need to consider two cases:
  -- when idx % w = 0 and when idx % w ≠ 0.
  --
  -- Although we are analyzing (idx + 1) % w, it is more convenient to express
  -- it as `idx % w + 1`. That is because `idx % w + 1` is a bit easier for omega
  -- to reason about.
  by_cases h : idx % w + 1 = w
  . -- idx % w + 1 = w
    -- Recovering the original condition for the if-else statement.
    have hcond : (idx + 1) % w = 0 := by
      rw [Nat.add_mod, show (idx % w + 1 % w) % w = 0 from by simp [h]]
    rw [ite_eq_left hcond, div_mul idx w]
    omega
  . -- idx % w + 1 ≠ w
    have hle : idx % w ≤ idx := Nat.mod_le idx w
    have hmod_lt : idx % w < w := Nat.mod_lt idx hw
    have hmod_add_lt : idx % w + 1 < w := by omega  -- requires hmod_lt and h
    have hadd : (idx + 1) % w = (idx % w + 1) % w := by rw [Nat.mod_add_mod]
    -- Recovering the condition for the if-else statement in this case.
    have hcond : (idx + 1) % w ≠ 0 := by rw [hadd, Nat.mod_eq_of_lt hmod_add_lt]; omega
    -- Lemma for reducing the modulus when the value is less than w.
    have hredux : (idx % w + 1) % w = idx % w + 1 := by rw [Nat.mod_eq_of_lt hmod_add_lt]
    rw [ite_eq_right hcond, div_mul idx w, hadd, hredux]
    omega -- requires hle
