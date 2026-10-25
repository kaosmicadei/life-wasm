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

In this file, we prove that both representations of the left and right shifts
are equivalent.

NOTE: In the `life.wat` file, we used a fixed size of `w = 32`. Since 32 is a
power of two, we can replace the module operation by a bit wise AND, `& 31`.
-/

def moveLeftSpec (w : Nat) (idx : Nat) : Nat :=
  let row := idx / w
  let col := idx % w
  row * w + (col + w - 1) % w

def moveLeftImpl (w : Nat) (idx : Nat) : Nat :=
  idx + (if idx % w == 0 then w else 0) - 1

theorem moveLeftCorrect (w : Nat) (hw : 0 < w) (idx : Nat) :
  moveLeftImpl w idx = moveLeftSpec w idx := by
  unfold moveLeftImpl moveLeftSpec
  simp?
  -- Because of the if-else structure, we need to consider two cases:
  -- when idx % w = 0 and when idx % w ≠ 0.
  --
  -- Before that, let's define some helpful lemmas that will be used
  -- in both cases.
  --
  -- From the definition of modulus operation:
  have hle : idx % w ≤ idx := Nat.mod_le idx w
  -- From the definition of `row` in `moveLeftSpec` and the modulus operation, we
  -- have `row = idx / w`. We then have `row * w = idx - idx % w`.
  have hrow : idx / w * w = idx - idx % w := by
    rw [Nat.mul_comm, ← Nat.add_left_cancel_iff (n := idx % w),
        Nat.mod_add_div, Nat.add_comm, Nat.sub_add_cancel hle]
  -- Now we can proceed with the case analysis on idx % w.
  by_cases h : idx % w = 0
  . -- idx % w = 0
    -- From the definition of `col` in `moveLeftSpec`, we have `col = idx % w`.
    -- Since `idx % w = 0` and `w - 1 < w`, we have:
    have hcol : (idx % w + w - 1) % w = w - 1 := by rw [h]; simp?
    rw [ite_eq_left h, hcol, hrow, h]
    omega
  . -- idx % w ≠ 0
    -- From the definition of the modulus operation:
    have hiw : idx % w < w := Nat.mod_lt idx hw
    -- From the definition of `col` in `moveLeftSpec`, we have `col = idx % w`.
    -- For `idx % w ≠ 0`, we have `col = idx % w` and `col - 1 = idx % w - 1`.
    have hcol : (idx % w + w - 1) % w = idx % w - 1 := by
      rw [Nat.add_comm, Nat.add_sub_assoc (by omega), Nat.add_mod]
      simp
      rw [Nat.mod_eq_of_lt (by omega)] -- uses hiw
    rw [ite_eq_right h, hcol, hrow]
    omega

def moveRightSpec (w : Nat) (idx : Nat) : Nat :=
  let row := idx / w
  let col := idx % w
  row * w + (col + 1) % w

def moveRightImpl (w : Nat) (idx : Nat) : Nat :=
  idx + 1 - (if (idx + 1) % w == 0 then w else 0)

theorem moveRightCorrect (w : Nat) (hw : 1 < w) (idx : Nat) :
  moveRightImpl w idx = moveRightSpec w idx := by
  unfold moveRightImpl moveRightSpec
  simp?
  -- Because of the if-else structure, we need to consider two cases:
  -- when idx % w = 0 and when idx % w ≠ 0.
  --
  -- Before that, let's define some helpful lemmas that will be used
  -- in both cases.
  -- From the definition of modulus operation:
  have hle : idx % w ≤ idx := Nat.mod_le idx w
  -- From the definition of `row` in `moveLeftSpec` and the modulus operation, we
  -- have `row = idx / w`. We then have `row * w = idx - idx % w`.
  have hrow : idx / w * w = idx - idx % w := by
    rw [Nat.mul_comm, ← Nat.add_left_cancel_iff (n := idx % w),
        Nat.mod_add_div, Nat.add_comm, Nat.sub_add_cancel hle]
  -- Now we can proceed with the case analysis on (idx + 1) % w.
  --
  -- Although we are analyzing (idx + 1) % w, it is more convenient to express
  -- it as `idx % w + 1`. That is because `idx % w + 1` is a bit easier for omega
  -- to reason about.
  by_cases h : idx % w + 1 = w
  . -- idx % w + 1 = w
    -- Recovering the original condition for the if-else statement.
    have hcond : (idx + 1) % w = 0 := by
      rw [Nat.add_mod, show (idx % w + 1 % w) % w = 0 from by simp [h]]
    rw [ite_eq_left hcond, hrow]
    omega
  . -- idx % w + 1 ≠ w
    have h0w : 0 < w := Nat.lt_of_succ_lt hw
    have hiw : idx % w < w := Nat.mod_lt idx h0w
    have hlt : idx % w + 1 < w := by omega  -- uses hiw and h
    have hadd : (idx + 1) % w = (idx % w + 1) % w := by rw [Nat.add_mod]; simp?
    -- Recovering the condition for the if-else statement in this case.
    have hcond : (idx + 1) % w ≠ 0 := by rw [hadd, Nat.mod_eq_of_lt hlt]; omega
    -- Lemma for reducing the modulus when the value is less than w.
    have hredux : (idx % w + 1) % w = idx % w + 1 := by rw [Nat.mod_eq_of_lt hlt]
    rw [ite_eq_right hcond, hrow, hadd, hredux]
    omega
