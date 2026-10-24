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
  simp only [beq_iff_eq]
  have hr : idx % w < w := Nat.mod_lt idx hw
  have hle : idx % w ≤ idx := Nat.mod_le idx w
  have hidx : idx / w * w = idx - idx % w := by
    rw [Nat.mul_comm, ← Nat.add_left_cancel_iff (n := (idx % w)),
        Nat.mod_add_div, Nat.add_comm, Nat.sub_add_cancel hle]
  by_cases h : idx % w = 0
  · have hspec : (idx % w + w - 1) % w = w - 1 := by
      rw [h, show (0 + w - 1) = w - 1 from by omega, Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_left h, hspec, hidx]
    omega
  · have hpos : 0 < idx % w := Nat.pos_of_ne_zero h
    have hspec : (idx % w + w - 1) % w = idx % w - 1 := by
      rw [show idx % w + w - 1 = (idx % w - 1) + w from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_right h, hspec, hidx]
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
  simp only [beq_iff_eq]
  have hw0 : 0 < w := Nat.lt_of_succ_lt hw
  have hr : idx % w < w := Nat.mod_lt idx hw0
  have hle : idx % w ≤ idx := Nat.mod_le idx w
  have hidx: idx / w * w = idx - idx % w := by
    rw [Nat.mul_comm, ← Nat.add_left_cancel_iff (n := (idx % w))]
    rw [Nat.mod_add_div, Nat.add_comm, Nat.sub_add_cancel hle]
  have hadd : (idx + 1) % w = (idx % w + 1) % w := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hw]
  by_cases hc : idx % w + 1 = w
  . have hcond : (idx + 1) % w = 0 := by rw [hadd, hc, Nat.mod_self]
    have hspec : (idx % w + 1) % w = 0 := by rw [hc, Nat.mod_self]
    rw [ite_eq_left hcond, hspec, hidx]
    omega
  . -- idx % w + 1 ≠ w
    have hlt : idx % w + 1 < w := by omega
    have hcond : (idx + 1) % w ≠ 0 := by
      rw [hadd, Nat.mod_eq_of_lt hlt]
      omega
    have hspec : (idx % w + 1) % w = idx % w + 1 := by rw [Nat.mod_eq_of_lt hlt]
    rw [ite_eq_right hcond, hspec, hidx]
    omega
