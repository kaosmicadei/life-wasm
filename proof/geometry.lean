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
