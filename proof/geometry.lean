def moveLeftSpec (w : Nat) (idx : Nat) : Nat :=
  let row := idx / w
  let col := idx % w
  row * w + (col + w - 1) % w

def moveLeftImpl (w : Nat) (idx : Nat) : Nat :=
  idx + (if idx % w == 0 then w else 0) - 1

theorem moveLeftCorrect (w : Nat) (hw : 0 < w) (idx : Nat) :
  moveLeftImpl w idx = moveLeftSpec w idx := by
  unfold moveLeftImpl moveLeftSpec
  simp
  by_cases h : idx % w = 0
  . rw [h]
    simp
    have h1 : w ∣ idx := Nat.dvd_of_mod_eq_zero h
    have h2 : idx / w * w = idx := Nat.div_mul_cancel h1
    have h3 : 1 ≤ w := Nat.le_of_pred_lt hw
    rw [h2, Nat.add_sub_assoc h3]
  . -- idx % w ≠ 0
    rw [ite_eq_right h, Nat.add_zero]
    have h1 : idx / w * w = idx - idx % w := by
      rw [Nat.mul_comm, ← Nat.add_left_cancel_iff (n := (idx % w))]
      rw [Nat.mod_add_div, ← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
      by_cases hidx : idx < w
      . rw [Nat.mod_eq_of_lt hidx]
        simp
      . -- idx < w → False
        have h2 : w ≤ idx := Nat.le_of_not_lt hidx
        have h3 : idx % w < w := Nat.mod_lt idx hw
        have h4 : idx % w < idx := Nat.lt_of_lt_of_le h3 h2
        exact Nat.le_of_lt h4
    rw [h1]
    have h2 : 0 < idx % w := Nat.pos_of_ne_zero h
    by_cases hidx : idx < w
    . rw [Nat.mod_eq_of_lt hidx]
      simp
      have h3 : 0 < idx := by
        rw [Nat.mod_eq_of_lt hidx] at h2
        exact h2
      have h4 : 1 ≤ idx := Nat.le_of_pred_lt h3
      rw [Nat.add_comm, Nat.add_sub_assoc h4, Nat.add_mod]
      simp
      have h5 : idx - 1 < idx := Nat.sub_lt h3 (by trivial)
      rw [Nat.mod_eq_of_lt (Nat.lt_trans h5 hidx)]
    . -- idx ≥ w
      have h3 : w ≤ idx := Nat.le_of_not_lt hidx
      have h4 : 1 ≤ idx % w := Nat.le_of_pred_lt h2
      rw [Nat.add_comm (idx % w), Nat.add_sub_assoc h4, Nat.add_mod]
      simp
      have h5 : idx % w < w := Nat.mod_lt idx hw
      have h6 : idx % w - 1 < idx % w := Nat.sub_lt h2 (by trivial)
      rw [Nat.mod_eq_of_lt (Nat.lt_trans h6 h5)]
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
