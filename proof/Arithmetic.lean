/-
In the file `life.wat`, we used a fixed size of `w = 32` for the grid.

For the periodic boundary conditions, we use a `% 32` operation to wrap around
the column indices. Since 32 is a power of two, we can replace the `% 32`
operation with a bitwise AND operation, `& 31`, eliminating the need of expensive
division operations.

This file contains the proof of equivalence between the modulus operation and
the bitwise AND operation for when `w = 2 ^ k`.
-/

def periodicBoundarySpec (w idx : Nat) : Nat := idx % w

def periodicBoundaryImpl (w idx : Nat) : Nat := idx &&& (w - 1)

theorem periodicBoundaryCorrect (w idx : Nat) (hw : ∃ k, w = 2 ^ k) :
  periodicBoundarySpec w idx = periodicBoundaryImpl w idx := by
  unfold periodicBoundarySpec periodicBoundaryImpl
  obtain ⟨k, rfl⟩ := hw
  -- Two numbers are equal if all their bits are equal.
  apply Nat.eq_of_testBit_eq
  intro i
  -- x % 2^k is the same as selecting the bits i < k of x where x[i] = 1.
  rw [Nat.testBit_mod_two_pow]
  -- Take a bit i from x & y is the same as taking the bit i from x and
  -- the bit i from y and performing a logical AND.
  rw [Nat.testBit_and]
  -- (2^k - 1) have all the bits i < k set to 1
  rw [Nat.testBit_two_pow_sub_one]
  rw [Bool.and_comm]
