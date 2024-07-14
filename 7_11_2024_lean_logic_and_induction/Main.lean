import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.GeomSum


/- Supply proofs for 2 out of the 3 assignments.
   Do all 3 for 5 points of extra credit.

   All assignments can be proven through induction and appropriate use of library functions and logic operations.
-/

-- Assignment 1: Show that 2^n % 7 = 1, 2, or 4 for all n.
-- The main theorem
theorem assignment1 : ∀ n : ℕ, 2^n % 7 = 1 ∨ 2^n % 7 = 2 ∨ 2^n % 7 = 4 := by
  intro n
  induction n with
  | zero =>
    left
    exact Nat.mod_eq_of_lt (by norm_num : 1 < 7)
  | succ k ih =>
    cases ih with
    | inl h1 =>
      right; left
      calc (2^(k+1) % 7) = ((2^k) * 2 % 7) := by rw [Nat.pow_succ]
      _ = ((2^k % 7) * (2 % 7) % 7) := by rw [Nat.mul_mod]
      _ = (1 * 2 % 7) := by rw [h1]
      _ = (2 % 7) := by rw [Nat.one_mul]
    | inr h2 =>
      cases h2 with
      | inl h2_1 =>
        right; right
        calc (2^(k+1) % 7) = ((2^k) * 2 % 7) := by rw [Nat.pow_succ]
        _ = ((2^k % 7) * (2 % 7) % 7) := by rw [Nat.mul_mod]
        _ = (2 * 2 % 7) := by rw [h2_1]
        _ = (4 % 7) := by norm_num
      | inr h2_2 =>
        left
        calc (2^(k+1) % 7) = ((2^k) * 2 % 7) := by rw [Nat.pow_succ]
        _ = ((2^k % 7) * (2 % 7) % 7) := by rw [Nat.mul_mod]
        _ = (4 * 2 % 7) := by rw [h2_2]
        _ = (8 % 7) := by norm_num
        _ = 1 := by norm_num
--End of Proof

open Finset
open BigOperators

-- Assignment 2: Show that (1-x)*(1+x+x^2+...+x^{n-1}) = (1-x^n)
theorem assignment2 (x : ℝ) : ∀ n : ℕ, (1 - x) * (∑ i in range n, x ^ i) = 1 - x ^ n := by
  intro n
  induction n with
  | zero =>
    simp only [Finset.sum_range_zero, zero_sub, mul_zero, pow_zero, sub_self]
  | succ k hk =>
    have h_sum : ∑ i in range (k + 1), x ^ i = (∑ i in range k, x ^ i) + x ^ k := by
     rw [sum_range_succ, add_comm]
    rw [h_sum]
    rw [mul_add]
    rw [hk]
    simp only [mul_add, sub_add_eq_sub_sub, add_sub_assoc, pow_succ, mul_sub, sub_sub, add_sub_cancel]
    ring
--End of Proof

-- Assignment 3: Show that if a₀ = 0, aₙ₊₁ = 2*aₙ + 1 then aₙ = 2^n - 1.
theorem assignment3
  (a : ℕ → ℝ) (h_zero : a 0 = 0) (h_rec : ∀ n : ℕ, a (n + 1) = 2 * (a n) + 1) :
  ∀ n : ℕ, a n = 2^n - 1 := by
  intro n
  induction n with
  | zero =>
    rw [h_zero]
    simp
  | succ k hk =>
    rw [h_rec k]
    rw [hk]
    rw [pow_succ]
    ring
--End of proof
