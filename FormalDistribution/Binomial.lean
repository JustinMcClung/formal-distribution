/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Algebra.Ring.Basic

/-!
# Extended Binomial Coefficients

This file defines the extended binomial coefficient for integer upper index and
natural number lower index, along with an integer-valued variant used for
computations in formal distribution theory.

## Main definitions

* `Int.extChoose` - extended binomial coefficient `C(j, n)` for `j : ℤ`, `n : ℕ`, valued in `ℚ`
* `intBinomial` - integer-valued binomial coefficient for `k : ℤ`, `n : ℕ`

## Main results

* `Int.extChoose_eq_intBinomial` - the two definitions agree after casting
* `Int.extChoose_nonneg` - agrees with `Nat.choose` for non-negative arguments

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.2.2
-/

/-! ## Extended binomial coefficient -/

/-- Extended binomial coefficient for integer upper index.

Computes `j(j-1)⋯(j-n+1)/n!` via the recurrence `C(j,0) = 1`,
`C(j,n+1) = C(j,n) · (j-n) / (n+1)`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.2.2
-/
def Int.extChoose (j : ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => Int.extChoose j n * ((↑j : ℚ) - ↑n) / (↑(n + 1) : ℚ)

notation "(" j " choose " n ")" => Int.extChoose j n

/-- Extended binomial coefficient is 1 when `n = 0`. -/
@[simp]
theorem Int.extChoose_zero (j : ℤ) : Int.extChoose j 0 = 1 := rfl

/-- Recurrence for the extended binomial coefficient. -/
theorem Int.extChoose_succ (j : ℤ) (n : ℕ) :
    Int.extChoose j (n + 1) = Int.extChoose j n * ((↑j : ℚ) - ↑n) / (↑(n + 1) : ℚ) := rfl

/-! ## Integer-valued binomial coefficient -/

/-- Integer-valued generalized binomial coefficient.

For `k ≥ 0`: uses `Nat.choose`. For `k < 0`: uses the identity
`C(k,n) = (-1)^n · C(n-k-1, n)`. -/
def intBinomial (k : ℤ) (n : ℕ) : ℤ :=
  match k with
  | .ofNat m => ↑(Nat.choose m n)
  | .negSucc m => (-1) ^ n * ↑(Nat.choose (n + m) n)

/-- `intBinomial k 0 = 1` for all `k`. -/
theorem intBinomial_zero (k : ℤ) : intBinomial k 0 = 1 := by
  cases k <;> simp [intBinomial]

/-- For `k = -1`: `intBinomial (-1) n = (-1)^n`. -/
theorem intBinomial_neg_one (n : ℕ) : intBinomial (-1) n = (-1) ^ n := by
  show (-1 : ℤ) ^ n * ↑(Nat.choose (n + 0) n) = (-1) ^ n
  simp

/-- Key identity: `(k - n) * C(k, n) = k * C(k-1, n)`. -/
theorem intBinomial_mul_sub (k : ℤ) (n : ℕ) :
    (k - ↑n) * intBinomial k n = k * intBinomial (k - 1) n := by
  cases k with
  | ofNat m =>
    cases m with
    | zero =>
      simp only [intBinomial, Int.ofNat_eq_natCast, Nat.cast_zero, zero_mul, zero_sub]
      rcases n with - | n <;> simp [Nat.choose_zero_succ]
    | succ m =>
      have h_eq : (Int.ofNat (m + 1) - 1 : ℤ) = Int.ofNat m := by
        simp only [Int.ofNat_eq_natCast]; push_cast; omega
      have h_l : intBinomial (Int.ofNat (m + 1)) n = ↑(Nat.choose (m + 1) n) := rfl
      have h_r : intBinomial (Int.ofNat (m + 1) - 1) n = ↑(Nat.choose m n) := by
        rw [h_eq]; rfl
      rw [h_l, h_r]; simp only [Int.ofNat_eq_natCast]
      cases n with
      | zero => simp
      | succ n =>
        have h_abs := Nat.add_one_mul_choose_eq m n
        have h_pascal := Nat.choose_succ_succ m n
        have h_abs_z : (↑(m + 1) : ℤ) * ↑(Nat.choose m n) =
            ↑(Nat.choose (m + 1) (n + 1)) * (↑(n + 1) : ℤ) := by exact_mod_cast h_abs
        have h_pascal_z : (↑(Nat.choose (m + 1) (n + 1)) : ℤ) =
            ↑(Nat.choose m n) + ↑(Nat.choose m (n + 1)) := by exact_mod_cast h_pascal
        nlinarith
  | negSucc m =>
    change (Int.negSucc m - ↑n) * ((-1) ^ n * ↑(Nat.choose (n + m) n)) =
           Int.negSucc m * ((-1) ^ n * ↑(Nat.choose (n + m + 1) n))
    have h_key : (n + m + 1) * Nat.choose (n + m) n = (m + 1) * Nat.choose (n + m + 1) n := by
      have h1 := Nat.add_one_mul_choose_eq (n + m) m
      have h2 : Nat.choose (n + m) n = Nat.choose (n + m) m := Nat.choose_symm_add
      have h3 : Nat.choose (n + m + 1) n = Nat.choose (n + m + 1) (m + 1) := by
        rw [show n + m + 1 = n + (m + 1) from by omega]; exact Nat.choose_symm_add
      rw [h2, h3]; exact h1.trans (mul_comm _ _)
    suffices h : (Int.negSucc m - (↑n : ℤ)) * ↑(Nat.choose (n + m) n) =
                 Int.negSucc m * ↑(Nat.choose (n + m + 1) n) by
      calc (Int.negSucc m - ↑n) * ((-1) ^ n * ↑(Nat.choose (n + m) n))
          = (-1) ^ n * ((Int.negSucc m - ↑n) * ↑(Nat.choose (n + m) n)) := by ring
        _ = (-1) ^ n * (Int.negSucc m * ↑(Nat.choose (n + m + 1) n)) := by rw [h]
        _ = Int.negSucc m * ((-1) ^ n * ↑(Nat.choose (n + m + 1) n)) := by ring
    have h_key_z : (↑(n + m + 1) : ℤ) * ↑(Nat.choose (n + m) n) =
        ↑(m + 1) * ↑(Nat.choose (n + m + 1) n) := by exact_mod_cast h_key
    have h_neg : (Int.negSucc m : ℤ) = -(↑m + 1) := by omega
    rw [h_neg]; push_cast at h_key_z ⊢; nlinarith

/-- Identity: `(n+1) * C(k, n+1) = k * C(k-1, n)`. -/
theorem intBinomial_succ_mul_eq (k : ℤ) (n : ℕ) :
    (↑(n + 1) : ℤ) * intBinomial k (n + 1) = k * intBinomial (k - 1) n := by
  cases k with
  | ofNat m =>
    cases m with
    | zero =>
      simp only [intBinomial, Int.ofNat_eq_natCast, Nat.cast_zero, zero_mul,
                  Nat.choose_zero_succ, mul_zero]
    | succ m =>
      have h_eq : (Int.ofNat (m + 1) - 1 : ℤ) = Int.ofNat m := by
        simp only [Int.ofNat_eq_natCast]; push_cast; omega
      have h_l : intBinomial (Int.ofNat (m + 1)) (n + 1) = ↑(Nat.choose (m + 1) (n + 1)) := rfl
      have h_r : intBinomial (Int.ofNat (m + 1) - 1) n = ↑(Nat.choose m n) := by rw [h_eq]; rfl
      rw [h_l, h_r]; simp only [Int.ofNat_eq_natCast]
      have h := (Nat.add_one_mul_choose_eq m n).symm
      rw [mul_comm] at h; exact_mod_cast h
  | negSucc m =>
    change (↑(n + 1) : ℤ) * ((-1) ^ (n + 1) * ↑(Nat.choose (n + 1 + m) (n + 1))) =
           Int.negSucc m * ((-1) ^ n * ↑(Nat.choose (n + m + 1) n))
    rw [show n + 1 + m = n + m + 1 from by omega]
    have h_key : (n + 1) * Nat.choose (n + m + 1) (n + 1) = (m + 1) * Nat.choose (n + m + 1) n := by
      have h1 := Nat.add_one_mul_choose_eq (n + m) n
      have h2 := Nat.add_one_mul_choose_eq (n + m) m
      have h_sym : Nat.choose (n + m) n = Nat.choose (n + m) m := Nat.choose_symm_add
      have h_sym2 : Nat.choose (n + m + 1) (m + 1) = Nat.choose (n + m + 1) n := by
        rw [show n + m + 1 = n + (m + 1) from by omega]; exact (Nat.choose_symm_add).symm
      rw [h_sym] at h1; rw [h_sym2] at h2; linarith
    have h_z : (↑(n + 1) : ℤ) * ↑(Nat.choose (n + m + 1) (n + 1)) =
               (↑(m + 1) : ℤ) * ↑(Nat.choose (n + m + 1) n) := by exact_mod_cast h_key
    have h_neg : (Int.negSucc m : ℤ) = -(↑m + 1) := by omega
    rw [h_neg, pow_succ]
    calc (↑(n + 1) : ℤ) * ((-1) ^ n * (-1) * ↑(Nat.choose (n + m + 1) (n + 1)))
        = -((-1 : ℤ) ^ n) * (↑(n + 1) * ↑(Nat.choose (n + m + 1) (n + 1))) := by ring
      _ = -((-1 : ℤ) ^ n) * (↑(m + 1) * ↑(Nat.choose (n + m + 1) n)) := by rw [h_z]
      _ = -(↑m + 1) * ((-1) ^ n * ↑(Nat.choose (n + m + 1) n)) := by push_cast; ring

/-- `Int.extChoose` agrees with `intBinomial` when cast to `ℚ`. -/
theorem Int.extChoose_eq_intBinomial (j : ℤ) (n : ℕ) :
    Int.extChoose j n = (↑(intBinomial j n) : ℚ) := by
  induction n with
  | zero => simp [intBinomial_zero]
  | succ n ih =>
    rw [Int.extChoose_succ, ih]
    have h_eq : (↑(n + 1) : ℤ) * intBinomial j (n + 1) = (j - ↑n) * intBinomial j n := by
      linarith [intBinomial_succ_mul_eq j n, intBinomial_mul_sub j n]
    have h_ne : (↑(n + 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    rw [eq_comm, eq_div_iff h_ne]
    have h_q : (↑(n + 1) : ℚ) * ↑(intBinomial j (n + 1)) =
               ((↑j : ℚ) - ↑n) * ↑(intBinomial j n) := by exact_mod_cast h_eq
    linarith [mul_comm (↑(intBinomial j (n + 1)) : ℚ) (↑(n + 1) : ℚ),
              mul_comm (↑(intBinomial j n) : ℚ) ((↑j : ℚ) - ↑n)]

/-- Extended binomial agrees with `Nat.choose` for non-negative arguments. -/
theorem Int.extChoose_nonneg (k n : ℕ) : Int.extChoose (↑k : ℤ) n = (↑(Nat.choose k n) : ℚ) := by
  rw [Int.extChoose_eq_intBinomial]; simp [intBinomial]

/-- `intBinomial 0 (n+1) = 0`. -/
@[simp]
theorem intBinomial_zero_left (n : ℕ) : intBinomial 0 (n + 1) = 0 := by
  simp [intBinomial]

/-- Pascal's rule for generalized binomial coefficients:
`C(k+1, n+1) = C(k, n) + C(k, n+1)`. -/
theorem intBinomial_pascal (k : ℤ) (n : ℕ) :
    intBinomial (k + 1) (n + 1) = intBinomial k n + intBinomial k (n + 1) := by
  have h_ne : (↑(n + 1) : ℤ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  apply mul_left_cancel₀ h_ne
  rw [mul_add]
  have lhs := intBinomial_succ_mul_eq (k + 1) n
  rw [show k + 1 - 1 = k from by omega] at lhs
  have rhs2 := intBinomial_succ_mul_eq k n
  rw [lhs, rhs2, ← intBinomial_mul_sub k n]
  push_cast; ring
