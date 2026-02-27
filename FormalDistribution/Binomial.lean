/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Binomial

/-!
# Binomial Coefficients for Formal Distribution Theory

This file provides `intBinomial`, a generalized binomial coefficient for integer upper
index, defined as `Ring.choose` from Mathlib's `BinomialRing` API. Thin wrappers provide
the absorption identity and other properties needed for formal distribution theory.

## Main definitions

* `intBinomial` - integer-valued binomial coefficient `C(k, n)` for `k : ℤ`, `n : ℕ`,
  defined as `Ring.choose k n`

## Main results

* `intBinomial_neg_one` - `C(-1, n) = (-1)^n`
* `intBinomial_mul_sub` - absorption identity: `(k - n) * C(k, n) = k * C(k-1, n)`
* `intBinomial_succ_mul_eq` - `(n+1) * C(k, n+1) = k * C(k-1, n)`
* `intBinomial_pascal` - Pascal's rule: `C(k+1, n+1) = C(k, n) + C(k, n+1)`

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.2.2
* [Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*]
-/

/-- Generalized binomial coefficient for integer upper index, defined as
`Ring.choose` from Mathlib's `BinomialRing` API. -/
abbrev intBinomial (k : ℤ) (n : ℕ) : ℤ := Ring.choose k n

/-- `intBinomial k 0 = 1` for all `k`. -/
theorem intBinomial_zero (k : ℤ) : intBinomial k 0 = 1 :=
  Ring.choose_zero_right k

/-- For natural number arguments, `intBinomial` agrees with `Nat.choose`. -/
theorem intBinomial_natCast (k n : ℕ) : intBinomial (↑k) n = ↑(Nat.choose k n) :=
  Ring.choose_natCast k n

/-- For `k = -1`: `intBinomial (-1) n = (-1)^n`. -/
theorem intBinomial_neg_one (n : ℕ) : intBinomial (-1) n = (-1) ^ n := by
  show Ring.multichoose ((-1 : ℤ) - ↑n + 1) n = (-1) ^ n
  rw [show (-1 : ℤ) - ↑n + 1 = -↑n from by omega]
  exact Ring.multichoose_neg_self n

/-- Identity: `(n+1) * C(k, n+1) = k * C(k-1, n)`.

This is the upper index absorption identity, derived from
`Ring.choose_smul_choose` with `k = 1`. -/
theorem intBinomial_succ_mul_eq (k : ℤ) (n : ℕ) :
    (↑(n + 1) : ℤ) * intBinomial k (n + 1) = k * intBinomial (k - 1) n := by
  have h := Ring.choose_smul_choose k (show 1 ≤ n + 1 from Nat.succ_le_succ (Nat.zero_le n))
  simp only [Nat.choose_one_right, Ring.choose_one_right, Nat.add_sub_cancel, nsmul_eq_mul] at h
  exact_mod_cast h

/-- Pascal's rule: `C(k+1, n+1) = C(k, n) + C(k, n+1)`. -/
theorem intBinomial_pascal (k : ℤ) (n : ℕ) :
    intBinomial (k + 1) (n + 1) = intBinomial k n + intBinomial k (n + 1) :=
  Ring.choose_succ_succ k n

/-- Key identity: `(k - n) * C(k, n) = k * C(k-1, n)`.

Derived from `intBinomial_succ_mul_eq` and `intBinomial_pascal`. -/
theorem intBinomial_mul_sub (k : ℤ) (n : ℕ) :
    (k - ↑n) * intBinomial k n = k * intBinomial (k - 1) n := by
  rw [← intBinomial_succ_mul_eq k n]
  have h2 : (↑(n + 1) : ℤ) * intBinomial (k + 1) (n + 1) = (k + 1) * intBinomial k n := by
    have := intBinomial_succ_mul_eq (k + 1) n; rwa [show k + 1 - 1 = k from by ring] at this
  have h3 : intBinomial k (n + 1) = intBinomial (k + 1) (n + 1) - intBinomial k n := by
    linarith [intBinomial_pascal k n]
  rw [h3, mul_sub, h2]; push_cast; ring

/-- `intBinomial 0 (n+1) = 0`. -/
@[simp]
theorem intBinomial_zero_left (n : ℕ) : intBinomial 0 (n + 1) = 0 :=
  Ring.choose_zero_succ ℤ n
