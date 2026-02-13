/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FormalDistribution.Basic

/-!
# Formal Differentiation of Distributions

This file defines formal differentiation for formal distributions and proves
its basic properties: linearity, commutativity, and interaction with iteration.

## Main definitions

* `FormalDistribution.deriv` - formal derivative with respect to a variable
* `FormalDistribution.iteratedDeriv` - iterated formal derivative

## Main results

* `FormalDistribution.deriv_add` - derivative distributes over addition
* `FormalDistribution.deriv_smul` - derivative commutes with scalar multiplication
* `FormalDistribution.deriv_deriv_comm` - partial derivatives commute

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Section 1.1
-/

variable {A : Type*} [Ring A]

namespace FormalDistribution

variable {n : ℕ}

/-- Formal derivative of a distribution with respect to variable `i`.

For `a(z) = ∑ aₙ zⁿ`, the derivative is `∂_z a = ∑ (n+1)·a_{n+1} z^n`,
so `(∂_z a)_m = (m+1)·a_{m+1}`. -/
def deriv (a : FormalDistribution A n) (i : Fin n) : FormalDistribution A n where
  coeff := fun idx =>
    let shifted_idx := Function.update idx i (idx i + 1)
    (idx i + 1 : ℤ) • (a.coeff shifted_idx)
  support_finite := by
    have ha := a.support_finite
    have h_subset : {idx : Fin n → ℤ |
                    (idx i + 1 : ℤ) • (a.coeff (Function.update idx i (idx i + 1))) ≠ 0} ⊆
                    (fun idx' : Fin n → ℤ => fun j => if j = i then idx' i - 1 else idx' j) ''
                    {idx' : Fin n → ℤ | a.coeff idx' ≠ 0} := by
      intro idx hne
      let shifted_idx := Function.update idx i (idx i + 1)
      use shifted_idx
      constructor
      · by_contra h
        simp only [Set.mem_setOf_eq] at h
        push_neg at h
        simp only [shifted_idx] at h
        simp [h] at hne
      · ext j
        by_cases hj : j = i
        · rw [hj]
          simp only [ite_true]
          unfold shifted_idx Function.update
          simp
        · simp only [hj, ite_false]
          unfold shifted_idx
          rw [Function.update_of_ne hj]
    apply Set.Finite.subset _ h_subset
    exact Set.Finite.image _ ha

/-- Iterated formal derivative. -/
def iteratedDeriv (a : FormalDistribution A n) (i : Fin n) : ℕ → FormalDistribution A n
  | 0 => a
  | k + 1 => deriv (iteratedDeriv a i k) i

notation:max a "^[∂" i "," k "]" => iteratedDeriv a i k

/-! ### Properties of formal differentiation -/

/-- Derivative of zero is zero. -/
@[simp]
theorem deriv_zero (i : Fin n) : deriv (0 : FormalDistribution A n) i = 0 := by
  ext idx
  apply smul_zero

/-- Derivative distributes over addition. -/
@[simp]
theorem deriv_add (a b : FormalDistribution A n) (i : Fin n) :
    deriv (a + b) i = deriv a i + deriv b i := by
  ext idx
  show (idx i + 1 : ℤ) • ((a + b).coeff (Function.update idx i (idx i + 1))) =
       (idx i + 1 : ℤ) • (a.coeff (Function.update idx i (idx i + 1))) +
       (idx i + 1 : ℤ) • (b.coeff (Function.update idx i (idx i + 1)))
  have : (a + b).coeff (Function.update idx i (idx i + 1)) =
         a.coeff (Function.update idx i (idx i + 1)) + b.coeff (Function.update idx i (idx i + 1)) := rfl
  rw [this, smul_add]

/-- Derivative commutes with scalar multiplication. -/
@[simp]
theorem deriv_smul (c : A) (a : FormalDistribution A n) (i : Fin n) :
    deriv (c • a) i = c • deriv a i := by
  ext idx
  show (idx i + 1 : ℤ) • (c * a.coeff (Function.update idx i (idx i + 1))) =
       c * ((idx i + 1 : ℤ) • a.coeff (Function.update idx i (idx i + 1)))
  rw [zsmul_eq_mul, zsmul_eq_mul]
  rw [← mul_assoc, (Int.cast_commute (idx i + 1) c).eq, mul_assoc]

/-! ### Iterated derivative properties -/

/-- Iterated derivative of zero is zero. -/
@[simp]
theorem iteratedDeriv_zero (i : Fin n) (k : ℕ) :
    iteratedDeriv (0 : FormalDistribution A n) i k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iteratedDeriv, ih]

/-- Iterated derivative distributes over addition. -/
@[simp]
theorem iteratedDeriv_add (a b : FormalDistribution A n) (i : Fin n) (k : ℕ) :
    iteratedDeriv (a + b) i k = iteratedDeriv a i k + iteratedDeriv b i k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iteratedDeriv, ih]

/-- Iterated derivative commutes with scalar multiplication. -/
@[simp]
theorem iteratedDeriv_smul (c : A) (a : FormalDistribution A n) (i : Fin n) (k : ℕ) :
    iteratedDeriv (c • a) i k = c • iteratedDeriv a i k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iteratedDeriv, ih]

/-- Partial derivatives in different variables commute. -/
theorem deriv_deriv_comm (a : FormalDistribution A n) (i j : Fin n) :
    (a.deriv i).deriv j = (a.deriv j).deriv i := by
  by_cases h : i = j
  · rw [h]
  · ext idx
    simp only [deriv]
    have eval_i_after_j : Function.update idx j (idx j + 1) i = idx i :=
      update_eval_diff idx j i (idx j + 1) (Ne.symm h)
    have eval_j_after_i : Function.update idx i (idx i + 1) j = idx j :=
      update_eval_diff idx i j (idx i + 1) h
    have double_update_eq :
      Function.update (Function.update idx i (idx i + 1)) j (idx j + 1) =
      Function.update (Function.update idx j (idx j + 1)) i (idx i + 1) := by
      funext k
      by_cases hki : k = i
      · rw [hki, update_eval_same, update_eval_diff _ _ _ _ (Ne.symm h), update_eval_same]
      · by_cases hkj : k = j
        · rw [hkj, update_eval_same, update_eval_diff _ _ _ _ h, update_eval_same]
        · have lhs : Function.update (Function.update idx i (idx i + 1)) j (idx j + 1) k = idx k := by
            rw [update_eval_diff _ j k _ (Ne.symm hkj), update_eval_diff _ i k _ (Ne.symm hki)]
          have rhs : Function.update (Function.update idx j (idx j + 1)) i (idx i + 1) k = idx k := by
            rw [update_eval_diff _ i k _ (Ne.symm hki), update_eval_diff _ j k _ (Ne.symm hkj)]
          rw [lhs, rhs]
    rw [eval_i_after_j, eval_j_after_i, double_update_eq]
    show (idx j + 1 : ℤ) • (idx i + 1 : ℤ) • _ = (idx i + 1 : ℤ) • (idx j + 1 : ℤ) • _
    rw [zsmul_comm]

/-- Iterated derivatives compose additively. -/
theorem iteratedDeriv_add_eq (a : FormalDistribution A n) (i : Fin n) (k m : ℕ) :
    iteratedDeriv (iteratedDeriv a i k) i m = iteratedDeriv a i (k + m) := by
  induction m with
  | zero => simp [iteratedDeriv]
  | succ m ih =>
    simp only [iteratedDeriv]
    rw [ih]
    rfl

/-- Double derivative equals iterated derivative of order 2. -/
theorem deriv_deriv_eq_iteratedDeriv (a : FormalDistribution A n) (i : Fin n) :
    (a.deriv i).deriv i = a.iteratedDeriv i 2 := by
  rfl

/-- Coefficient of derivative in terms of original coefficient. -/
theorem deriv_coeff_eq (a : FormalDistribution A n) (i : Fin n) (idx : Fin n → ℤ) :
    (a.deriv i).coeff idx = (idx i + 1 : ℤ) • a.coeff (Function.update idx i (idx i + 1)) := by
  rfl

end FormalDistribution
