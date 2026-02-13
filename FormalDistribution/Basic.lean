/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Formal Distributions: Basic Definitions

This file defines formal distributions and generalized formal distributions over a ring,
along with their basic algebraic structure.

## Main definitions

* `FormalPolynomial` - formal polynomials in several variables
* `FormalTaylorSeries` - formal Taylor series in several variables
* `FormalDistribution` - formal Laurent series with total finite support
* `GeneralizedFormalDistribution` - formal Laurent series with bounded-finite support
* `FormalDist1`, `FormalDist2` - type aliases for 1- and 2-variable distributions
* `GenFormalDist1`, `GenFormalDist2` - type aliases for generalized distributions

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Section 1.1
-/

open scoped BigOperators

variable {A : Type*} [Ring A]

/-! ## 1.1 Formal distributions -/

/-- Formal polynomials in several variables over a ring `A`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.1.1
-/
def FormalPolynomial (A : Type*) [Ring A] (vars : Type*) : Type _ :=
  vars → A

/-- Formal Taylor series in several variables over a ring `A`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.1.1
-/
def FormalTaylorSeries (A : Type*) [Ring A] (vars : Type*) : Type _ :=
  vars → PowerSeries A

/-- Formal distributions with total finite support.

A formal distribution in `nvars` variables over a ring `A` is a formal Laurent series
`∑_{i ∈ ℤⁿ} aᵢ z^i` where only finitely many coefficients `aᵢ` are nonzero.

This type requires total finite support, enabling clean algebraic operations
including a well-defined Cauchy product. For distributions with infinite but
bounded support (such as the formal delta), use `GeneralizedFormalDistribution`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.1.1
-/
@[ext]
structure FormalDistribution (A : Type*) [Ring A] (nvars : ℕ) where
  /-- The coefficient function mapping multi-indices to ring elements. -/
  coeff : (Fin nvars → ℤ) → A
  /-- Only finitely many coefficients are nonzero. -/
  support_finite : {idx : Fin nvars → ℤ | coeff idx ≠ 0}.Finite

/-- Generalized formal distributions with bounded-finite support.

This version only requires that for any lower bound, finitely many supported indices
lie above that bound. This accommodates distributions with infinite support such as
the formal delta `δ(z,w) = ∑_n z^n w^{-n-1}`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.1.1
-/
@[ext]
structure GeneralizedFormalDistribution (A : Type*) [Ring A] (nvars : ℕ) where
  /-- The coefficient function mapping multi-indices to ring elements. -/
  coeff : (Fin nvars → ℤ) → A
  /-- For any lower bound, only finitely many supported indices lie above it. -/
  support_finite : ∀ (bound : Fin nvars → ℤ),
    {idx : Fin nvars → ℤ | (∀ i, idx i ≥ bound i) ∧ coeff idx ≠ 0}.Finite

/-- One-variable formal distribution. -/
abbrev FormalDist1 (A : Type*) [Ring A] := FormalDistribution A 1

/-- Two-variable formal distribution. -/
abbrev FormalDist2 (A : Type*) [Ring A] := FormalDistribution A 2

/-- One-variable generalized formal distribution. -/
abbrev GenFormalDist1 (A : Type*) [Ring A] := GeneralizedFormalDistribution A 1

/-- Two-variable generalized formal distribution. -/
abbrev GenFormalDist2 (A : Type*) [Ring A] := GeneralizedFormalDistribution A 2

/-! ### Conversions between FormalDistribution and GeneralizedFormalDistribution -/

/-- Every `FormalDistribution` can be viewed as a `GeneralizedFormalDistribution`.

Total finite support implies bounded-finite support. -/
def FormalDistribution.toGeneralized {A : Type*} [Ring A] {nvars : ℕ}
    (a : FormalDistribution A nvars) : GeneralizedFormalDistribution A nvars where
  coeff := a.coeff
  support_finite := fun bound => by
    have ha := a.support_finite
    apply Set.Finite.subset ha
    intro idx ⟨_, hne⟩
    exact hne

/-! ### Basic operations on GeneralizedFormalDistribution -/

namespace GeneralizedFormalDistribution

variable {n : ℕ}

/-- The zero generalized formal distribution. -/
instance : Zero (GeneralizedFormalDistribution A n) where
  zero := ⟨fun _ => 0, by
    intro bound
    convert Set.finite_empty
    ext idx
    simp⟩

/-- Addition of generalized formal distributions. -/
instance : Add (GeneralizedFormalDistribution A n) where
  add a b := ⟨
    fun idx => a.coeff idx + b.coeff idx,
    by
      intro bound
      have ha := a.support_finite bound
      have hb := b.support_finite bound
      apply Set.Finite.subset (Set.Finite.union ha hb)
      intro idx ⟨hall, hne⟩
      by_cases ha' : a.coeff idx ≠ 0
      · left; exact ⟨hall, ha'⟩
      · right; simp at ha'; simp [ha'] at hne; exact ⟨hall, hne⟩
  ⟩

/-- Negation of generalized formal distributions. -/
instance : Neg (GeneralizedFormalDistribution A n) where
  neg a := ⟨fun idx => -a.coeff idx, by
    intro bound; apply Set.Finite.subset (a.support_finite bound)
    intro idx ⟨hall, hne⟩; exact ⟨hall, by simp at hne ⊢; exact hne⟩⟩

/-- Subtraction of generalized formal distributions. -/
instance : Sub (GeneralizedFormalDistribution A n) where
  sub a b := ⟨
    fun idx => a.coeff idx - b.coeff idx, by
      intro bound
      apply Set.Finite.subset (Set.Finite.union (a.support_finite bound) (b.support_finite bound))
      intro idx ⟨hall, hne⟩
      by_cases ha' : a.coeff idx ≠ 0
      · left; exact ⟨hall, ha'⟩
      · right; simp at ha'; simp [ha'] at hne; exact ⟨hall, hne⟩⟩

/-- Scalar multiplication of generalized formal distributions. -/
instance : SMul A (GeneralizedFormalDistribution A n) where
  smul c a := ⟨
    fun idx => c • a.coeff idx,
    by
      intro bound
      have ha := a.support_finite bound
      apply Set.Finite.subset ha
      intro idx ⟨hall, hne⟩
      by_cases hc : c = 0
      · simp [hc] at hne
      · exact ⟨hall, fun h => hne (by simp [h])⟩
  ⟩

/-- Formal derivative of a generalized distribution with respect to variable `i`. -/
def deriv (a : GeneralizedFormalDistribution A n) (i : Fin n) : GeneralizedFormalDistribution A n where
  coeff := fun idx =>
    let shifted_idx := Function.update idx i (idx i + 1)
    (idx i + 1 : ℤ) • (a.coeff shifted_idx)
  support_finite := fun bound => by
    let shifted_bound := Function.update bound i (bound i + 1)
    have ha := a.support_finite shifted_bound
    have h_subset : {idx : Fin n → ℤ | (∀ j, idx j ≥ bound j) ∧
                    (idx i + 1 : ℤ) • (a.coeff (Function.update idx i (idx i + 1))) ≠ 0} ⊆
                    (fun idx' : Fin n → ℤ => fun j => if j = i then idx' i - 1 else idx' j) ''
                    {idx' : Fin n → ℤ | (∀ j, idx' j ≥ shifted_bound j) ∧ a.coeff idx' ≠ 0} := by
      intro idx ⟨hall, hne⟩
      let shifted_idx := Function.update idx i (idx i + 1)
      use shifted_idx
      constructor
      · constructor
        · intro j
          by_cases hj : j = i
          · rw [hj]
            unfold shifted_idx Function.update shifted_bound
            simp
            have : idx i ≥ bound i := hall i
            omega
          · unfold shifted_idx shifted_bound
            rw [Function.update_of_ne hj, Function.update_of_ne hj]
            exact hall j
        · intro h
          rw [h] at hne
          simp at hne
      · ext j
        by_cases hj : j = i
        · rw [hj]
          simp
          unfold shifted_idx Function.update
          simp
        · simp [hj]
          unfold shifted_idx
          rw [Function.update_of_ne hj]
    apply Set.Finite.subset _ h_subset
    exact Set.Finite.image _ ha

/-! ### Multiplication for GeneralizedFormalDistribution (2D only) -/

/-- Convolution product of a finitely-supported distribution with a generalized one.

`(a * b)_{n,m} = ∑_{k,l} a_{k,l} * b_{n-k,m-l}`

Since `a` has finite support, the sum is well-defined. -/
noncomputable def mulFormalGen (a : FormalDistribution A 2)
    (b : GeneralizedFormalDistribution A 2) (n m : ℤ) : A :=
  Finset.sum a.support_finite.toFinset fun idx_a =>
    a.coeff idx_a * b.coeff (fun i => if i = 0 then n - idx_a 0 else m - idx_a 1)

/-- Multiplication: `FormalDistribution × GeneralizedFormalDistribution → GeneralizedFormalDistribution`. -/
noncomputable def FormalDistribution.mulGen
    (a : FormalDistribution A 2) (b : GeneralizedFormalDistribution A 2) :
    GeneralizedFormalDistribution A 2 := ⟨
  fun idx => mulFormalGen a b (idx 0) (idx 1),
  by
    intro bound
    suffices h_cover : (⋃ (idx_a : Fin 2 → ℤ) (_ : idx_a ∈ (a.support_finite.toFinset : Set _)),
        {idx : Fin 2 → ℤ | (∀ i, idx i ≥ bound i) ∧
         b.coeff (fun i => if i = 0 then idx 0 - idx_a 0 else idx 1 - idx_a 1) ≠ 0}).Finite by
      apply h_cover.subset
      intro idx ⟨hge, hne⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      have h_exists : ∃ idx_a ∈ a.support_finite.toFinset,
          a.coeff idx_a *
            b.coeff (fun i => if i = 0 then idx 0 - idx_a 0 else idx 1 - idx_a 1) ≠ 0 := by
        by_contra hall; push_neg at hall
        apply hne; unfold mulFormalGen; exact Finset.sum_eq_zero hall
      obtain ⟨idx_a, hmem, hterm⟩ := h_exists
      exact ⟨idx_a, Finset.mem_coe.mpr hmem, hge, fun h => hterm (by simp [h])⟩
    apply Set.Finite.biUnion a.support_finite.toFinset.finite_toSet
    intro idx_a _
    have hb := b.support_finite (fun i => bound i - idx_a i)
    apply Set.Finite.subset (hb.image (fun idx' i => idx' i + idx_a i))
    intro idx ⟨hge, hne⟩
    simp only [Set.mem_image]
    refine ⟨fun i => if i = 0 then idx 0 - idx_a 0 else idx 1 - idx_a 1, ?_, ?_⟩
    · constructor
      · intro i; fin_cases i <;> simp <;> linarith [hge 0, hge 1]
      · exact hne
    · ext i; fin_cases i <;> simp
⟩

/-! ### Embedding 1D generalized distributions into 2D -/

/-- Embed a 1D generalized distribution into 2D in the first variable (concentrated at second = 0). -/
noncomputable def embedFst (a : GeneralizedFormalDistribution A 1) : GeneralizedFormalDistribution A 2 where
  coeff := fun idx => if idx 1 = 0 then a.coeff (fun _ => idx 0) else 0
  support_finite := fun bound => by
    let bound_a : Fin 1 → ℤ := fun _ => bound 0
    have ha := a.support_finite bound_a
    have : {idx : Fin 2 → ℤ | (∀ i, idx i ≥ bound i) ∧
                               (if idx 1 = 0 then a.coeff (fun _ => idx 0) else 0) ≠ 0} ⊆
           (fun k => fun i : Fin 2 => if i = 0 then k else 0) ''
           {k : ℤ | k ≥ bound_a 0 ∧ a.coeff (fun _ => k) ≠ 0} := by
      intro idx ⟨hall, hne⟩
      split_ifs at hne with h1
      · use idx 0
        constructor
        · constructor
          · simp [bound_a]; exact hall 0
          · exact hne
        · ext i; fin_cases i <;> simp [*]
      · simp at hne
    apply Set.Finite.subset _ this
    have ha' : {k : ℤ | k ≥ bound_a 0 ∧ a.coeff (fun _ => k) ≠ 0} ⊆
               (fun idx1 : Fin 1 → ℤ => idx1 0) ''
               {idx1 : Fin 1 → ℤ | (∀ i, idx1 i ≥ bound_a i) ∧ a.coeff idx1 ≠ 0} := by
      intro k ⟨hk, ha_ne⟩
      use (fun _ => k)
      exact ⟨⟨fun i => by simp [bound_a]; exact hk, ha_ne⟩, rfl⟩
    apply Set.Finite.image
    exact Set.Finite.subset (Set.Finite.image _ ha) ha'

/-- Embed a 1D generalized distribution into 2D in the second variable (concentrated at first = 0). -/
noncomputable def embedSnd (a : GeneralizedFormalDistribution A 1) : GeneralizedFormalDistribution A 2 where
  coeff := fun idx => if idx 0 = 0 then a.coeff (fun _ => idx 1) else 0
  support_finite := fun bound => by
    let bound_a : Fin 1 → ℤ := fun _ => bound 1
    have ha := a.support_finite bound_a
    have : {idx : Fin 2 → ℤ | (∀ i, idx i ≥ bound i) ∧
                               (if idx 0 = 0 then a.coeff (fun _ => idx 1) else 0) ≠ 0} ⊆
           (fun l => fun i : Fin 2 => if i = 0 then 0 else l) ''
           {l : ℤ | l ≥ bound_a 0 ∧ a.coeff (fun _ => l) ≠ 0} := by
      intro idx ⟨hall, hne⟩
      split_ifs at hne with h0
      · use idx 1
        constructor
        · constructor
          · simp [bound_a]; exact hall 1
          · exact hne
        · ext i; fin_cases i <;> simp [*]
      · simp at hne
    apply Set.Finite.subset _ this
    have ha' : {l : ℤ | l ≥ bound_a 0 ∧ a.coeff (fun _ => l) ≠ 0} ⊆
               (fun idx1 : Fin 1 → ℤ => idx1 0) ''
               {idx1 : Fin 1 → ℤ | (∀ i, idx1 i ≥ bound_a i) ∧ a.coeff idx1 ≠ 0} := by
      intro l ⟨hl, ha_ne⟩
      use (fun _ => l)
      exact ⟨⟨fun i => by simp [bound_a]; exact hl, ha_ne⟩, rfl⟩
    apply Set.Finite.image
    exact Set.Finite.subset (Set.Finite.image _ ha) ha'

/-- Extract the residue in a specific variable from a 2D generalized distribution. -/
noncomputable def residueAt (i : Fin 2) (a : GeneralizedFormalDistribution A 2) : GeneralizedFormalDistribution A 1 where
  coeff := fun idx => a.coeff (fun j => if j = i then -1 else idx 0)
  support_finite := fun bound => by
    let bound_a : Fin 2 → ℤ := fun j => if j = i then -1 else bound 0
    have ha := a.support_finite bound_a
    have : {idx : Fin 1 → ℤ | (∀ j, idx j ≥ bound j) ∧
                               a.coeff (fun j => if j = i then -1 else idx 0) ≠ 0} ⊆
           (fun idx2 : Fin 2 → ℤ => fun _ : Fin 1 => idx2 (if i = 0 then 1 else 0)) ''
           {idx2 : Fin 2 → ℤ | (∀ j, idx2 j ≥ bound_a j) ∧ a.coeff idx2 ≠ 0} := by
      intro idx ⟨_, hne⟩
      use (fun j => if j = i then -1 else idx 0)
      constructor
      · constructor
        · intro j
          by_cases hj : j = i
          · simp [hj, bound_a]
          · fin_cases i <;> fin_cases j <;> (try simp [*]) <;> (try contradiction)
            all_goals simp [bound_a, *]
        · exact hne
      · funext j; fin_cases j; fin_cases i <;> rfl
    exact Set.Finite.subset (Set.Finite.image _ ha) this

/-- Iterated formal derivative for generalized distributions. -/
def iteratedDeriv (a : GeneralizedFormalDistribution A n) (i : Fin n) : ℕ → GeneralizedFormalDistribution A n
  | 0 => a
  | k + 1 => deriv (iteratedDeriv a i k) i

end GeneralizedFormalDistribution

/-! ### Helper lemmas for Function.update -/

/-- Updating and then evaluating at the updated index gives the new value. -/
lemma update_eval_same {n : ℕ} (idx : Fin n → ℤ) (i : Fin n) (x : ℤ) :
    Function.update idx i x i = x := by
  simp [Function.update]

/-- Updating and then evaluating at a different index gives the original value. -/
lemma update_eval_diff {n : ℕ} (idx : Fin n → ℤ) (i j : Fin n) (x : ℤ) (h : i ≠ j) :
    Function.update idx i x j = idx j := by
  simp only [Function.update]
  split_ifs with heq
  · exact absurd heq.symm h
  · rfl

/-- For `Fin 2`, if indices are different, one is 0 and the other is 1. -/
lemma fin2_ne_cases {i j : Fin 2} (h : i ≠ j) : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

namespace FormalDistribution

variable {n : ℕ}

/-- The zero formal distribution. -/
instance : Zero (FormalDistribution A n) where
  zero := ⟨fun _ => 0, by
    convert Set.finite_empty
    ext idx
    simp⟩

/-- Addition of formal distributions. -/
instance : Add (FormalDistribution A n) where
  add a b := ⟨
    fun idx => a.coeff idx + b.coeff idx,
    by
      have ha := a.support_finite
      have hb := b.support_finite
      apply Set.Finite.subset (Set.Finite.union ha hb)
      intro idx hne
      by_cases ha' : a.coeff idx ≠ 0
      · left; exact ha'
      · right; simp at ha'; simp [ha'] at hne; exact hne
  ⟩

/-- Scalar multiplication of formal distributions. -/
instance : SMul A (FormalDistribution A n) where
  smul c a := ⟨
    fun idx => c * a.coeff idx,
    by
      have ha := a.support_finite
      apply Set.Finite.subset ha
      intro idx hne
      by_cases hc : c = 0
      · simp [hc] at hne
      · exact fun h => hne (by simp [h])
  ⟩

/-! ### Support properties -/

/-- Total finite support implies finite support above any bound. -/
lemma support_finite_above_bound (a : FormalDistribution A n) (bound : Fin n → ℤ) :
    {idx : Fin n → ℤ | (∀ i, idx i ≥ bound i) ∧ a.coeff idx ≠ 0}.Finite := by
  apply Set.Finite.subset a.support_finite
  intro idx ⟨_, h⟩
  exact h

/-- Support of zero distribution is empty. -/
theorem support_zero (bound : Fin n → ℤ) :
    {idx : Fin n → ℤ | (∀ i, idx i ≥ bound i) ∧ (0 : FormalDistribution A n).coeff idx ≠ 0} = ∅ := by
  ext idx
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro ⟨_, h⟩
  exact h rfl

/-- If two distributions agree on coefficients, they are equal. -/
theorem ext_coeff {a b : FormalDistribution A n} (h : ∀ idx, a.coeff idx = b.coeff idx) : a = b := by
  ext idx
  exact h idx

end FormalDistribution
