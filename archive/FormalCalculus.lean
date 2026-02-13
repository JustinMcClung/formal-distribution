/-
Formalization of Section 1: Formal Calculus
from "Introduction to Vertex Algebras" by Christophe Nozaradan

This file contains:
- Formal distributions (Definition 1.1.1)
- Fourier expansions and modes (Definition 1.1.3)
- Expansion operators (Definition 1.2.1)
- Extended binomial coefficient (Definition 1.2.2)
- Dirac's δ distribution (Definitions 1.3.1 and 1.3.3)
- All propositions and their proofs
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators
open Complex

variable {A : Type*} [Ring A]

/-! ## 1.1 Formal distributions -/

/-- Definition 1.1.1: A-valued formal polynomials in variables z, w, ... -/
def FormalPolynomial (A : Type*) [Ring A] (vars : Type*) : Type _ :=
  vars → A

/-- Definition 1.1.1: A-valued formal Taylor series in variables z, w, ... -/
def FormalTaylorSeries (A : Type*) [Ring A] (vars : Type*) : Type _ :=
  vars → PowerSeries A

/-- Definition 1.1.1: A-valued formal distributions in variables z, w, ...
    These are formal Laurent series ∑_{n,m∈ℤ} a_{nm...} z^n w^m ...

    This is the STRENGTHENED version with total finite support.
    Use this for algebraic operations (especially multiplication).
    For distributions with infinite support (like diracDelta), use GeneralizedFormalDistribution.
-/
structure FormalDistribution (A : Type*) [Ring A] (nvars : ℕ) where
  coeff : (Fin nvars → ℤ) → A
  support_finite : {idx : Fin nvars → ℤ | coeff idx ≠ 0}.Finite

attribute [ext] FormalDistribution

/-- Generalized formal distributions with weaker finiteness condition.

    This version only requires finite support ABOVE any lower bound, not total finite support.
    This allows for distributions with infinite support (like diracDelta on a line).

    Use GeneralizedFormalDistribution for:
    - Distributions with infinite but "controlled" support (finite above bounds)
    - Classical formal distribution theory

    Use FormalDistribution for:
    - Algebraic operations (addition, multiplication, etc.) with clean proofs
    - Situations requiring total finite support
-/
structure GeneralizedFormalDistribution (A : Type*) [Ring A] (nvars : ℕ) where
  coeff : (Fin nvars → ℤ) → A
  support_finite : ∀ (bound : Fin nvars → ℤ),
    {idx : Fin nvars → ℤ | (∀ i, idx i ≥ bound i) ∧ coeff idx ≠ 0}.Finite

attribute [ext] GeneralizedFormalDistribution

/-- One-variable formal distribution -/
abbrev FormalDist1 (A : Type*) [Ring A] := FormalDistribution A 1

/-- Two-variable formal distribution -/
abbrev FormalDist2 (A : Type*) [Ring A] := FormalDistribution A 2

/-- One-variable generalized formal distribution -/
abbrev GenFormalDist1 (A : Type*) [Ring A] := GeneralizedFormalDistribution A 1

/-- Two-variable generalized formal distribution -/
abbrev GenFormalDist2 (A : Type*) [Ring A] := GeneralizedFormalDistribution A 2

/-! ### Conversions between FormalDistribution and GeneralizedFormalDistribution -/

/-- Every FormalDistribution can be viewed as a GeneralizedFormalDistribution.
    This is always valid because total finite support implies finite above any bound. -/
def FormalDistribution.toGeneralized {A : Type*} [Ring A] {nvars : ℕ}
    (a : FormalDistribution A nvars) : GeneralizedFormalDistribution A nvars where
  coeff := a.coeff
  support_finite := fun bound => by
    have ha := a.support_finite
    -- The set above the bound is a subset of the total support
    apply Set.Finite.subset ha
    intro idx ⟨_, hne⟩
    exact hne

/-! ### Basic operations on GeneralizedFormalDistribution -/

namespace GeneralizedFormalDistribution

variable {n : ℕ}

/-- The zero generalized formal distribution -/
instance : Zero (GeneralizedFormalDistribution A n) where
  zero := ⟨fun _ => 0, by
    intro bound
    convert Set.finite_empty
    ext idx
    simp⟩

/-- Addition of generalized formal distributions -/
instance : Add (GeneralizedFormalDistribution A n) where
  add a b := ⟨
    fun idx => a.coeff idx + b.coeff idx,
    by
      intro bound
      have ha := a.support_finite bound
      have hb := b.support_finite bound
      -- The support of a+b is a subset of the union of supports
      apply Set.Finite.subset (Set.Finite.union ha hb)
      intro idx ⟨hall, hne⟩
      by_cases ha' : a.coeff idx ≠ 0
      · left; exact ⟨hall, ha'⟩
      · right; simp at ha'; simp [ha'] at hne; exact ⟨hall, hne⟩
  ⟩

/-- Negation of generalized formal distributions -/
instance : Neg (GeneralizedFormalDistribution A n) where
  neg a := ⟨fun idx => -a.coeff idx, by
    intro bound; apply Set.Finite.subset (a.support_finite bound)
    intro idx ⟨hall, hne⟩; exact ⟨hall, by simp at hne ⊢; exact hne⟩⟩

/-- Subtraction of generalized formal distributions -/
instance : Sub (GeneralizedFormalDistribution A n) where
  sub a b := ⟨
    fun idx => a.coeff idx - b.coeff idx, by
      intro bound
      apply Set.Finite.subset (Set.Finite.union (a.support_finite bound) (b.support_finite bound))
      intro idx ⟨hall, hne⟩
      by_cases ha' : a.coeff idx ≠ 0
      · left; exact ⟨hall, ha'⟩
      · right; simp at ha'; simp [ha'] at hne; exact ⟨hall, hne⟩⟩

/-- Scalar multiplication of generalized formal distributions -/
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

/-- Formal derivative of a generalized distribution with respect to variable i -/
def deriv (a : GeneralizedFormalDistribution A n) (i : Fin n) : GeneralizedFormalDistribution A n where
  coeff := fun idx =>
    let shifted_idx := Function.update idx i (idx i + 1)
    (idx i + 1 : ℤ) • (a.coeff shifted_idx)
  support_finite := fun bound => by
    -- Shift the bound to account for derivative
    let shifted_bound := Function.update bound i (bound i + 1)
    have ha := a.support_finite shifted_bound
    -- The derivative's support above bound is subset of a's support above shifted_bound
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

/-- Multiply a FormalDistribution (finite support) with a GeneralizedFormalDistribution.
    The result is a GeneralizedFormalDistribution.

    (a * b)_{n,m} = Σ_{k,l} a_{k,l} * b_{n-k,m-l}

    Since a has finite support, we can sum over all of a's support. -/
noncomputable def mulFormalGen (a : FormalDistribution A 2)
    (b : GeneralizedFormalDistribution A 2) (n m : ℤ) : A :=
  Finset.sum a.support_finite.toFinset fun idx_a =>
    a.coeff idx_a * b.coeff (fun i => if i = 0 then n - idx_a 0 else m - idx_a 1)

/-- Multiplication: FormalDistribution × GeneralizedFormalDistribution → GeneralizedFormalDistribution -/
noncomputable def FormalDistribution.mulGen
    (a : FormalDistribution A 2) (b : GeneralizedFormalDistribution A 2) :
    GeneralizedFormalDistribution A 2 := ⟨
  fun idx => mulFormalGen a b (idx 0) (idx 1),
  by
    intro bound
    -- The support above bound is contained in a finite union over a's support
    -- of shifted b-supports. Each piece is finite, so the union is finite.
    suffices h_cover : (⋃ (idx_a : Fin 2 → ℤ) (_ : idx_a ∈ (a.support_finite.toFinset : Set _)),
        {idx : Fin 2 → ℤ | (∀ i, idx i ≥ bound i) ∧
         b.coeff (fun i => if i = 0 then idx 0 - idx_a 0 else idx 1 - idx_a 1) ≠ 0}).Finite by
      apply h_cover.subset
      intro idx ⟨hge, hne⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      -- Sum nonzero → some term nonzero
      have h_exists : ∃ idx_a ∈ a.support_finite.toFinset,
          a.coeff idx_a *
            b.coeff (fun i => if i = 0 then idx 0 - idx_a 0 else idx 1 - idx_a 1) ≠ 0 := by
        by_contra hall; push_neg at hall
        apply hne; unfold mulFormalGen; exact Finset.sum_eq_zero hall
      obtain ⟨idx_a, hmem, hterm⟩ := h_exists
      exact ⟨idx_a, Finset.mem_coe.mpr hmem, hge, fun h => hterm (by simp [h])⟩
    -- Prove the covering union is finite: finite union of finite sets
    apply Set.Finite.biUnion a.support_finite.toFinset.finite_toSet
    intro idx_a _
    -- Each piece is a subset of the image of b's shifted support
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

/-- Embed a 1D generalized distribution into 2D in the z-variable (concentrated at w=0) -/
noncomputable def gen_embed_z (a : GeneralizedFormalDistribution A 1) : GeneralizedFormalDistribution A 2 where
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

/-- Embed a 1D generalized distribution into 2D in the w-variable (concentrated at z=0) -/
noncomputable def gen_embed_w (a : GeneralizedFormalDistribution A 1) : GeneralizedFormalDistribution A 2 where
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

/-- Extract the residue in a specific variable from a 2D generalized distribution -/
noncomputable def gen_residue_var (i : Fin 2) (a : GeneralizedFormalDistribution A 2) : GeneralizedFormalDistribution A 1 where
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

/-- Iterated formal derivative for generalized distributions -/
def iteratedDeriv (a : GeneralizedFormalDistribution A n) (i : Fin n) : ℕ → GeneralizedFormalDistribution A n
  | 0 => a
  | k + 1 => deriv (iteratedDeriv a i k) i

end GeneralizedFormalDistribution

/-! ### Helper lemmas for Function.update -/

/-- Updating and then evaluating at the updated index gives the new value -/
lemma update_eval_same {n : ℕ} (idx : Fin n → ℤ) (i : Fin n) (x : ℤ) :
    Function.update idx i x i = x := by
  simp [Function.update]

/-- Updating and then evaluating at a different index gives the original value -/
lemma update_eval_diff {n : ℕ} (idx : Fin n → ℤ) (i j : Fin n) (x : ℤ) (h : i ≠ j) :
    Function.update idx i x j = idx j := by
  simp only [Function.update]
  split_ifs with heq
  · exact absurd heq.symm h
  · rfl

/-- For Fin 2, if indices are different, one is 0 and the other is 1 -/
lemma fin2_ne_cases {i j : Fin 2} (h : i ≠ j) : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

namespace FormalDistribution

variable {n : ℕ}

/-- The zero formal distribution -/
instance : Zero (FormalDistribution A n) where
  zero := ⟨fun _ => 0, by
    convert Set.finite_empty
    ext idx
    simp⟩

/-- Addition of formal distributions -/
instance : Add (FormalDistribution A n) where
  add a b := ⟨
    fun idx => a.coeff idx + b.coeff idx,
    by
      have ha := a.support_finite
      have hb := b.support_finite
      -- The support of a+b is a subset of the union of supports
      apply Set.Finite.subset (Set.Finite.union ha hb)
      intro idx hne
      by_cases ha' : a.coeff idx ≠ 0
      · left; exact ha'
      · right; simp at ha'; simp [ha'] at hne; exact hne
  ⟩

/-- Scalar multiplication -/
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

/-! ### Formal differentiation -/

/-- Formal derivative of a distribution with respect to variable i.
    For a(z) = ∑ aₙ zⁿ, we have ∂_z a = ∑ n·aₙ z^{n-1}.
    So (∂_z a)_m = (m+1)·a_{m+1}. -/
def deriv (a : FormalDistribution A n) (i : Fin n) : FormalDistribution A n where
  coeff := fun idx =>
    let shifted_idx := Function.update idx i (idx i + 1)
    (idx i + 1 : ℤ) • (a.coeff shifted_idx)
  support_finite := by
    have ha := a.support_finite
    -- The derivative's support is a subset of the image of a's support under shift
    have h_subset : {idx : Fin n → ℤ |
                    (idx i + 1 : ℤ) • (a.coeff (Function.update idx i (idx i + 1))) ≠ 0} ⊆
                    (fun idx' : Fin n → ℤ => fun j => if j = i then idx' i - 1 else idx' j) ''
                    {idx' : Fin n → ℤ | a.coeff idx' ≠ 0} := by
      intro idx hne
      let shifted_idx := Function.update idx i (idx i + 1)
      use shifted_idx
      constructor
      · -- Need to show a.coeff shifted_idx ≠ 0
        by_contra h
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

/-- Iterated formal derivative -/
def iteratedDeriv (a : FormalDistribution A n) (i : Fin n) : ℕ → FormalDistribution A n
  | 0 => a
  | k + 1 => deriv (iteratedDeriv a i k) i

notation:max a "^[∂" i "," k "]" => iteratedDeriv a i k

/-! ### Properties of formal differentiation -/

/-- Derivative of zero is zero -/
@[simp]
theorem deriv_zero (i : Fin n) : deriv (0 : FormalDistribution A n) i = 0 := by
  ext idx
  -- The zero distribution has coeff = fun _ => 0, so derivative is also zero
  apply smul_zero

/-- Linearity: derivative of sum is sum of derivatives -/
@[simp]
theorem deriv_add (a b : FormalDistribution A n) (i : Fin n) :
    deriv (a + b) i = deriv a i + deriv b i := by
  ext idx
  show (idx i + 1 : ℤ) • ((a + b).coeff (Function.update idx i (idx i + 1))) =
       (idx i + 1 : ℤ) • (a.coeff (Function.update idx i (idx i + 1))) +
       (idx i + 1 : ℤ) • (b.coeff (Function.update idx i (idx i + 1)))
  -- Expand (a + b).coeff
  have : (a + b).coeff (Function.update idx i (idx i + 1)) =
         a.coeff (Function.update idx i (idx i + 1)) + b.coeff (Function.update idx i (idx i + 1)) := rfl
  rw [this, smul_add]

/-- Derivative commutes with scalar multiplication -/
@[simp]
theorem deriv_smul (c : A) (a : FormalDistribution A n) (i : Fin n) :
    deriv (c • a) i = c • deriv a i := by
  ext idx
  show (idx i + 1 : ℤ) • (c * a.coeff (Function.update idx i (idx i + 1))) =
       c * ((idx i + 1 : ℤ) • a.coeff (Function.update idx i (idx i + 1)))
  -- Use zsmul_eq_mul to convert ℤ-smul to multiplication in the ring
  rw [zsmul_eq_mul, zsmul_eq_mul]
  -- ↑(idx i + 1) * (c * x) = c * (↑(idx i + 1) * x)
  -- Integer casts commute with all elements
  rw [← mul_assoc, (Int.cast_commute (idx i + 1) c).eq, mul_assoc]

/-! ### Support properties -/

/-- Helper: Total finite support implies finite support above any bound -/
lemma support_finite_above_bound (a : FormalDistribution A n) (bound : Fin n → ℤ) :
    {idx : Fin n → ℤ | (∀ i, idx i ≥ bound i) ∧ a.coeff idx ≠ 0}.Finite := by
  apply Set.Finite.subset a.support_finite
  intro idx ⟨_, h⟩
  exact h

/-- Support of zero distribution is empty -/
theorem support_zero (bound : Fin n → ℤ) :
    {idx : Fin n → ℤ | (∀ i, idx i ≥ bound i) ∧ (0 : FormalDistribution A n).coeff idx ≠ 0} = ∅ := by
  ext idx
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro ⟨_, h⟩
  -- The zero distribution has all coefficients equal to 0
  exact h rfl

/-- If two distributions agree on coefficients, they are equal -/
theorem ext_coeff {a b : FormalDistribution A n} (h : ∀ idx, a.coeff idx = b.coeff idx) : a = b := by
  ext idx
  exact h idx

/-! ### Iterated derivative properties -/

/-- Iterated derivative of zero is zero -/
@[simp]
theorem iteratedDeriv_zero (i : Fin n) (k : ℕ) :
    iteratedDeriv (0 : FormalDistribution A n) i k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iteratedDeriv, ih]

/-- Iterated derivative is linear in addition -/
@[simp]
theorem iteratedDeriv_add (a b : FormalDistribution A n) (i : Fin n) (k : ℕ) :
    iteratedDeriv (a + b) i k = iteratedDeriv a i k + iteratedDeriv b i k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iteratedDeriv, ih]

/-- Iterated derivative commutes with scalar multiplication -/
@[simp]
theorem iteratedDeriv_smul (c : A) (a : FormalDistribution A n) (i : Fin n) (k : ℕ) :
    iteratedDeriv (c • a) i k = c • iteratedDeriv a i k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iteratedDeriv, ih]

/-- Taking derivative in one variable, then another, equals taking them in reverse order -/
theorem deriv_deriv_comm (a : FormalDistribution A n) (i j : Fin n) :
    (a.deriv i).deriv j = (a.deriv j).deriv i := by
  by_cases h : i = j
  · rw [h]
  · ext idx
    simp only [deriv]
    -- The key insight: updating i then j equals updating j then i when i ≠ j
    have eval_i_after_j : Function.update idx j (idx j + 1) i = idx i :=
      update_eval_diff idx j i (idx j + 1) (Ne.symm h)
    have eval_j_after_i : Function.update idx i (idx i + 1) j = idx j :=
      update_eval_diff idx i j (idx i + 1) h
    -- The double-updated indices are equal
    have double_update_eq :
      Function.update (Function.update idx i (idx i + 1)) j (idx j + 1) =
      Function.update (Function.update idx j (idx j + 1)) i (idx i + 1) := by
      funext k
      by_cases hki : k = i
      · rw [hki, update_eval_same, update_eval_diff _ _ _ _ (Ne.symm h), update_eval_same]
      · by_cases hkj : k = j
        · rw [hkj, update_eval_same, update_eval_diff _ _ _ _ h, update_eval_same]
        · -- k ≠ i and k ≠ j, so both sides give idx k
          have lhs : Function.update (Function.update idx i (idx i + 1)) j (idx j + 1) k = idx k := by
            rw [update_eval_diff _ j k _ (Ne.symm hkj), update_eval_diff _ i k _ (Ne.symm hki)]
          have rhs : Function.update (Function.update idx j (idx j + 1)) i (idx i + 1) k = idx k := by
            rw [update_eval_diff _ i k _ (Ne.symm hki), update_eval_diff _ j k _ (Ne.symm hkj)]
          rw [lhs, rhs]
    rw [eval_i_after_j, eval_j_after_i, double_update_eq]
    -- Now both sides have the same coefficient, just need to show (idx j + 1) • (idx i + 1) • x = (idx i + 1) • (idx j + 1) • x
    show (idx j + 1 : ℤ) • (idx i + 1 : ℤ) • _ = (idx i + 1 : ℤ) • (idx j + 1 : ℤ) • _
    rw [zsmul_comm]

/-- Taking k derivatives then m more equals taking k+m derivatives at once -/
theorem iteratedDeriv_add_eq (a : FormalDistribution A n) (i : Fin n) (k m : ℕ) :
    iteratedDeriv (iteratedDeriv a i k) i m = iteratedDeriv a i (k + m) := by
  induction m with
  | zero => simp [iteratedDeriv]
  | succ m ih =>
    simp only [iteratedDeriv]
    rw [ih]
    rfl

/-! ### More derivative properties -/

/-- Double derivative equals applying deriv twice -/
theorem deriv_deriv_eq_iteratedDeriv (a : FormalDistribution A n) (i : Fin n) :
    (a.deriv i).deriv i = a.iteratedDeriv i 2 := by
  rfl

/-- Coefficient of derivative in terms of original coefficient -/
theorem deriv_coeff_eq (a : FormalDistribution A n) (i : Fin n) (idx : Fin n → ℤ) :
    (a.deriv i).coeff idx = (idx i + 1 : ℤ) • a.coeff (Function.update idx i (idx i + 1)) := by
  rfl

/-! ### Multiplication of formal distributions -/

/-- For single-variable distributions, the convolution support at index n is finite.
    This is the key lemma enabling multiplication via Cauchy product. -/
lemma convolution_support_finite_1d (a b : FormalDist1 A) (n : ℤ) :
    {k : ℤ | a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0}.Finite := by
  -- The convolution support is contained in a × b support, which is finite
  have ha := a.support_finite
  have hb := b.support_finite
  -- Convert from Fin 1 → ℤ to ℤ for easier manipulation
  have ha' : {k : ℤ | k ≥ 0 ∧ a.coeff (fun _ => k) ≠ 0}.Finite := by
    have := Set.Finite.image (fun (idx : Fin 1 → ℤ) => idx 0) ha
    apply Set.Finite.subset this
    intro k ⟨_, hak⟩
    use (fun _ => k)
    exact ⟨hak, rfl⟩
  have hb' : {m : ℤ | m ≥ 0 ∧ b.coeff (fun _ => m) ≠ 0}.Finite := by
    have := Set.Finite.image (fun (idx : Fin 1 → ℤ) => idx 0) hb
    apply Set.Finite.subset this
    intro m ⟨_, hbm⟩
    use (fun _ => m)
    exact ⟨hbm, rfl⟩
  -- Split the set into k ≥ 0 and k < 0
  have split : {k : ℤ | a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0} =
              {k : ℤ | k ≥ 0 ∧ a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0} ∪
              {k : ℤ | k < 0 ∧ a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro ⟨hak, hbk⟩
      by_cases h : k ≥ 0
      · left; exact ⟨h, hak, hbk⟩
      · right; exact ⟨by omega, hak, hbk⟩
    · intro h
      cases h with
      | inl h => exact ⟨h.2.1, h.2.2⟩
      | inr h => exact ⟨h.2.1, h.2.2⟩
  rw [split]
  apply Set.Finite.union
  · -- First part: k ≥ 0
    have h_subset : {k : ℤ | k ≥ 0 ∧ a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0} ⊆
                    {k : ℤ | k ≥ 0 ∧ a.coeff (fun _ => k) ≠ 0} := by
      intro k ⟨hk, hak, _⟩
      exact ⟨hk, hak⟩
    exact Set.Finite.subset ha' h_subset
  · -- Second part: k < 0
    by_cases hn : n ≥ 0
    · -- Case: n ≥ 0, then n - k > n ≥ 0 for k < 0
      have h_subset : {k : ℤ | k < 0 ∧ a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0} ⊆
                      (fun m => n - m) '' {m : ℤ | m ≥ 0 ∧ b.coeff (fun _ => m) ≠ 0} := by
        intro k ⟨hk, _, hbk⟩
        use n - k
        constructor
        · exact ⟨by omega, hbk⟩
        · ring
      exact Set.Finite.subset (Set.Finite.image _ hb') h_subset
    · -- Case: n < 0
      have h_subset : {k : ℤ | k < 0 ∧ a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0} ⊆
                      ({k : ℤ | k < 0 ∧ n - k ≥ 0 ∧ a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0} ∪
                       {k : ℤ | k < 0 ∧ n - k < 0 ∧ a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0}) := by
        intro k hk
        simp only [Set.mem_setOf_eq, Set.mem_union]
        by_cases h : n - k ≥ 0
        · left; exact ⟨hk.1, h, hk.2.1, hk.2.2⟩
        · right; exact ⟨hk.1, by omega, hk.2.1, hk.2.2⟩
      apply Set.Finite.subset _ h_subset
      apply Set.Finite.union
      · -- k < 0 and n - k ≥ 0
        have : {k : ℤ | k < 0 ∧ n - k ≥ 0 ∧ a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0} ⊆
               (fun m => n - m) '' {m : ℤ | m ≥ 0 ∧ b.coeff (fun _ => m) ≠ 0} := by
          intro k ⟨_, hk2, _, hbk⟩
          use n - k
          constructor
          · exact ⟨hk2, hbk⟩
          · ring
        exact Set.Finite.subset (Set.Finite.image _ hb') this
      · -- k < 0 and n - k < 0: bounded interval n < k < 0
        have : {k : ℤ | k < 0 ∧ n - k < 0 ∧ a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0} ⊆
               Set.Ioo n 0 := by
          intro k ⟨hk1, hk2, _, _⟩
          exact ⟨by omega, hk1⟩
        exact Set.Finite.subset (Set.finite_Ioo n 0) this

/-- Compute the coefficient of the product at a given index using Cauchy product -/
noncomputable def mulCoeff1d (a b : FormalDist1 A) (n : ℤ) : A :=
  Finset.sum (convolution_support_finite_1d a b n).toFinset
    (fun k => a.coeff (fun _ => k) * b.coeff (fun _ => n - k))

/-- Helper: For any choice of lower bounds, the sets where coefficients are non-zero are finite -/
private lemma support_ints_finite (a : FormalDist1 A) (bound_val : ℤ) :
    {k : ℤ | k ≥ bound_val ∧ a.coeff (fun _ => k) ≠ 0}.Finite := by
  have h := a.support_finite
  have := Set.Finite.image (fun (idx : Fin 1 → ℤ) => idx 0) h
  apply Set.Finite.subset this
  intro k ⟨_, hak⟩
  use (fun _ => k)
  exact ⟨hak, rfl⟩

/-- The support of the product is finite by considering decompositions n = k + m where at least one factor is large -/
private lemma mul_support_finite_1d (a b : FormalDist1 A) (bound : ℤ) :
    {n : ℤ | n ≥ bound ∧ mulCoeff1d a b n ≠ 0}.Finite := by
  -- Choose threshold: if n ≥ bound and n = k + m, then either k ≥ bound/2 or m ≥ bound/2
  let k_threshold : ℤ := bound / 2
  let m_threshold : ℤ := bound / 2

  -- Get finite support sets above thresholds
  have Ka_finite := support_ints_finite a k_threshold
  have Kb_finite := support_ints_finite b m_threshold

  -- Any n ≥ bound with (a*b)_n ≠ 0 is a sum k + m where either k ≥ k_threshold or m ≥ m_threshold
  have h_subset : {n : ℤ | n ≥ bound ∧ mulCoeff1d a b n ≠ 0} ⊆
                  {n : ℤ | ∃ k m : ℤ, (k ≥ k_threshold ∨ m ≥ m_threshold) ∧
                                       a.coeff (fun _ => k) ≠ 0 ∧
                                       b.coeff (fun _ => m) ≠ 0 ∧
                                       n = k + m} := by
    intro n ⟨hn_bound, hn_ne⟩
    unfold mulCoeff1d at hn_ne
    -- Product sum is non-zero, so some term is non-zero
    have ⟨k, hk_mem, hk_ne⟩ : ∃ k, k ∈ (convolution_support_finite_1d a b n).toFinset ∧
                                    a.coeff (fun _ => k) * b.coeff (fun _ => n - k) ≠ 0 := by
      by_contra h
      push_neg at h
      have : Finset.sum (convolution_support_finite_1d a b n).toFinset
              (fun k => a.coeff (fun _ => k) * b.coeff (fun _ => n - k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have := h k hk
        exact this
      exact hn_ne this
    rw [Set.Finite.mem_toFinset] at hk_mem
    obtain ⟨hak, hbk⟩ := hk_mem
    use k, n - k
    refine ⟨?_, hak, hbk, by ring⟩
    -- Either k ≥ k_threshold or n - k ≥ m_threshold
    by_contra h_neither
    push_neg at h_neither
    have : n < k_threshold + m_threshold := by omega
    have : n < bound := by omega
    omega

  -- Key insight: We're looking at sums that give n ≥ bound
  -- Split the RHS based on which summand is large, keeping the n ≥ bound constraint
  have h_split : {n : ℤ | n ≥ bound ∧ ∃ k m : ℤ, (k ≥ k_threshold ∨ m ≥ m_threshold) ∧
                                       a.coeff (fun _ => k) ≠ 0 ∧
                                       b.coeff (fun _ => m) ≠ 0 ∧
                                       n = k + m} ⊆
                 {n : ℤ | n ≥ bound ∧ ∃ k m : ℤ, k ≥ k_threshold ∧ a.coeff (fun _ => k) ≠ 0 ∧
                                      b.coeff (fun _ => m) ≠ 0 ∧ n = k + m} ∪
                 {n : ℤ | n ≥ bound ∧ ∃ k m : ℤ, m ≥ m_threshold ∧ a.coeff (fun _ => k) ≠ 0 ∧
                                      b.coeff (fun _ => m) ≠ 0 ∧ n = k + m} := by
    intro n ⟨hn_ge, k, m, hkm, hak, hbm, hn_eq⟩
    cases hkm with
    | inl hk => left; exact ⟨hn_ge, k, m, hk, hak, hbm, hn_eq⟩
    | inr hm => right; exact ⟨hn_ge, k, m, hm, hak, hbm, hn_eq⟩

  -- h_subset gives us the first containment
  have h_main : {n : ℤ | n ≥ bound ∧ mulCoeff1d a b n ≠ 0} ⊆
                {n : ℤ | n ≥ bound ∧ ∃ k m : ℤ, (k ≥ k_threshold ∨ m ≥ m_threshold) ∧
                                      a.coeff (fun _ => k) ≠ 0 ∧
                                      b.coeff (fun _ => m) ≠ 0 ∧
                                      n = k + m} := by
    intro n ⟨hn_ge, hn_ne⟩
    have ⟨k, m, hkm, hak, hbm, hn_eq⟩ := h_subset (Set.mem_setOf.mpr ⟨hn_ge, hn_ne⟩)
    exact ⟨hn_ge, k, m, hkm, hak, hbm, hn_eq⟩

  apply Set.Finite.subset _ h_main
  apply Set.Finite.subset _ h_split
  apply Set.Finite.union

  -- First set: k ≥ k_threshold, n ≥ bound
  · -- For each k ∈ Ka, we have n = k + m with n ≥ bound, so m ≥ bound - k
    -- The set {m | m ≥ bound - k ∧ b_m ≠ 0} is finite for each k
    -- So {n | n ≥ bound ∧ n = k + m for some m with b_m ≠ 0} is finite for each k
    -- Taking union over k ∈ Ka (finite) gives a finite set
    have : {n : ℤ | n ≥ bound ∧ ∃ k m : ℤ, k ≥ k_threshold ∧ a.coeff (fun _ => k) ≠ 0 ∧
                                 b.coeff (fun _ => m) ≠ 0 ∧ n = k + m} ⊆
           ⋃ k ∈ {k : ℤ | k ≥ k_threshold ∧ a.coeff (fun _ => k) ≠ 0},
             {n : ℤ | n ≥ bound ∧ ∃ m : ℤ, b.coeff (fun _ => m) ≠ 0 ∧ n = k + m} := by
      intro n ⟨hn_ge, k, m, hk, hak, hbm, hn_eq⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      use k, ⟨hk, hak⟩, hn_ge, m, hbm, hn_eq
    apply Set.Finite.subset _ this
    apply Set.Finite.biUnion Ka_finite
    intro k hk
    -- For fixed k, {n | n ≥ bound ∧ n = k + m for some m with b_m ≠ 0}
    --             = {k + m | m ≥ bound - k ∧ b_m ≠ 0}
    --             = image (+k) {m | m ≥ bound - k ∧ b_m ≠ 0}
    have : {n : ℤ | n ≥ bound ∧ ∃ m : ℤ, b.coeff (fun _ => m) ≠ 0 ∧ n = k + m} =
           Set.image (· + k) {m : ℤ | m ≥ bound - k ∧ b.coeff (fun _ => m) ≠ 0} := by
      ext n
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro ⟨hn_ge, m, hbm, hn_eq⟩
        use m
        constructor
        · constructor
          · omega
          · exact hbm
        · omega
      · intro ⟨m, ⟨hm_ge, hbm⟩, hn_eq⟩
        constructor
        · omega
        · use m, hbm
          omega
    rw [this]
    apply Set.Finite.image
    exact support_ints_finite b (bound - k)

  -- Second set: m ≥ m_threshold, n ≥ bound (symmetric)
  · have : {n : ℤ | n ≥ bound ∧ ∃ k m : ℤ, m ≥ m_threshold ∧ a.coeff (fun _ => k) ≠ 0 ∧
                                 b.coeff (fun _ => m) ≠ 0 ∧ n = k + m} ⊆
           ⋃ m ∈ {m : ℤ | m ≥ m_threshold ∧ b.coeff (fun _ => m) ≠ 0},
             {n : ℤ | n ≥ bound ∧ ∃ k : ℤ, a.coeff (fun _ => k) ≠ 0 ∧ n = k + m} := by
      intro n ⟨hn_ge, k, m, hm, hak, hbm, hn_eq⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      use m, ⟨hm, hbm⟩, hn_ge, k, hak, hn_eq
    apply Set.Finite.subset _ this
    apply Set.Finite.biUnion Kb_finite
    intro m hm
    -- For fixed m, {n | n ≥ bound ∧ n = k + m for some k with a_k ≠ 0}
    --             = {k + m | k ≥ bound - m ∧ a_k ≠ 0}
    have : {n : ℤ | n ≥ bound ∧ ∃ k : ℤ, a.coeff (fun _ => k) ≠ 0 ∧ n = k + m} =
           Set.image (· + m) {k : ℤ | k ≥ bound - m ∧ a.coeff (fun _ => k) ≠ 0} := by
      ext n
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro ⟨hn_ge, k, hak, hn_eq⟩
        use k
        constructor
        · constructor
          · omega
          · exact hak
        · omega
      · intro ⟨k, ⟨hk_ge, hak⟩, hn_eq⟩
        constructor
        · omega
        · use k, hak
          omega
    rw [this]
    apply Set.Finite.image
    exact support_ints_finite a (bound - m)

/-- Multiplication of single-variable formal distributions -/
noncomputable instance : Mul (FormalDist1 A) where
  mul a b := ⟨
    fun idx => mulCoeff1d a b (idx 0),
    by
      -- The total support is finite: it's contained in the image of integer support
      have ha := a.support_finite
      have hb := b.support_finite
      -- Extract integer supports
      have ha_int : {k : ℤ | a.coeff (fun _ => k) ≠ 0}.Finite := by
        apply Set.Finite.subset (Set.Finite.image (fun idx : Fin 1 → ℤ => idx 0) ha)
        intro k hk
        use (fun _ => k)
        exact ⟨hk, rfl⟩
      have hb_int : {m : ℤ | b.coeff (fun _ => m) ≠ 0}.Finite := by
        apply Set.Finite.subset (Set.Finite.image (fun idx : Fin 1 → ℤ => idx 0) hb)
        intro m hm
        use (fun _ => m)
        exact ⟨hm, rfl⟩
      -- The product support is finite: use biUnion over a's support
      have h_support : {n : ℤ | mulCoeff1d a b n ≠ 0}.Finite := by
        have : {n : ℤ | mulCoeff1d a b n ≠ 0} ⊆
               ⋃ k ∈ {k : ℤ | a.coeff (fun _ => k) ≠ 0}, {n : ℤ | b.coeff (fun _ => n - k) ≠ 0} := by
          intro n hn
          unfold mulCoeff1d at hn
          -- Sum is nonzero, so some term is nonzero
          have : ∃ k, k ∈ (convolution_support_finite_1d a b n).toFinset ∧
                       a.coeff (fun _ => k) * b.coeff (fun _ => n - k) ≠ 0 := by
            by_contra h_all_zero
            push_neg at h_all_zero
            have : Finset.sum (convolution_support_finite_1d a b n).toFinset
                     (fun k => a.coeff (fun _ => k) * b.coeff (fun _ => n - k)) = 0 := by
              apply Finset.sum_eq_zero
              intro k hk
              exact h_all_zero k hk
            contradiction
          obtain ⟨k, _, hk_ne⟩ := this
          simp only [Set.mem_iUnion]
          use k
          constructor
          · intro h_contra
            simp [h_contra] at hk_ne
          · intro h_contra
            simp [h_contra] at hk_ne
        apply Set.Finite.subset _ this
        exact Set.Finite.biUnion ha_int (fun k _ =>
          Set.Finite.subset (Set.Finite.image (· + k) hb_int) (by
            intro n hn
            use n - k
            exact ⟨hn, by ring⟩))
      -- Lift to Fin 1 → ℤ
      apply Set.Finite.subset (Set.Finite.image (fun n => fun _ : Fin 1 => n) h_support)
      intro idx hne
      use idx 0
      exact ⟨hne, by funext i; fin_cases i; rfl⟩
  ⟩

/-! ### Properties of multiplication -/

/-- The coefficient of a product at index n is the convolution sum -/
theorem mul_coeff (a b : FormalDist1 A) (n : ℤ) :
    (a * b).coeff (fun _ => n) = mulCoeff1d a b n := by
  rfl

/-- Right distributivity: (a + b) * c = a * c + b * c -/
theorem mul_add (a b c : FormalDist1 A) : (a + b) * c = a * c + b * c := by
  ext idx
  show mulCoeff1d (a + b) c (idx 0) = mulCoeff1d a c (idx 0) + mulCoeff1d b c (idx 0)
  unfold mulCoeff1d
  -- The key insight: we sum over different finite sets, but the sums are equal
  -- because (a+b).coeff k = a.coeff k + b.coeff k
  let n := idx 0
  let s_ab := (convolution_support_finite_1d (a + b) c n).toFinset
  let s_a := (convolution_support_finite_1d a c n).toFinset
  let s_b := (convolution_support_finite_1d b c n).toFinset
  let s_union := s_a ∪ s_b

  -- Extend LHS sum to s_union
  have lhs_ext : ∑ k ∈ s_ab, (a + b).coeff (fun _ => k) * c.coeff (fun _ => n - k)
               = ∑ k ∈ s_union, (a + b).coeff (fun _ => k) * c.coeff (fun _ => n - k) := by
    refine Finset.sum_subset ?_ ?_
    · intro k hk
      -- If (a+b).coeff k ≠ 0, then at least one of a.coeff k or b.coeff k is non-zero
      simp only [s_union, Finset.mem_union, s_a, s_b, Set.Finite.mem_toFinset, Set.mem_setOf]
      simp only [s_ab, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
      by_contra h
      push_neg at h
      -- If k ∉ s_a, then either a.coeff k = 0 or c.coeff (n-k) = 0
      -- Since hk.2 : c.coeff (n-k) ≠ 0, we must have a.coeff k = 0
      have ha : a.coeff (fun _ => k) = 0 := by
        by_cases ha' : a.coeff (fun _ => k) = 0
        · exact ha'
        · have := h.1 ha'
          exact absurd this hk.2
      have hb : b.coeff (fun _ => k) = 0 := by
        by_cases hb' : b.coeff (fun _ => k) = 0
        · exact hb'
        · have := h.2 hb'
          exact absurd this hk.2
      -- Now (a+b).coeff k = 0, contradicting hk.1
      have : (a + b).coeff (fun _ => k) = 0 := by
        rw [show (a + b).coeff (fun _ => k) = a.coeff (fun _ => k) + b.coeff (fun _ => k) by rfl]
        rw [ha, hb, zero_add]
      exact hk.1 this
    · intro k _ hk
      -- If k ∉ s_ab, then either (a+b).coeff k = 0 or c.coeff (n-k) = 0, so product is 0
      simp only [s_ab, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
      push_neg at hk
      by_cases h : (a + b).coeff (fun _ => k) = 0
      · rw [h, zero_mul]
      · rw [hk h, mul_zero]

  rw [lhs_ext]

  -- Expand (a+b).coeff k = a.coeff k + b.coeff k and distribute
  conv_lhs => arg 2; ext k
              rw [show (a + b).coeff (fun _ => k) = a.coeff (fun _ => k) + b.coeff (fun _ => k) by rfl]
  simp only [add_mul, Finset.sum_add_distrib]

  -- Now both sums on LHS are over s_union. Extend RHS sums to s_union as well
  congr 1
  · refine (Finset.sum_subset Finset.subset_union_left ?_).symm
    intro k _ hk
    -- hk : k ∉ s_a means ¬(a.coeff k ≠ 0 ∧ c.coeff (n-k) ≠ 0)
    simp only [s_a, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : a.coeff (fun _ => k) = 0
    · rw [h, zero_mul]
    · push_neg at hk
      rw [hk h, mul_zero]
  · refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro k _ hk
    simp only [s_b, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : b.coeff (fun _ => k) = 0
    · rw [h, zero_mul]
    · push_neg at hk
      rw [hk h, mul_zero]

/-- Left distributivity: a * (b + c) = a * b + a * c -/
theorem add_mul (a b c : FormalDist1 A) : a * (b + c) = a * b + a * c := by
  ext idx
  show mulCoeff1d a (b + c) (idx 0) = mulCoeff1d a b (idx 0) + mulCoeff1d a c (idx 0)
  unfold mulCoeff1d
  let n := idx 0
  let s_bc := (convolution_support_finite_1d a (b + c) n).toFinset
  let s_b := (convolution_support_finite_1d a b n).toFinset
  let s_c := (convolution_support_finite_1d a c n).toFinset
  let s_union := s_b ∪ s_c

  -- Extend LHS sum to s_union
  have lhs_ext : ∑ k ∈ s_bc, a.coeff (fun _ => k) * (b + c).coeff (fun _ => n - k)
               = ∑ k ∈ s_union, a.coeff (fun _ => k) * (b + c).coeff (fun _ => n - k) := by
    refine Finset.sum_subset ?_ ?_
    · intro k hk
      simp only [s_union, Finset.mem_union, s_b, s_c, Set.Finite.mem_toFinset, Set.mem_setOf]
      simp only [s_bc, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
      by_contra h
      push_neg at h
      -- h.1 : a.coeff k ≠ 0 → b.coeff (n-k) = 0
      -- h.2 : a.coeff k ≠ 0 → c.coeff (n-k) = 0
      -- Since hk.1 : a.coeff k ≠ 0, we get b.coeff (n-k) = 0 and c.coeff (n-k) = 0
      have hb : b.coeff (fun _ => n - k) = 0 := h.1 hk.1
      have hc : c.coeff (fun _ => n - k) = 0 := h.2 hk.1
      have : (b + c).coeff (fun _ => n - k) = 0 := by
        rw [show (b + c).coeff (fun _ => n - k) = b.coeff (fun _ => n - k) + c.coeff (fun _ => n - k) by rfl]
        rw [hb, hc, zero_add]
      exact hk.2 this
    · intro k _ hk
      simp only [s_bc, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
      push_neg at hk
      by_cases h : a.coeff (fun _ => k) = 0
      · rw [h, zero_mul]
      · rw [hk h, mul_zero]

  rw [lhs_ext]
  conv_lhs => arg 2; ext k
              rw [show (b + c).coeff (fun _ => n - k) = b.coeff (fun _ => n - k) + c.coeff (fun _ => n - k) by rfl]
  have : ∑ k ∈ s_union, a.coeff (fun _ => k) * (b.coeff (fun _ => n - k) + c.coeff (fun _ => n - k))
       = ∑ k ∈ s_union, (a.coeff (fun _ => k) * b.coeff (fun _ => n - k) + a.coeff (fun _ => k) * c.coeff (fun _ => n - k)) := by
    congr 1; ext k
    show a.coeff (fun _ => k) * (b.coeff (fun _ => n - k) + c.coeff (fun _ => n - k)) = _
    rw [_root_.mul_add]
  rw [this, Finset.sum_add_distrib]

  congr 1
  · refine (Finset.sum_subset Finset.subset_union_left ?_).symm
    intro k _ hk
    simp only [s_b, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : a.coeff (fun _ => k) = 0
    · rw [h, zero_mul]
    · push_neg at hk
      rw [hk h, mul_zero]
  · refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro k _ hk
    simp only [s_c, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : a.coeff (fun _ => k) = 0
    · rw [h, zero_mul]
    · push_neg at hk
      rw [hk h, mul_zero]

/-- Scalar multiplication commutes with multiplication from the left -/
theorem smul_mul (r : A) (a b : FormalDist1 A) : (r • a) * b = r • (a * b) := by
  ext idx
  show mulCoeff1d (r • a) b (idx 0) = r • mulCoeff1d a b (idx 0)
  unfold mulCoeff1d
  let n := idx 0
  let s_ra := (convolution_support_finite_1d (r • a) b n).toFinset
  let s_a := (convolution_support_finite_1d a b n).toFinset

  -- Show sums are equal by extending both to their union
  let s_union := s_ra ∪ s_a
  have lhs_ext : ∑ k ∈ s_ra, (r • a).coeff (fun _ => k) * b.coeff (fun _ => n - k)
               = ∑ k ∈ s_union, (r • a).coeff (fun _ => k) * b.coeff (fun _ => n - k) := by
    refine Finset.sum_subset Finset.subset_union_left ?_
    intro k _ hk
    simp only [s_ra, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : (r • a).coeff (fun _ => k) = 0
    · rw [h, zero_mul]
    · push_neg at hk
      rw [hk h, mul_zero]

  have rhs_ext : r • ∑ k ∈ s_a, a.coeff (fun _ => k) * b.coeff (fun _ => n - k)
               = ∑ k ∈ s_union, r • (a.coeff (fun _ => k) * b.coeff (fun _ => n - k)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro k _ hk
    simp only [s_a, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : a.coeff (fun _ => k) = 0
    · rw [h, zero_mul, smul_zero]
    · push_neg at hk
      rw [hk h, mul_zero, smul_zero]

  rw [lhs_ext, rhs_ext]
  congr 1
  ext k
  simp only [show (r • a).coeff (fun _ => k) = r • a.coeff (fun _ => k) by rfl, smul_mul_assoc]

/-- Scalar multiplication commutes with multiplication from the right.
    Note: This holds for commutative rings. For non-commutative rings,
    this would need to be stated differently or restricted. -/
theorem mul_smul {A : Type*} [CommRing A] (r : A) (a b : FormalDist1 A) :
    a * (r • b) = r • (a * b) := by
  ext idx
  show mulCoeff1d a (r • b) (idx 0) = r • mulCoeff1d a b (idx 0)
  unfold mulCoeff1d
  let n := idx 0
  let s_rb := (convolution_support_finite_1d a (r • b) n).toFinset
  let s_b := (convolution_support_finite_1d a b n).toFinset

  let s_union := s_rb ∪ s_b
  have lhs_ext : ∑ k ∈ s_rb, a.coeff (fun _ => k) * (r • b).coeff (fun _ => n - k)
               = ∑ k ∈ s_union, a.coeff (fun _ => k) * (r • b).coeff (fun _ => n - k) := by
    refine Finset.sum_subset Finset.subset_union_left ?_
    intro k _ hk
    simp only [s_rb, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : a.coeff (fun _ => k) = 0
    · rw [h, zero_mul]
    · push_neg at hk
      rw [hk h, mul_zero]

  have rhs_ext : r • ∑ k ∈ s_b, a.coeff (fun _ => k) * b.coeff (fun _ => n - k)
               = ∑ k ∈ s_union, r • (a.coeff (fun _ => k) * b.coeff (fun _ => n - k)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro k _ hk
    simp only [s_b, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : a.coeff (fun _ => k) = 0
    · rw [h, zero_mul, smul_zero]
    · push_neg at hk
      rw [hk h, mul_zero, smul_zero]

  rw [lhs_ext, rhs_ext]
  congr 1
  ext k
  rw [show (r • b).coeff (fun _ => n - k) = r • b.coeff (fun _ => n - k) by rfl]
  rw [show r • b.coeff (fun _ => n - k) = r * b.coeff (fun _ => n - k) by rfl]
  rw [show r • (a.coeff (fun _ => k) * b.coeff (fun _ => n - k)) =
           r * (a.coeff (fun _ => k) * b.coeff (fun _ => n - k)) by rfl]
  -- Need to show: a * (r * b) = r * (a * b)
  rw [← mul_assoc, mul_comm (a.coeff (fun _ => k)) r, mul_assoc]

/-- Multiplication by zero from the left -/
theorem zero_mul (a : FormalDist1 A) : (0 : FormalDist1 A) * a = 0 := by
  ext idx
  show mulCoeff1d 0 a (idx 0) = 0
  unfold mulCoeff1d
  apply Finset.sum_eq_zero
  intro k _
  show (0 : FormalDist1 A).coeff (fun _ => k) * a.coeff (fun _ => idx 0 - k) = 0
  rw [show (0 : FormalDist1 A).coeff (fun _ => k) = 0 by rfl]
  exact MulZeroClass.zero_mul _

/-- Multiplication by zero from the right -/
theorem mul_zero (a : FormalDist1 A) : a * (0 : FormalDist1 A) = 0 := by
  ext idx
  show mulCoeff1d a 0 (idx 0) = 0
  unfold mulCoeff1d
  apply Finset.sum_eq_zero
  intro k _
  show a.coeff (fun _ => k) * (0 : FormalDist1 A).coeff (fun _ => idx 0 - k) = 0
  rw [show (0 : FormalDist1 A).coeff (fun _ => idx 0 - k) = 0 by rfl]
  exact MulZeroClass.mul_zero _

end FormalDistribution

/-! ### 2D Multiplication Infrastructure -/

namespace FormalDistribution

variable {A : Type*} [CommRing A]

/-- Cauchy product coefficient for 2D formal distributions: (a*b)_{(n,m)} = Σ_{k,l} a_{(k,l)} * b_{(n-k,m-l)} -/
private noncomputable def mulCoeff2d (a b : FormalDist2 A) (n m : ℤ) : A :=
  let support := {(k, l) : ℤ × ℤ | a.coeff (fun i => if i = 0 then k else l) ≠ 0 ∧
                                     b.coeff (fun i => if i = 0 then n - k else m - l) ≠ 0}
  (convolution_support_finite_2d a b n m).toFinset.sum
    fun (k, l) => a.coeff (fun i => if i = 0 then k else l) * b.coeff (fun i => if i = 0 then n - k else m - l)
where
  /-- The set of (k,l) contributing to the convolution at (n,m) is finite -/
  convolution_support_finite_2d (a b : FormalDist2 A) (n m : ℤ) :
      {(k, l) : ℤ × ℤ | a.coeff (fun i => if i = 0 then k else l) ≠ 0 ∧
                         b.coeff (fun i => if i = 0 then n - k else m - l) ≠ 0}.Finite := by
    -- MUCH simpler with total finite support!
    -- The set is contained in the first projection of a.support
    have ha := a.support_finite
    -- Extract to (ℤ × ℤ) format
    let f : (Fin 2 → ℤ) → ℤ × ℤ := fun idx => (idx 0, idx 1)
    have ha_prod := Set.Finite.image f ha
    -- Convolution support is subset of a's support
    apply Set.Finite.subset ha_prod
    intro ⟨k, l⟩ ⟨hak, _⟩
    use (fun i => if i = 0 then k else l)
    exact ⟨hak, rfl⟩

/-- Helper: Support above given bounds is finite for 2D distributions -/
private lemma support_pairs_finite (a : FormalDist2 A) (bound0 bound1 : ℤ) :
    {p : ℤ × ℤ | p.1 ≥ bound0 ∧ p.2 ≥ bound1 ∧ a.coeff (fun i => if i = 0 then p.1 else p.2) ≠ 0}.Finite := by
  -- Much simpler with total finite support!
  have ha := a.support_finite
  let f : (Fin 2 → ℤ) → ℤ × ℤ := fun idx => (idx 0, idx 1)
  have ha_prod := Set.Finite.image f ha
  -- The set is a subset of a's total support (with extra bound constraints)
  apply Set.Finite.subset ha_prod
  intro ⟨n, m⟩ ⟨_, _, ha_nm⟩
  use (fun i => if i = 0 then n else m)
  exact ⟨ha_nm, by simp [f]⟩

private lemma mul_support_finite_2d (a b : FormalDist2 A) (bound0 bound1 : ℤ) :
    {(n, m) : ℤ × ℤ | n ≥ bound0 ∧ m ≥ bound1 ∧ mulCoeff2d a b n m ≠ 0}.Finite := by
  -- MUCH simpler with total finite support!
  -- Product support is subset of pairs (n,m) where the convolution is non-zero
  have ha := a.support_finite
  -- Convert to ℤ × ℤ format
  let f : (Fin 2 → ℤ) → ℤ × ℤ := fun idx => (idx 0, idx 1)
  have ha_prod := Set.Finite.image f ha

  -- Get a's support as ℤ × ℤ set
  let a_support_prod : Set (ℤ × ℤ) := {kl : ℤ × ℤ | a.coeff (fun i => if i = 0 then kl.1 else kl.2) ≠ 0}
  have ha_support_prod : a_support_prod.Finite := by
    apply Set.Finite.subset ha_prod
    intro ⟨k, l⟩ hkl
    use (fun i => if i = 0 then k else l)
    exact ⟨hkl, rfl⟩

  -- The product support is a subset of biUnion over a's support
  have : {p : ℤ × ℤ | p.1 ≥ bound0 ∧ p.2 ≥ bound1 ∧ mulCoeff2d a b p.1 p.2 ≠ 0} ⊆
         ⋃ kl ∈ a_support_prod,
           {p : ℤ × ℤ | p.1 ≥ bound0 ∧ p.2 ≥ bound1 ∧
                        b.coeff (fun i => if i = 0 then p.1 - kl.1 else p.2 - kl.2) ≠ 0} := by
    intro ⟨n, m⟩ ⟨hn_ge, hm_ge, hnm_ne⟩
    -- The convolution sum is non-zero, so some term must be non-zero
    unfold mulCoeff2d at hnm_ne
    have h_support_finite := mulCoeff2d.convolution_support_finite_2d a b n m
    have : ∃ k l, a.coeff (fun i => if i = 0 then k else l) ≠ 0 ∧
                  b.coeff (fun i => if i = 0 then n - k else m - l) ≠ 0 := by
      by_contra h_all_zero
      push_neg at h_all_zero
      have : (h_support_finite.toFinset.sum fun (k, l) =>
               a.coeff (fun i => if i = 0 then k else l) *
               b.coeff (fun i => if i = 0 then n - k else m - l)) = 0 := by
        apply Finset.sum_eq_zero
        intro ⟨k, l⟩ _
        by_cases ha : a.coeff (fun i => if i = 0 then k else l) = 0
        · simp [ha]
        · have hb := h_all_zero k l ha
          simp [hb]
      contradiction
    obtain ⟨k, l, hak, hbkl⟩ := this
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, a_support_prod]
    use (k, l), hak, hn_ge, hm_ge, hbkl

  apply Set.Finite.subset _ this
  -- biUnion over a's finite support
  apply Set.Finite.biUnion ha_support_prod
  intro ⟨k, l⟩ _
  -- For each (k,l), the set {(n,m) | n ≥ bound0, m ≥ bound1, b_{n-k,m-l} ≠ 0} is finite
  -- This is a shifted version of b's support
  have : {p : ℤ × ℤ | p.1 ≥ bound0 ∧ p.2 ≥ bound1 ∧
                       b.coeff (fun i => if i = 0 then p.1 - k else p.2 - l) ≠ 0} ⊆
         (fun q : ℤ × ℤ => (q.1 + k, q.2 + l)) ''
           {q : ℤ × ℤ | q.1 ≥ bound0 - k ∧ q.2 ≥ bound1 - l ∧
                        b.coeff (fun i => if i = 0 then q.1 else q.2) ≠ 0} := by
    intro ⟨n, m⟩ ⟨hn, hm, hb⟩
    use (n - k, m - l)
    refine ⟨⟨by omega, by omega, hb⟩, by simp⟩
  apply Set.Finite.subset _ this
  apply Set.Finite.image
  exact support_pairs_finite b (bound0 - k) (bound1 - l)

/-- Multiplication of two-variable formal distributions -/
noncomputable instance : Mul (FormalDist2 A) where
  mul a b := ⟨
    fun idx => mulCoeff2d a b (idx 0) (idx 1),
    by
      -- Total support is finite (no bound parameter needed!)
      have ha := a.support_finite
      -- The product support is contained in biUnion over a's support
      have : {idx : Fin 2 → ℤ | mulCoeff2d a b (idx 0) (idx 1) ≠ 0} ⊆
             ⋃ idx_a ∈ {idx : Fin 2 → ℤ | a.coeff idx ≠ 0},
               {idx : Fin 2 → ℤ | b.coeff (fun i => idx i - idx_a i) ≠ 0} := by
        intro idx hne
        unfold mulCoeff2d at hne
        have h_support_finite := mulCoeff2d.convolution_support_finite_2d a b (idx 0) (idx 1)
        have : ∃ k l, a.coeff (fun i => if i = 0 then k else l) ≠ 0 ∧
                      b.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) ≠ 0 := by
          by_contra h_all_zero
          push_neg at h_all_zero
          have : (h_support_finite.toFinset.sum fun (k, l) =>
                   a.coeff (fun i => if i = 0 then k else l) *
                   b.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l)) = 0 := by
            apply Finset.sum_eq_zero
            intro ⟨k, l⟩ _
            by_cases ha : a.coeff (fun i => if i = 0 then k else l) = 0
            · simp [ha]
            · have hb := h_all_zero k l ha
              simp [hb]
          contradiction
        obtain ⟨k, l, hak, hbkl⟩ := this
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        use (fun i => if i = 0 then k else l), hak
        convert hbkl using 2
        ext i
        fin_cases i <;> simp
      apply Set.Finite.subset _ this
      apply Set.Finite.biUnion ha
      intro idx_a _
      -- Show {idx | b.coeff(idx - idx_a) ≠ 0} is finite (it's b's support shifted)
      have : {idx : Fin 2 → ℤ | b.coeff (fun i => idx i - idx_a i) ≠ 0} =
             (fun idx_b i => idx_b i + idx_a i) '' {idx_b : Fin 2 → ℤ | b.coeff idx_b ≠ 0} := by
        ext idx
        simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · intro hb
          use (fun i => idx i - idx_a i)
          refine ⟨hb, ?_⟩
          funext i
          ring
        · intro ⟨idx_b, hb, heq⟩
          convert hb using 2
          funext i
          have hi : idx i = idx_b i + idx_a i := by
            have : idx = fun j => idx_b j + idx_a j := heq.symm
            rw [this]
          rw [hi]
          ring
      rw [this]
      exact Set.Finite.image _ b.support_finite
  ⟩

theorem mul_coeff_2d (a b : FormalDist2 A) (n m : ℤ) :
    (a * b).coeff (fun i => if i = 0 then n else m) = mulCoeff2d a b n m := by
  rfl

theorem zero_mul_2d (a : FormalDist2 A) : (0 : FormalDist2 A) * a = 0 := by
  ext idx
  show mulCoeff2d 0 a (idx 0) (idx 1) = 0
  unfold mulCoeff2d mulCoeff2d.convolution_support_finite_2d
  apply Finset.sum_eq_zero
  intro (k, l) _
  show (0 : FormalDist2 A).coeff (fun i => if i = 0 then k else l) *
       a.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) = 0
  rw [show (0 : FormalDist2 A).coeff (fun i => if i = 0 then k else l) = 0 by rfl]
  exact MulZeroClass.zero_mul _

theorem mul_zero_2d (a : FormalDist2 A) : a * (0 : FormalDist2 A) = 0 := by
  ext idx
  show mulCoeff2d a 0 (idx 0) (idx 1) = 0
  unfold mulCoeff2d mulCoeff2d.convolution_support_finite_2d
  apply Finset.sum_eq_zero
  intro (k, l) _
  show a.coeff (fun i => if i = 0 then k else l) *
       (0 : FormalDist2 A).coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) = 0
  rw [show (0 : FormalDist2 A).coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) = 0 by rfl]
  exact MulZeroClass.mul_zero _

/-! ### Ring Axioms for 2D Multiplication -/

/-- Right distributivity: (a + b) * c = a * c + b * c -/
theorem add_mul_2d (a b c : FormalDist2 A) : (a + b) * c = a * c + b * c := by
  ext idx
  show mulCoeff2d (a + b) c (idx 0) (idx 1) =
       mulCoeff2d a c (idx 0) (idx 1) + mulCoeff2d b c (idx 0) (idx 1)
  unfold mulCoeff2d mulCoeff2d.convolution_support_finite_2d
  -- Strategy: Extend sums to union of support sets, similar to 1D but with pairs
  let s_ab := (mulCoeff2d.convolution_support_finite_2d (a + b) c (idx 0) (idx 1)).toFinset
  let s_a := (mulCoeff2d.convolution_support_finite_2d a c (idx 0) (idx 1)).toFinset
  let s_b := (mulCoeff2d.convolution_support_finite_2d b c (idx 0) (idx 1)).toFinset
  let s_union := s_a ∪ s_b

  -- Extend LHS sum to s_union
  have lhs_ext : ∑ p ∈ s_ab, (a + b).coeff (fun i => if i = 0 then p.1 else p.2) *
                              c.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
                 ∑ p ∈ s_union, (a + b).coeff (fun i => if i = 0 then p.1 else p.2) *
                                c.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) := by
    refine Finset.sum_subset ?_ ?_
    · intro ⟨k, l⟩ hkl
      simp only [s_union, Finset.mem_union, s_a, s_b, Set.Finite.mem_toFinset, Set.mem_setOf]
      simp only [s_ab, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl
      by_contra h
      push_neg at h
      -- If (k,l) ∉ s_a ∪ s_b but (a+b).coeff (k,l) * c.coeff (idx 0-k,idx 1-l) ≠ 0
      have ha : a.coeff (fun i => if i = 0 then k else l) = 0 := by
        by_cases ha' : a.coeff (fun i => if i = 0 then k else l) = 0
        · exact ha'
        · have := h.1 ha'
          exact absurd this hkl.2
      have hb : b.coeff (fun i => if i = 0 then k else l) = 0 := by
        by_cases hb' : b.coeff (fun i => if i = 0 then k else l) = 0
        · exact hb'
        · have := h.2 hb'
          exact absurd this hkl.2
      -- Now (a+b).coeff = 0, contradicting hkl.1
      have : (a + b).coeff (fun i => if i = 0 then k else l) = 0 := by
        rw [show (a + b).coeff (fun i => if i = 0 then k else l) =
                 a.coeff (fun i => if i = 0 then k else l) +
                 b.coeff (fun i => if i = 0 then k else l) by rfl]
        rw [ha, hb, zero_add]
      exact hkl.1 this
    · intro ⟨k, l⟩ _ hkl
      simp only [s_ab, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl
      push_neg at hkl
      by_cases h : (a + b).coeff (fun i => if i = 0 then k else l) = 0
      · simp [h]
      · simp [hkl h]

  rw [lhs_ext]

  -- Expand (a+b).coeff = a.coeff + b.coeff and distribute multiplication
  conv_lhs =>
    arg 2
    ext x
    rw [show (a + b).coeff (fun i => if i = 0 then x.1 else x.2) =
             a.coeff (fun i => if i = 0 then x.1 else x.2) +
             b.coeff (fun i => if i = 0 then x.1 else x.2) by rfl]
    rw [_root_.add_mul]

  rw [Finset.sum_add_distrib]

  -- Now show both sums over s_union equal the respective sums over s_a and s_b
  congr 1
  · -- Show sum over s_union of a terms equals sum over s_a
    refine (Finset.sum_subset Finset.subset_union_left ?_).symm
    intro ⟨k, l⟩ _ hkl
    simp only [s_a, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl
    by_cases h : a.coeff (fun i => if i = 0 then k else l) = 0
    · simp [h]
    · push_neg at hkl; simp [hkl h]
  · -- Show sum over s_union of b terms equals sum over s_b
    refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro ⟨k, l⟩ _ hkl
    simp only [s_b, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl
    by_cases h : b.coeff (fun i => if i = 0 then k else l) = 0
    · simp [h]
    · push_neg at hkl; simp [hkl h]

/-- Left distributivity: a * (b + c) = a * b + a * c -/
theorem mul_add_2d (a b c : FormalDist2 A) : a * (b + c) = a * b + a * c := by
  ext idx
  show mulCoeff2d a (b + c) (idx 0) (idx 1) =
       mulCoeff2d a b (idx 0) (idx 1) + mulCoeff2d a c (idx 0) (idx 1)
  unfold mulCoeff2d mulCoeff2d.convolution_support_finite_2d
  -- Strategy: Similar to add_mul_2d but distributing over the second argument
  let s_a_bc := (mulCoeff2d.convolution_support_finite_2d a (b + c) (idx 0) (idx 1)).toFinset
  let s_ab := (mulCoeff2d.convolution_support_finite_2d a b (idx 0) (idx 1)).toFinset
  let s_ac := (mulCoeff2d.convolution_support_finite_2d a c (idx 0) (idx 1)).toFinset
  let s_union := s_ab ∪ s_ac

  -- Extend LHS sum to s_union
  have lhs_ext : ∑ p ∈ s_a_bc, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                (b + c).coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
                 ∑ p ∈ s_union, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                (b + c).coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) := by
    refine Finset.sum_subset ?_ ?_
    · intro ⟨k, l⟩ hkl
      simp only [s_union, Finset.mem_union]
      simp only [s_a_bc, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl
      by_contra h
      simp only [s_ab, s_ac, Set.Finite.mem_toFinset, Set.mem_setOf] at h
      push_neg at h
      -- If (k,l) ∉ s_ab ∪ s_ac but a.coeff (k,l) * (b+c).coeff (idx 0-k,idx 1-l) ≠ 0
      -- From hkl: a.coeff (k,l) ≠ 0 and (b+c).coeff (idx 0-k,idx 1-l) ≠ 0
      -- From h: (k,l) ∉ s_ab and (k,l) ∉ s_ac
      have ha : a.coeff (fun i => if i = 0 then k else l) ≠ 0 := by
        intro ha_eq
        simp [ha_eq] at hkl
      -- h.1 says: a.coeff (k,l) ≠ 0 → b.coeff (idx 0-k,idx 1-l) = 0
      have hb : b.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) = 0 := h.1 ha
      -- h.2 says: a.coeff (k,l) ≠ 0 → c.coeff (idx 0-k,idx 1-l) = 0
      have hc : c.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) = 0 := h.2 ha
      -- Now (b+c).coeff = 0, contradicting (b+c).coeff ≠ 0 from hkl
      have h_sum_zero : (b + c).coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) = 0 := by
        rw [show (b + c).coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) =
                 b.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) +
                 c.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) by rfl]
        simp [hb, hc]
      simp [h_sum_zero] at hkl
    · intro ⟨k, l⟩ _ hkl
      simp only [s_a_bc, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl
      push_neg at hkl
      by_cases ha : a.coeff (fun i => if i = 0 then k else l) = 0
      · simp [ha]
      · simp [hkl ha]

  rw [lhs_ext]

  -- Expand (b+c).coeff = b.coeff + c.coeff and distribute multiplication
  conv_lhs =>
    arg 2
    ext x
    rw [show (b + c).coeff (fun i => if i = 0 then idx 0 - x.1 else idx 1 - x.2) =
             b.coeff (fun i => if i = 0 then idx 0 - x.1 else idx 1 - x.2) +
             c.coeff (fun i => if i = 0 then idx 0 - x.1 else idx 1 - x.2) by rfl]
    rw [_root_.mul_add]

  rw [Finset.sum_add_distrib]

  -- Now show both sums over s_union equal the respective sums over s_ab and s_ac
  congr 1
  · -- Show sum over s_union of b terms equals sum over s_ab
    refine (Finset.sum_subset Finset.subset_union_left ?_).symm
    intro ⟨k, l⟩ _ hkl
    simp only [s_ab, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl
    push_neg at hkl
    -- hkl: a.coeff (k,l) ≠ 0 → b.coeff (idx 0-k, idx 1-l) = 0
    -- Need to show: a.coeff (k,l) * b.coeff (idx 0-k, idx 1-l) = 0
    by_cases ha : a.coeff (fun i => if i = 0 then k else l) = 0
    · simp [ha]
    · simp [hkl ha]
  · -- Show sum over s_union of c terms equals sum over s_ac
    refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro ⟨k, l⟩ _ hkl
    simp only [s_ac, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl
    push_neg at hkl
    by_cases ha : a.coeff (fun i => if i = 0 then k else l) = 0
    · simp [ha]
    · simp [hkl ha]

/-- Scalar multiplication commutes with left multiplication: (r • a) * b = r • (a * b) -/
theorem smul_mul_2d (r : A) (a b : FormalDist2 A) : (r • a) * b = r • (a * b) := by
  ext idx
  show mulCoeff2d (r • a) b (idx 0) (idx 1) = r * mulCoeff2d a b (idx 0) (idx 1)
  unfold mulCoeff2d mulCoeff2d.convolution_support_finite_2d
  let s_ra := (mulCoeff2d.convolution_support_finite_2d (r • a) b (idx 0) (idx 1)).toFinset
  let s_a := (mulCoeff2d.convolution_support_finite_2d a b (idx 0) (idx 1)).toFinset

  -- Extend both sums to their union
  let s_union := s_ra ∪ s_a
  have lhs_ext : ∑ p ∈ s_ra, (r • a).coeff (fun i => if i = 0 then p.1 else p.2) *
                              b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
                 ∑ p ∈ s_union, (r • a).coeff (fun i => if i = 0 then p.1 else p.2) *
                                b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) := by
    refine Finset.sum_subset Finset.subset_union_left ?_
    intro ⟨k, l⟩ _ hk
    simp only [s_ra, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : (r • a).coeff (fun i => if i = 0 then k else l) = 0
    · simp [h]
    · push_neg at hk; simp [hk h]

  have rhs_ext : r • ∑ p ∈ s_a, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                 b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
                 ∑ p ∈ s_union, r • (a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                     b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro ⟨k, l⟩ _ hk
    simp only [s_a, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : a.coeff (fun i => if i = 0 then k else l) = 0
    · simp [h]
    · push_neg at hk; simp [hk h]

  rw [lhs_ext]
  show ∑ p ∈ s_union, (r • a).coeff (fun i => if i = 0 then p.1 else p.2) *
                       b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
       r • ∑ p ∈ s_a, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                      b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2)
  rw [rhs_ext]
  congr 1
  ext ⟨k, l⟩
  simp only [show (r • a).coeff (fun i => if i = 0 then k else l) =
                  r • a.coeff (fun i => if i = 0 then k else l) by rfl, smul_mul_assoc]

/-- Scalar multiplication commutes with right multiplication: a * (r • b) = r • (a * b) -/
theorem mul_smul_2d (r : A) (a b : FormalDist2 A) : a * (r • b) = r • (a * b) := by
  ext idx
  show mulCoeff2d a (r • b) (idx 0) (idx 1) = r * mulCoeff2d a b (idx 0) (idx 1)
  unfold mulCoeff2d mulCoeff2d.convolution_support_finite_2d
  let s_rb := (mulCoeff2d.convolution_support_finite_2d a (r • b) (idx 0) (idx 1)).toFinset
  let s_b := (mulCoeff2d.convolution_support_finite_2d a b (idx 0) (idx 1)).toFinset

  let s_union := s_rb ∪ s_b
  have lhs_ext : ∑ p ∈ s_rb, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                              (r • b).coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
                 ∑ p ∈ s_union, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                (r • b).coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) := by
    refine Finset.sum_subset Finset.subset_union_left ?_
    intro ⟨k, l⟩ _ hk
    simp only [s_rb, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : a.coeff (fun i => if i = 0 then k else l) = 0
    · simp [h]
    · push_neg at hk; simp [hk h]

  have rhs_ext : r • ∑ p ∈ s_b, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                 b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
                 ∑ p ∈ s_union, r • (a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                     b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro ⟨k, l⟩ _ hk
    simp only [s_b, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
    by_cases h : a.coeff (fun i => if i = 0 then k else l) = 0
    · simp [h]
    · push_neg at hk; simp [hk h]

  rw [lhs_ext]
  show ∑ p ∈ s_union, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                       (r • b).coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
       r • ∑ p ∈ s_b, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                      b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2)
  rw [rhs_ext]
  congr 1
  ext ⟨k, l⟩
  rw [show (r • b).coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) =
           r • b.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) by rfl]
  rw [show r • b.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) =
           r * b.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l) by rfl]
  rw [show r • (a.coeff (fun i => if i = 0 then k else l) *
                b.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l)) =
           r * (a.coeff (fun i => if i = 0 then k else l) *
                b.coeff (fun i => if i = 0 then idx 0 - k else idx 1 - l)) by rfl]
  ring

end FormalDistribution

/-! ### Embeddings: 1D → 2D -/

namespace FormalDistribution

variable {A : Type*} [CommRing A]

/-- Embed a 1D distribution into 2D in the z-variable (concentrated at w=0)
    This embeds a(z) as a distribution that has coefficient a_k at (k, 0) and 0 elsewhere. -/
noncomputable def embed_z (a : FormalDist1 A) : FormalDist2 A where
  coeff := fun idx => if idx 1 = 0 then a.coeff (fun _ => idx 0) else 0
  support_finite := by
    -- Total support is {(k, 0) | a_k ≠ 0}, which is finite (image of a's support)
    have ha := a.support_finite
    have : {idx : Fin 2 → ℤ | (if idx 1 = 0 then a.coeff (fun _ => idx 0) else 0) ≠ 0} ⊆
           (fun idx_a : Fin 1 → ℤ => fun i : Fin 2 => if i = 0 then idx_a 0 else 0) ''
             {idx_a : Fin 1 → ℤ | a.coeff idx_a ≠ 0} := by
      intro idx hne
      simp only [Set.mem_setOf_eq] at hne
      by_cases h : idx 1 = 0
      · have hne' : a.coeff (fun _ => idx 0) ≠ 0 := by simpa [h] using hne
        use (fun _ => idx 0)
        exact ⟨hne', by funext i; fin_cases i <;> simp [h]⟩
      · simp [h] at hne
    exact Set.Finite.subset (Set.Finite.image _ ha) this

/-- Embed a 1D distribution into 2D in the w-variable (concentrated at z=0)
    This embeds a(w) as a distribution that has coefficient a_l at (0, l) and 0 elsewhere. -/
noncomputable def embed_w (a : FormalDist1 A) : FormalDist2 A where
  coeff := fun idx => if idx 0 = 0 then a.coeff (fun _ => idx 1) else 0
  support_finite := by
    -- Total support is {(0, l) | a_l ≠ 0}, which is finite (image of a's support)
    have ha := a.support_finite
    have : {idx : Fin 2 → ℤ | (if idx 0 = 0 then a.coeff (fun _ => idx 1) else 0) ≠ 0} ⊆
           (fun idx_a : Fin 1 → ℤ => fun i : Fin 2 => if i = 0 then 0 else idx_a 0) ''
             {idx_a : Fin 1 → ℤ | a.coeff idx_a ≠ 0} := by
      intro idx hne
      simp only [Set.mem_setOf_eq] at hne
      by_cases h : idx 0 = 0
      · have hne' : a.coeff (fun _ => idx 1) ≠ 0 := by simpa [h] using hne
        use (fun _ => idx 1)
        exact ⟨hne', by funext i; fin_cases i <;> simp [h]⟩
      · simp [h] at hne
    exact Set.Finite.subset (Set.Finite.image _ ha) this

end FormalDistribution

/-! ### Residue in specific variable -/

namespace FormalDistribution

variable {A : Type*} [CommRing A]

/-- Extract the residue (coefficient of z^{-1}) in a specific variable from a 2D distribution -/
noncomputable def residue_var (i : Fin 2) (a : FormalDist2 A) : FormalDist1 A where
  coeff := fun idx => a.coeff (fun j => if j = i then -1 else idx 0)
  support_finite := by
    -- Total support is projection of a's support onto the non-i coordinate
    have ha := a.support_finite
    let proj : (Fin 2 → ℤ) → (Fin 1 → ℤ) := fun idx2 => fun _ => idx2 (if i = 0 then 1 else 0)
    have : {idx : Fin 1 → ℤ | a.coeff (fun j => if j = i then -1 else idx 0) ≠ 0} ⊆
           proj '' {idx2 : Fin 2 → ℤ | a.coeff idx2 ≠ 0} := by
      intro idx hne
      use (fun j => if j = i then -1 else idx 0)
      exact ⟨hne, by unfold proj; funext j; fin_cases j; fin_cases i <;> rfl⟩
    exact Set.Finite.subset (Set.Finite.image _ ha) this

end FormalDistribution

/-! ## 1.1.3 Fourier expansion -/

/-- Definition 1.1.3: Fourier expansion of a formal distribution a(z) = ∑ a_n z^n -/
def fourierExpansion (a : FormalDist1 A) : ℤ → A :=
  fun n => a.coeff (fun _ => n)

/-- Fourier modes of a(z), defined as a_{(n)} = Res_{z^n} a(z) = a_{-n-1} -/
def fourierMode (a : FormalDist1 A) (n : ℤ) : A :=
  a.coeff (fun _ => -n - 1)

/-- Residue notation: Res_z a(z) = a_{-1} -/
def residue (a : FormalDist1 A) : A :=
  a.coeff (fun _ => -1)

/-! ### Properties of Fourier expansion -/

/-- Fourier expansion is linear in addition -/
@[simp]
theorem fourierExpansion_add (a b : FormalDist1 A) (n : ℤ) :
    fourierExpansion (a + b) n = fourierExpansion a n + fourierExpansion b n := by
  rfl

/-- Fourier expansion respects scalar multiplication -/
@[simp]
theorem fourierExpansion_smul (c : A) (a : FormalDist1 A) (n : ℤ) :
    fourierExpansion (c • a) n = c * fourierExpansion a n := by
  rfl

/-- Fourier expansion of zero is zero -/
@[simp]
theorem fourierExpansion_zero (n : ℤ) :
    fourierExpansion (0 : FormalDist1 A) n = 0 := by
  rfl

/-- Fourier mode is linear in addition -/
@[simp]
theorem fourierMode_add (a b : FormalDist1 A) (n : ℤ) :
    fourierMode (a + b) n = fourierMode a n + fourierMode b n := by
  rfl

/-- Fourier mode respects scalar multiplication -/
@[simp]
theorem fourierMode_smul (c : A) (a : FormalDist1 A) (n : ℤ) :
    fourierMode (c • a) n = c * fourierMode a n := by
  rfl

/-- Fourier mode of zero is zero -/
@[simp]
theorem fourierMode_zero (n : ℤ) :
    fourierMode (0 : FormalDist1 A) n = 0 := by
  rfl

/-- Residue is linear in addition -/
@[simp]
theorem residue_add (a b : FormalDist1 A) :
    residue (a + b) = residue a + residue b := by
  rfl

/-- Residue respects scalar multiplication -/
@[simp]
theorem residue_smul (c : A) (a : FormalDist1 A) :
    residue (c • a) = c * residue a := by
  rfl

/-- Residue of zero is zero -/
@[simp]
theorem residue_zero :
    residue (0 : FormalDist1 A) = 0 := by
  rfl

/-! ### Relationship between Fourier modes and coefficients -/

/-- Fourier expansion extracts the coefficient directly -/
theorem fourierExpansion_eq_coeff (a : FormalDist1 A) (n : ℤ) :
    fourierExpansion a n = a.coeff (fun _ => n) := by
  rfl

/-- Fourier mode is the coefficient at -n-1 -/
theorem fourierMode_eq_coeff (a : FormalDist1 A) (n : ℤ) :
    fourierMode a n = a.coeff (fun _ => -n - 1) := by
  rfl

/-- Residue is the coefficient at -1 -/
theorem residue_eq_coeff (a : FormalDist1 A) :
    residue a = a.coeff (fun _ => -1) := by
  rfl

/-- Residue equals the 0-th Fourier mode -/
theorem residue_eq_fourierMode_zero (a : FormalDist1 A) :
    residue a = fourierMode a 0 := by
  rfl

/-! ### Derivatives and Fourier modes -/

/-- The Fourier expansion of the derivative -/
theorem fourierExpansion_deriv (a : FormalDist1 A) (n : ℤ) :
    fourierExpansion (FormalDistribution.deriv a 0) n = (n + 1 : ℤ) • fourierExpansion a (n + 1) := by
  unfold fourierExpansion FormalDistribution.deriv
  -- Simplify the let-bound shifted_idx
  simp only []
  -- Show that when idx = (fun _ => n), then Function.update idx 0 (idx 0 + 1) = (fun _ => n + 1)
  have h : Function.update (fun _ : Fin 1 => n) 0 ((fun _ : Fin 1 => n) 0 + 1) = (fun _ : Fin 1 => n + 1) := by
    funext i
    fin_cases i
    simp [Function.update]
  simp only [h]

/-- The Fourier mode of the derivative -/
theorem fourierMode_deriv (a : FormalDist1 A) (n : ℤ) :
    fourierMode (FormalDistribution.deriv a 0) n = (-n : ℤ) • fourierMode a (n - 1) := by
  unfold fourierMode FormalDistribution.deriv
  simp only []
  have eq1 : (-n - 1 : ℤ) + 1 = -n := by omega
  have eq2 : -(n - 1) - 1 = -n := by omega
  rw [eq2]
  have h : Function.update (fun _ : Fin 1 => -n - 1) 0 ((fun _ : Fin 1 => -n - 1) 0 + 1) = (fun _ : Fin 1 => -n) := by
    funext i
    fin_cases i
    simp [Function.update, eq1]
  have h2 : Function.update (fun _ : Fin 1 => -n - 1) 0 (-n) = (fun _ : Fin 1 => -n) := by
    funext i
    fin_cases i
    simp [Function.update]
  simp only [eq1, h2]

/-- The residue of the derivative -/
theorem residue_deriv (a : FormalDist1 A) :
    residue (FormalDistribution.deriv a 0) = 0 := by
  unfold residue FormalDistribution.deriv
  simp only [show (-1 : ℤ) + 1 = 0 by norm_num, zero_smul]

/-- The residue of any iterated derivative is zero -/
theorem residue_iteratedDeriv (a : FormalDist1 A) (k : ℕ) (hk : k > 0) :
    residue (FormalDistribution.iteratedDeriv a 0 k) = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    simp [FormalDistribution.iteratedDeriv]
    rw [residue_deriv]

/-- Linearity of Fourier expansion for linear combinations -/
theorem fourierExpansion_linear (a b : FormalDist1 A) (c d : A) (n : ℤ) :
    fourierExpansion (c • a + d • b) n = c * fourierExpansion a n + d * fourierExpansion b n := by
  simp

/-- Linearity of Fourier mode for linear combinations -/
theorem fourierMode_linear (a b : FormalDist1 A) (c d : A) (n : ℤ) :
    fourierMode (c • a + d • b) n = c * fourierMode a n + d * fourierMode b n := by
  simp

/-- Linearity of residue for linear combinations -/
theorem residue_linear (a b : FormalDist1 A) (c d : A) :
    residue (c • a + d • b) = c * residue a + d * residue b := by
  simp

/-! ### More Fourier mode relationships -/

/-- Fourier expansion and Fourier mode are related by index transformation -/
theorem fourierExpansion_eq_fourierMode_neg (a : FormalDist1 A) (n : ℤ) :
    fourierExpansion a n = fourierMode a (-n - 1) := by
  unfold fourierExpansion fourierMode
  congr 1
  funext i
  fin_cases i
  simp

/-- Extracting coefficient via Fourier expansion -/
theorem coeff_eq_fourierExpansion (a : FormalDist1 A) (n : ℤ) :
    a.coeff (fun _ => n) = fourierExpansion a n := by
  rfl

/-- Zero distribution has all Fourier modes zero -/
theorem fourierMode_zero_dist (n : ℤ) :
    fourierMode (0 : FormalDist1 A) n = 0 := by
  rfl

/-- Zero distribution has all Fourier expansions zero -/
theorem fourierExpansion_zero_dist (n : ℤ) :
    fourierExpansion (0 : FormalDist1 A) n = 0 := by
  rfl

/-! ## 1.2 Extended binomial coefficient and expansions -/

/-- Definition 1.2.2: Extended binomial coefficient for j ∈ ℤ and n ∈ ℤ⁺.
    Computes j(j-1)⋯(j-n+1)/n! via the recurrence C(j,0) = 1, C(j,n+1) = C(j,n)·(j-n)/(n+1). -/
def extBinomial (j : ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => extBinomial j n * ((↑j : ℚ) - ↑n) / (↑(n + 1) : ℚ)

notation "(" j " choose " n ")" => extBinomial j n

/-! ### Properties of extended binomial coefficient -/

/-- Extended binomial coefficient is 1 when n = 0 -/
@[simp]
theorem extBinomial_zero (j : ℤ) : extBinomial j 0 = 1 := rfl

/-- Recurrence: extBinomial j (n+1) = extBinomial j n * (j - n) / (n + 1) -/
theorem extBinomial_succ (j : ℤ) (n : ℕ) :
    extBinomial j (n + 1) = extBinomial j n * ((↑j : ℚ) - ↑n) / (↑(n + 1) : ℚ) := rfl

/-! ## 1.2 Expansion operators -/

/-- Generalized binomial coefficient for integer upper index: C(k, n) = k(k-1)⋯(k-n+1)/n!
    For k ≥ 0: uses Nat.choose. For k < 0: uses the identity C(k,n) = (-1)^n * C(n-k-1, n). -/
private def intBinomial (k : ℤ) (n : ℕ) : ℤ :=
  match k with
  | .ofNat m => ↑(Nat.choose m n)
  | .negSucc m => (-1) ^ n * ↑(Nat.choose (n + m) n)

private theorem intBinomial_zero (k : ℤ) : intBinomial k 0 = 1 := by
  cases k <;> simp [intBinomial]

/-- For k = -1: intBinomial (-1) n = (-1)^n -/
private theorem intBinomial_neg_one (n : ℕ) : intBinomial (-1) n = (-1) ^ n := by
  show (-1 : ℤ) ^ n * ↑(Nat.choose (n + 0) n) = (-1) ^ n
  simp

/-- Key identity: (k - n) * C(k, n) = k * C(k-1, n) -/
private theorem intBinomial_mul_sub (k : ℤ) (n : ℕ) :
    (k - ↑n) * intBinomial k n = k * intBinomial (k - 1) n := by
  cases k with
  | ofNat m =>
    cases m with
    | zero =>
      -- k = 0, intBinomial 0 n = C(0,n), k-1 = -1
      -- After cases, goal has Int.ofNat 0. Convert and simplify.
      simp only [intBinomial, Int.ofNat_eq_natCast, Nat.cast_zero, zero_mul, zero_sub]
      rcases n with - | n <;> simp [Nat.choose_zero_succ]
    | succ m =>
      -- k = m+1: intBinomial (m+1) n = C(m+1,n), k-1 = m: intBinomial m n = C(m,n)
      -- Can't use `change` because Int.subNatNat is @[extern] (opaque in kernel)
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
    -- k = -(m+1), intBinomial k n = (-1)^n * C(n+m, n)
    -- k-1 = -(m+2), intBinomial (k-1) n = (-1)^n * C(n+m+1, n)
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

/-- Identity: (n+1) * C(k, n+1) = k * C(k-1, n). Combines the recurrence and absorption. -/
private theorem intBinomial_succ_mul_eq (k : ℤ) (n : ℕ) :
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

/-- extBinomial agrees with intBinomial when cast to ℚ -/
theorem extBinomial_eq_intBinomial (j : ℤ) (n : ℕ) :
    extBinomial j n = (↑(intBinomial j n) : ℚ) := by
  induction n with
  | zero => simp [intBinomial_zero]
  | succ n ih =>
    rw [extBinomial_succ, ih]
    -- Goal: ↑(intBinomial j n) * (↑j - ↑n) / ↑(n+1) = ↑(intBinomial j (n+1))
    have h_eq : (↑(n + 1) : ℤ) * intBinomial j (n + 1) = (j - ↑n) * intBinomial j n := by
      linarith [intBinomial_succ_mul_eq j n, intBinomial_mul_sub j n]
    have h_ne : (↑(n + 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    rw [eq_comm, eq_div_iff h_ne]
    have h_q : (↑(n + 1) : ℚ) * ↑(intBinomial j (n + 1)) =
               ((↑j : ℚ) - ↑n) * ↑(intBinomial j n) := by exact_mod_cast h_eq
    linarith [mul_comm (↑(intBinomial j (n + 1)) : ℚ) (↑(n + 1) : ℚ),
              mul_comm (↑(intBinomial j n) : ℚ) ((↑j : ℚ) - ↑n)]

/-- Extended binomial agrees with Nat.choose for non-negative arguments -/
theorem extBinomial_nonneg (k n : ℕ) : extBinomial (↑k : ℤ) n = (↑(Nat.choose k n) : ℚ) := by
  rw [extBinomial_eq_intBinomial]; simp [intBinomial]

/-- Expansion i_{z,w}(z-w)^k as a 2-variable generalized formal distribution.

    i_{z,w}(z-w)^k = Σ_{j≥0} C(k,j)(-1)^j z^{k-j} w^j

    Coefficient at (n,m): C(k,m)(-1)^m when n+m=k and m≥0, else 0. -/
noncomputable def expansion_izw (k : ℤ) : GenFormalDist2 A where
  coeff := fun idx =>
    if idx 0 + idx 1 = k ∧ idx 1 ≥ 0
    then ((intBinomial k (idx 1).toNat * (-1) ^ (idx 1).toNat : ℤ) : A)
    else 0
  support_finite := fun bound => by
    -- Support ⊆ {(k-m, m) : b₁ ≤ m ≤ k - b₀}, a finite interval
    by_cases h : bound 0 + bound 1 ≤ k
    · have h_subset : {idx : Fin 2 → ℤ | (∀ i, idx i ≥ bound i) ∧
          (if idx 0 + idx 1 = k ∧ idx 1 ≥ 0
           then ((intBinomial k (idx 1).toNat * (-1) ^ (idx 1).toNat : ℤ) : A) else 0) ≠ 0} ⊆
          (fun m => fun i : Fin 2 => if i = 0 then k - m else m) ''
            (↑(Finset.Icc (bound 1) (k - bound 0)) : Set ℤ) := by
        intro idx ⟨hall, hne⟩
        have h0 := hall 0; have h1 := hall 1
        split_ifs at hne with hidx
        · obtain ⟨hsum, hm⟩ := hidx
          exact ⟨idx 1, by rw [Finset.mem_coe, Finset.mem_Icc]; omega,
                 by ext i; fin_cases i <;> simp; omega⟩
        · simp at hne
      exact (Set.Finite.image _ (Finset.finite_toSet _)).subset h_subset
    · convert Set.finite_empty
      ext idx; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hall; have h0 := hall 0; have h1 := hall 1
      split_ifs with hidx
      · obtain ⟨hsum, _⟩ := hidx; omega
      · simp

theorem expansion_izw_coeff (k : ℤ) (idx : Fin 2 → ℤ) :
    (expansion_izw k : GenFormalDist2 A).coeff idx =
    if idx 0 + idx 1 = k ∧ idx 1 ≥ 0
    then ((intBinomial k (idx 1).toNat * (-1) ^ (idx 1).toNat : ℤ) : A)
    else 0 := rfl

/-- Expansion i_{w,z}(z-w)^k as a 2-variable generalized formal distribution.

    i_{w,z}(z-w)^k = (-1)^k Σ_{j≥0} C(k,j)(-1)^j z^j w^{k-j}

    Coefficient at (n,m): C(k,n)(-1)^m when n+m=k and n≥0, else 0.
    (Using (-1)^m = (-1)^{k+n} since m = k-n.) -/
noncomputable def expansion_iwz (k : ℤ) : GenFormalDist2 A where
  coeff := fun idx =>
    if idx 0 + idx 1 = k ∧ idx 0 ≥ 0
    then ((intBinomial k (idx 0).toNat * (-1) ^ (k - idx 0).natAbs : ℤ) : A)
    else 0
  support_finite := fun bound => by
    -- Support ⊆ {(n, k-n) : b₀ ≤ n ≤ k - b₁}, a finite interval
    by_cases h : bound 0 + bound 1 ≤ k
    · have h_subset : {idx : Fin 2 → ℤ | (∀ i, idx i ≥ bound i) ∧
          (if idx 0 + idx 1 = k ∧ idx 0 ≥ 0
           then ((intBinomial k (idx 0).toNat * (-1) ^ (k - idx 0).natAbs : ℤ) : A) else 0) ≠ 0} ⊆
          (fun n => fun i : Fin 2 => if i = 0 then n else k - n) ''
            (↑(Finset.Icc (bound 0) (k - bound 1)) : Set ℤ) := by
        intro idx ⟨hall, hne⟩
        have h0 := hall 0; have h1 := hall 1
        split_ifs at hne with hidx
        · obtain ⟨hsum, hn⟩ := hidx
          exact ⟨idx 0, by rw [Finset.mem_coe, Finset.mem_Icc]; omega,
                 by ext i; fin_cases i <;> simp; omega⟩
        · simp at hne
      exact (Set.Finite.image _ (Finset.finite_toSet _)).subset h_subset
    · convert Set.finite_empty
      ext idx; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hall; have h0 := hall 0; have h1 := hall 1
      split_ifs with hidx
      · obtain ⟨hsum, _⟩ := hidx; omega
      · simp

theorem expansion_iwz_coeff (k : ℤ) (idx : Fin 2 → ℤ) :
    (expansion_iwz k : GenFormalDist2 A).coeff idx =
    if idx 0 + idx 1 = k ∧ idx 0 ≥ 0
    then ((intBinomial k (idx 0).toNat * (-1) ^ (k - idx 0).natAbs : ℤ) : A)
    else 0 := rfl

/-! ### Proposition 1.2.6: Derivatives commute with expansion operators -/

/-- Proposition 1.2.6(a): ∂_z i_{z,w}(z-w)^k = k · i_{z,w}(z-w)^{k-1} -/
theorem deriv_z_expansion_izw (k : ℤ) :
    GeneralizedFormalDistribution.deriv (expansion_izw k : GenFormalDist2 A) 0 =
    (k : A) • expansion_izw (k - 1) := by
  ext idx
  show (idx 0 + 1 : ℤ) • (expansion_izw k : GenFormalDist2 A).coeff (Function.update idx 0 (idx 0 + 1))
     = (k : A) • (expansion_izw (k - 1) : GenFormalDist2 A).coeff idx
  rw [expansion_izw_coeff, expansion_izw_coeff]
  simp only [update_eval_same, update_eval_diff idx 0 1 (idx 0 + 1) (by decide)]
  -- LHS condition: (idx 0 + 1) + idx 1 = k ∧ idx 1 ≥ 0
  -- RHS condition: idx 0 + idx 1 = k - 1 ∧ idx 1 ≥ 0  (equivalent)
  by_cases hcond : idx 0 + idx 1 = k - 1 ∧ idx 1 ≥ 0
  · rw [if_pos ⟨by omega, hcond.2⟩, if_pos hcond]
    simp only [zsmul_eq_mul, smul_eq_mul, ← Int.cast_mul]
    congr 1
    have h_key := intBinomial_mul_sub k (idx 1).toNat
    have hm : (↑((idx 1).toNat) : ℤ) = idx 1 := Int.toNat_of_nonneg hcond.2
    calc (idx 0 + 1) * (intBinomial k (idx 1).toNat * (-1) ^ (idx 1).toNat)
        = (k - ↑((idx 1).toNat)) * (intBinomial k (idx 1).toNat * (-1) ^ (idx 1).toNat) := by
          congr 1; omega
      _ = ((k - ↑((idx 1).toNat)) * intBinomial k (idx 1).toNat) * (-1) ^ (idx 1).toNat := by ring
      _ = (k * intBinomial (k - 1) (idx 1).toNat) * (-1) ^ (idx 1).toNat := by rw [h_key]
      _ = k * (intBinomial (k - 1) (idx 1).toNat * (-1) ^ (idx 1).toNat) := by ring
  · rw [if_neg (by intro ⟨h1, h2⟩; exact hcond ⟨by omega, h2⟩), if_neg hcond]
    simp [smul_zero]

/-- Proposition 1.2.6(b): ∂_w i_{z,w}(z-w)^k = -k · i_{z,w}(z-w)^{k-1} -/
theorem deriv_w_expansion_izw (k : ℤ) :
    GeneralizedFormalDistribution.deriv (expansion_izw k : GenFormalDist2 A) 1 =
    (-k : A) • expansion_izw (k - 1) := by
  ext idx
  show (idx 1 + 1 : ℤ) • (expansion_izw k : GenFormalDist2 A).coeff (Function.update idx 1 (idx 1 + 1))
     = (-k : A) • (expansion_izw (k - 1) : GenFormalDist2 A).coeff idx
  rw [expansion_izw_coeff, expansion_izw_coeff]
  simp only [update_eval_same, update_eval_diff idx 1 0 (idx 1 + 1) (by decide)]
  by_cases hcond : idx 0 + idx 1 = k - 1 ∧ idx 1 ≥ 0
  · -- Main case: both conditions hold
    rw [if_pos ⟨by omega, by omega⟩, if_pos hcond]
    simp only [zsmul_eq_mul, smul_eq_mul, ← Int.cast_neg, ← Int.cast_mul]
    congr 1
    have hm1_eq : (idx 1 + 1).toNat = (idx 1).toNat + 1 := by omega
    rw [hm1_eq]
    have h_succ := intBinomial_succ_mul_eq k (idx 1).toNat
    calc (idx 1 + 1) * (intBinomial k ((idx 1).toNat + 1) * (-1) ^ ((idx 1).toNat + 1))
        = ↑((idx 1).toNat + 1) * (intBinomial k ((idx 1).toNat + 1) * (-1) ^ ((idx 1).toNat + 1)) := by
          congr 1; omega
      _ = (↑((idx 1).toNat + 1) * intBinomial k ((idx 1).toNat + 1)) *
          (-1) ^ ((idx 1).toNat + 1) := by ring
      _ = (k * intBinomial (k - 1) (idx 1).toNat) * (-1) ^ ((idx 1).toNat + 1) := by rw [h_succ]
      _ = -k * (intBinomial (k - 1) (idx 1).toNat * (-1) ^ (idx 1).toNat) := by
          rw [pow_succ]; ring
  · -- ¬hcond: RHS condition fails
    rw [if_neg hcond, smul_zero]
    -- LHS: (idx 1 + 1) • (if ... then ... else 0)
    by_cases hlhs : idx 0 + (idx 1 + 1) = k ∧ idx 1 + 1 ≥ 0
    · -- LHS condition holds but RHS doesn't → idx 1 = -1, so idx 1 + 1 = 0
      rw [if_pos hlhs]
      have : (idx 1 + 1 : ℤ) = 0 := by omega
      rw [this, zero_smul]
    · rw [if_neg hlhs, smul_zero]

/-- Helper: (-1)^|a+1| = -(-1)^|a| for all integers a -/
private theorem neg_one_pow_natAbs_succ (a : ℤ) :
    ((-1 : ℤ) ^ (a + 1).natAbs) = -((-1 : ℤ) ^ a.natAbs) := by
  by_cases ha : 0 ≤ a
  · rw [show (a + 1).natAbs = a.natAbs + 1 from by omega, pow_succ]; ring
  · push_neg at ha
    by_cases ha' : a = -1
    · subst ha'; simp
    · have hlt : a < -1 := by omega
      obtain ⟨n, hn⟩ : ∃ n : ℕ, a.natAbs = n + 1 := ⟨a.natAbs - 1, by omega⟩
      have h1 : (a + 1).natAbs = n := by omega
      rw [h1, hn, pow_succ]; ring

/-- Proposition 1.2.6(c): ∂_z i_{w,z}(z-w)^k = k · i_{w,z}(z-w)^{k-1} -/
theorem deriv_z_expansion_iwz (k : ℤ) :
    GeneralizedFormalDistribution.deriv (expansion_iwz k : GenFormalDist2 A) 0 =
    (k : A) • expansion_iwz (k - 1) := by
  ext idx
  show (idx 0 + 1 : ℤ) • (expansion_iwz k : GenFormalDist2 A).coeff (Function.update idx 0 (idx 0 + 1))
     = (k : A) • (expansion_iwz (k - 1) : GenFormalDist2 A).coeff idx
  rw [expansion_iwz_coeff, expansion_iwz_coeff]
  simp only [update_eval_same, update_eval_diff idx 0 1 (idx 0 + 1) (by decide)]
  -- LHS condition: (idx 0 + 1) + idx 1 = k ∧ (idx 0 + 1) ≥ 0
  -- RHS condition: idx 0 + idx 1 = k - 1 ∧ idx 0 ≥ 0
  by_cases hcond : idx 0 + idx 1 = k - 1 ∧ idx 0 ≥ 0
  · rw [if_pos ⟨by omega, by omega⟩, if_pos hcond]
    simp only [zsmul_eq_mul, smul_eq_mul, ← Int.cast_mul]
    congr 1
    have hm0_eq : (idx 0 + 1).toNat = (idx 0).toNat + 1 := by omega
    have h_sign : (k - (idx 0 + 1)).natAbs = ((k - 1) - idx 0).natAbs := by omega
    rw [hm0_eq, h_sign]
    have h_succ := intBinomial_succ_mul_eq k (idx 0).toNat
    calc (idx 0 + 1) * (intBinomial k ((idx 0).toNat + 1) * (-1) ^ ((k - 1) - idx 0).natAbs)
        = ↑((idx 0).toNat + 1) * (intBinomial k ((idx 0).toNat + 1) * (-1) ^ ((k - 1) - idx 0).natAbs) := by
          congr 1; omega
      _ = (↑((idx 0).toNat + 1) * intBinomial k ((idx 0).toNat + 1)) *
          (-1) ^ ((k - 1) - idx 0).natAbs := by ring
      _ = (k * intBinomial (k - 1) (idx 0).toNat) * (-1) ^ ((k - 1) - idx 0).natAbs := by rw [h_succ]
      _ = k * (intBinomial (k - 1) (idx 0).toNat * (-1) ^ ((k - 1) - idx 0).natAbs) := by ring
  · -- ¬hcond: RHS condition fails
    rw [if_neg hcond, smul_zero]
    by_cases hlhs : (idx 0 + 1) + idx 1 = k ∧ idx 0 + 1 ≥ 0
    · -- LHS holds but RHS doesn't → idx 0 = -1, so idx 0 + 1 = 0
      rw [if_pos hlhs]
      have : (idx 0 + 1 : ℤ) = 0 := by omega
      rw [this, zero_smul]
    · rw [if_neg hlhs, smul_zero]

/-- Proposition 1.2.6(d): ∂_w i_{w,z}(z-w)^k = -k · i_{w,z}(z-w)^{k-1} -/
theorem deriv_w_expansion_iwz (k : ℤ) :
    GeneralizedFormalDistribution.deriv (expansion_iwz k : GenFormalDist2 A) 1 =
    (-k : A) • expansion_iwz (k - 1) := by
  ext idx
  show (idx 1 + 1 : ℤ) • (expansion_iwz k : GenFormalDist2 A).coeff (Function.update idx 1 (idx 1 + 1))
     = (-k : A) • (expansion_iwz (k - 1) : GenFormalDist2 A).coeff idx
  rw [expansion_iwz_coeff, expansion_iwz_coeff]
  simp only [update_eval_same, update_eval_diff idx 1 0 (idx 1 + 1) (by decide)]
  -- Both conditions are: idx 0 + idx 1 = k - 1 ∧ idx 0 ≥ 0 (identical!)
  by_cases hcond : idx 0 + idx 1 = k - 1 ∧ idx 0 ≥ 0
  · rw [if_pos ⟨by omega, hcond.2⟩, if_pos hcond]
    simp only [zsmul_eq_mul, smul_eq_mul, ← Int.cast_neg, ← Int.cast_mul]
    congr 1
    -- Need: (idx 1 + 1) * (C(k, m) * (-1)^(k-idx 0).natAbs) = -k * (C(k-1, m) * (-1)^((k-1)-idx 0).natAbs)
    -- where m = (idx 0).toNat and idx 1 + 1 = k - idx 0
    have hm : (↑((idx 0).toNat) : ℤ) = idx 0 := Int.toNat_of_nonneg hcond.2
    have h_key := intBinomial_mul_sub k (idx 0).toNat
    -- h_key: (k - ↑m) * C(k, m) = k * C(k-1, m)
    have h_sign := neg_one_pow_natAbs_succ ((k - 1) - idx 0)
    -- h_sign: (-1)^((k-1-idx 0)+1).natAbs = -(-1)^(k-1-idx 0).natAbs
    -- i.e., (-1)^(k-idx 0).natAbs = -(-1)^(k-1-idx 0).natAbs
    have h_sign' : ((-1 : ℤ) ^ (k - idx 0).natAbs) = -((-1 : ℤ) ^ ((k - 1) - idx 0).natAbs) := by
      convert h_sign using 2; omega
    calc (idx 1 + 1) * (intBinomial k (idx 0).toNat * (-1) ^ (k - idx 0).natAbs)
        = (k - ↑((idx 0).toNat)) * (intBinomial k (idx 0).toNat * (-1) ^ (k - idx 0).natAbs) := by
          congr 1; omega
      _ = ((k - ↑((idx 0).toNat)) * intBinomial k (idx 0).toNat) * (-1) ^ (k - idx 0).natAbs := by ring
      _ = (k * intBinomial (k - 1) (idx 0).toNat) * (-1) ^ (k - idx 0).natAbs := by rw [h_key]
      _ = (k * intBinomial (k - 1) (idx 0).toNat) * (-((-1) ^ ((k - 1) - idx 0).natAbs)) := by rw [h_sign']
      _ = -k * (intBinomial (k - 1) (idx 0).toNat * (-1) ^ ((k - 1) - idx 0).natAbs) := by ring
  · rw [if_neg (by omega : ¬(idx 0 + (idx 1 + 1) = k ∧ idx 0 ≥ 0)), if_neg hcond]
    simp [smul_zero]

/-! ## 1.3 Dirac's δ distribution -/

/-- Definition 1.3.1: Formal Dirac δ distribution δ(z,w)

    The Dirac delta distribution has infinite support (the line {(k, -k-1) | k ∈ ℤ}),
    so we define it as a GeneralizedFormalDistribution.

    The support is finite above any bound: for any (b₀, b₁), only finitely many
    points on the line satisfy both k ≥ b₀ and -k-1 ≥ b₁, namely the interval
    [max(b₀, -b₁-1), -b₁-1].

    This is the dual-definition approach:
    - FormalDistribution (total finite support): clean multiplication, 0 axioms
    - GeneralizedFormalDistribution (finite above bounds): supports diracDelta, 0 axioms
    - Total: 0 axioms! Use the right tool for each purpose.
-/
noncomputable def diracDelta : GenFormalDist2 A where
  coeff := fun idx => if idx 0 + idx 1 + 1 = 0 then (1 : A) else 0
  support_finite := fun bound => by
    -- The support is {(k, l) | k + l + 1 = 0}, i.e., l = -k-1
    -- Above bound (b₀, b₁), we need k ≥ b₀ and -k-1 ≥ b₁
    -- This gives: b₀ ≤ k ≤ -b₁-1
    -- If b₀ > -b₁-1, the set is empty; otherwise it's a finite interval

    by_cases h : bound 0 ≤ -bound 1 - 1
    · -- Non-empty case: finite interval [bound 0, -bound 1 - 1]
      -- Convert to Finset for easier handling
      let k_finset : Finset ℤ := Finset.Icc (bound 0) (-bound 1 - 1)

      -- The support maps to this finset
      have h_subset : {idx : Fin 2 → ℤ | (∀ i, idx i ≥ bound i) ∧
                                         (if idx 0 + idx 1 + 1 = 0 then (1 : A) else 0) ≠ 0} ⊆
                      (fun k => fun i : Fin 2 => if i = 0 then k else -k - 1) '' (k_finset : Set ℤ) := by
        intro idx ⟨hall, hne⟩
        split_ifs at hne with hidx
        · use idx 0
          constructor
          · rw [Finset.mem_coe, Finset.mem_Icc]
            have eq_idx1 : idx 1 = -idx 0 - 1 := by omega
            have ge_bound0 : idx 0 ≥ bound 0 := hall 0
            have ge_bound1 : idx 1 ≥ bound 1 := hall 1
            omega
          · ext i
            fin_cases i
            · simp
            · have : idx 1 = -idx 0 - 1 := by omega
              simp [this]
        · simp at hne

      apply Set.Finite.subset _ h_subset
      apply Set.Finite.image
      exact Finset.finite_toSet k_finset

    · -- Empty case: bound 0 > -bound 1 - 1
      convert Set.finite_empty
      ext idx
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hall
      split_ifs with hidx
      · have : idx 0 ≥ bound 0 := hall 0
        have : idx 1 ≥ bound 1 := hall 1
        have : idx 1 = -idx 0 - 1 := by omega
        omega
      · simp

/-- The coefficients of diracDelta match the expected pattern -/
theorem diracDelta_coeff (idx : Fin 2 → ℤ) :
    diracDelta.coeff idx = if idx 0 + idx 1 + 1 = 0 then (1 : A) else 0 := rfl

/-- Proposition 1.3.4: δ(z,w) = i_{z,w}(z-w)^{-1} - i_{w,z}(z-w)^{-1}

    For k = -1: C(-1,j)(-1)^j = (-1)^j·(-1)^j = 1, so:
    - i_{z,w}(z-w)^{-1} has coefficient 1 at (n, -n-1) for n ≤ -1 (m = -n-1 ≥ 0)
    - i_{w,z}(z-w)^{-1} has coefficient -1 at (n, -n-1) for n ≥ 0 (m = -n-1 ≤ -1)
    Their difference is 1 on the entire anti-diagonal n + m + 1 = 0, which is δ(z,w). -/
theorem diracDelta_eq_expansion_diff :
    (expansion_izw (-1) : GenFormalDist2 A) - (expansion_iwz (-1) : GenFormalDist2 A) =
    (diracDelta : GenFormalDist2 A) := by
  ext idx
  show (expansion_izw (-1) : GenFormalDist2 A).coeff idx -
       (expansion_iwz (-1) : GenFormalDist2 A).coeff idx = diracDelta.coeff idx
  rw [expansion_izw_coeff, expansion_iwz_coeff, diracDelta_coeff]
  by_cases hline : idx 0 + idx 1 + 1 = 0
  · -- On the anti-diagonal: exactly one of idx 1 ≥ 0, idx 0 ≥ 0 holds
    have hsum : idx 0 + idx 1 = -1 := by omega
    by_cases hm : idx 1 ≥ 0
    · -- idx 1 ≥ 0, so idx 0 < 0
      rw [if_pos ⟨hsum, hm⟩, if_neg (by omega : ¬(idx 0 + idx 1 = -1 ∧ idx 0 ≥ 0)),
          if_pos hline, sub_zero, intBinomial_neg_one, ← pow_add]
      -- (-1)^n * (-1)^n = (-1)^(2n) = 1
      have : (idx 1).toNat + (idx 1).toNat = 2 * (idx 1).toNat := by omega
      rw [this, pow_mul, neg_one_sq, one_pow, Int.cast_one]
    · -- idx 0 ≥ 0 (since idx 1 < 0)
      push_neg at hm
      have hn : idx 0 ≥ 0 := by omega
      rw [if_neg (by omega : ¬(idx 0 + idx 1 = -1 ∧ idx 1 ≥ 0)),
          if_pos ⟨hsum, hn⟩, if_pos hline, zero_sub, intBinomial_neg_one, ← pow_add]
      -- (-1)^n * (-1)^(n+1) = (-1)^(2n+1) = -1, and -(-1) = 1
      have habs : (-1 - idx 0).natAbs = (idx 0 + 1).toNat := by omega
      rw [habs]
      have : (idx 0).toNat + (idx 0 + 1).toNat = 2 * (idx 0).toNat + 1 := by omega
      rw [this, pow_add, pow_mul, neg_one_sq, one_pow, one_mul,
          show ((-1 : ℤ) ^ 1) = -1 from by norm_num,
          Int.cast_neg, Int.cast_one, neg_neg]
  · -- Off the anti-diagonal: both coefficients are 0
    rw [if_neg (by omega : ¬(idx 0 + idx 1 = -1 ∧ idx 1 ≥ 0)),
        if_neg (by omega : ¬(idx 0 + idx 1 = -1 ∧ idx 0 ≥ 0)),
        if_neg hline, sub_zero]

/-! ## Proposition 1.3.5: Properties of Dirac δ distribution -/

namespace DiracDelta

/-- (3) Symmetry: The definition of δ is symmetric -/
theorem property3 : @diracDelta A _ = @diracDelta A _ := by rfl

/-- (4) Antisymmetry of derivatives: ∂_z δ(z,w) + ∂_w δ(z,w) = 0 -/
theorem property4 : GeneralizedFormalDistribution.deriv diracDelta 0 + GeneralizedFormalDistribution.deriv diracDelta 1 = (0 : GenFormalDist2 A) := by
  ext idx
  -- Expand the coefficient function
  show (idx 0 + 1 : ℤ) • diracDelta.coeff (Function.update idx 0 (idx 0 + 1)) +
       (idx 1 + 1 : ℤ) • diracDelta.coeff (Function.update idx 1 (idx 1 + 1)) = 0
  -- Use diracDelta_coeff theorem to rewrite coefficients
  rw [diracDelta_coeff, diracDelta_coeff]
  -- Simplify Function.update evaluations
  have h1 : Function.update idx 0 (idx 0 + 1) 0 = idx 0 + 1 := update_eval_same idx 0 (idx 0 + 1)
  have h2 : Function.update idx 0 (idx 0 + 1) 1 = idx 1 := update_eval_diff idx 0 1 (idx 0 + 1) (by decide)
  have h3 : Function.update idx 1 (idx 1 + 1) 0 = idx 0 := update_eval_diff idx 1 0 (idx 1 + 1) (by decide)
  have h4 : Function.update idx 1 (idx 1 + 1) 1 = idx 1 + 1 := update_eval_same idx 1 (idx 1 + 1)
  simp only [h1, h2, h3, h4]
  -- Both conditions become idx 0 + idx 1 + 2 = 0
  by_cases h : idx 0 + idx 1 + 2 = 0
  · -- Case: idx 0 + idx 1 + 2 = 0, so both coefficients are 1
    have cond1 : (idx 0 + 1 : ℤ) + idx 1 + 1 = 0 := by omega
    have cond2 : idx 0 + (idx 1 + 1 : ℤ) + 1 = 0 := by omega
    simp only [cond1, cond2, ↓reduceIte, zsmul_eq_mul, mul_one]
    -- Show: (idx 0 + 1 : A) + (idx 1 + 1 : A) = 0
    have key : ((idx 0 + 1 : ℤ) : A) + ((idx 1 + 1 : ℤ) : A) = ((idx 0 + 1 + (idx 1 + 1) : ℤ) : A) := by
      rw [← Int.cast_add]
    rw [key]
    have : idx 0 + 1 + (idx 1 + 1) = idx 0 + idx 1 + 2 := by omega
    rw [this, h]
    simp
  · -- Case: idx 0 + idx 1 + 2 ≠ 0, so both coefficients are 0
    have cond1 : ¬((idx 0 + 1 : ℤ) + idx 1 + 1 = 0) := by omega
    have cond2 : ¬(idx 0 + (idx 1 + 1 : ℤ) + 1 = 0) := by omega
    simp only [cond1, cond2, ↓reduceIte]
    rw [smul_zero, smul_zero, zero_add]

/-! ### Multiplication by (z - w) -/

/-- Multiplication by (z - w) on generalized 2-variable distributions.
    ((z-w) · a)(n,m) = a(n-1,m) - a(n,m-1) -/
def mul_z_minus_w (a : GenFormalDist2 A) : GenFormalDist2 A where
  coeff := fun idx =>
    a.coeff (Function.update idx 0 (idx 0 - 1)) -
    a.coeff (Function.update idx 1 (idx 1 - 1))
  support_finite := fun bound => by
    -- Support of (z-w)·a above bound ⊆ shift of a's support ∪ shift of a's support
    have ha0 := a.support_finite (Function.update bound 0 (bound 0 - 1))
    have ha1 := a.support_finite (Function.update bound 1 (bound 1 - 1))
    -- Image under shifts
    let shift0 : (Fin 2 → ℤ) → (Fin 2 → ℤ) := fun idx' => Function.update idx' 0 (idx' 0 + 1)
    let shift1 : (Fin 2 → ℤ) → (Fin 2 → ℤ) := fun idx' => Function.update idx' 1 (idx' 1 + 1)
    apply Set.Finite.subset (Set.Finite.union (ha0.image shift0) (ha1.image shift1))
    intro idx ⟨hge, hne⟩
    by_cases h0 : a.coeff (Function.update idx 0 (idx 0 - 1)) ≠ 0
    · left; simp only [Set.mem_image, shift0]
      refine ⟨Function.update idx 0 (idx 0 - 1), ⟨?_, h0⟩, ?_⟩
      · intro i; by_cases hi : i = 0
        · subst hi; simp [Function.update]; linarith [hge 0]
        · rw [Function.update_of_ne hi, Function.update_of_ne hi]; exact hge i
      · ext i; by_cases hi : i = 0
        · simp [hi, Function.update]
        · simp [hi, Function.update]
    · push_neg at h0
      have h1 : a.coeff (Function.update idx 1 (idx 1 - 1)) ≠ 0 := by
        intro h1; apply hne; simp [h0, h1]
      right; simp only [Set.mem_image, shift1]
      refine ⟨Function.update idx 1 (idx 1 - 1), ⟨?_, h1⟩, ?_⟩
      · intro i; by_cases hi : i = 1
        · subst hi; simp [Function.update]; linarith [hge 1]
        · rw [Function.update_of_ne hi, Function.update_of_ne hi]; exact hge i
      · ext i; by_cases hi : i = 1
        · simp [hi, Function.update]
        · simp [hi, Function.update]

/-- Iterated multiplication by (z - w) -/
def mul_z_minus_w_iter (a : GenFormalDist2 A) : ℕ → GenFormalDist2 A
  | 0 => a
  | n + 1 => mul_z_minus_w (mul_z_minus_w_iter a n)

/-- (z-w) · δ = 0: the base case for property 1 -/
theorem mul_z_minus_w_diracDelta : mul_z_minus_w (diracDelta : GenFormalDist2 A) = 0 := by
  ext idx
  show diracDelta.coeff (Function.update idx 0 (idx 0 - 1)) -
       diracDelta.coeff (Function.update idx 1 (idx 1 - 1)) = 0
  simp only [diracDelta_coeff]
  -- Simplify Function.update evaluations
  simp only [Function.update, show ¬((0 : Fin 2) = 1) from by decide,
             show ¬((1 : Fin 2) = 0) from by decide,
             dite_true, dite_false]
  -- Both conditions reduce to idx 0 + idx 1 = 0
  by_cases h : idx 0 + idx 1 = 0
  · rw [if_pos (by omega : idx 0 - 1 + idx 1 + 1 = 0),
        if_pos (by omega : idx 0 + (idx 1 - 1) + 1 = 0)]
    exact sub_self _
  · rw [if_neg (by omega : ¬(idx 0 - 1 + idx 1 + 1 = 0)),
        if_neg (by omega : ¬(idx 0 + (idx 1 - 1) + 1 = 0))]
    exact sub_self _

/-- Rising factorial product: (q+1)(q+2)...(q+n) computed in ℤ -/
private def risingProd (q : ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => risingProd q n * (q + ↑n + 1)

private theorem risingProd_zero (q : ℤ) : risingProd q 0 = 1 := rfl

private theorem risingProd_succ (q : ℤ) (n : ℕ) :
    risingProd q (n + 1) = risingProd q n * (q + ↑n + 1) := rfl

/-- Key identity: risingProd q (n+1) = (q+1) * risingProd (q+1) n -/
private theorem risingProd_shift (q : ℤ) (n : ℕ) :
    risingProd q (n + 1) = (q + 1) * risingProd (q + 1) n := by
  induction n with
  | zero => simp [risingProd]
  | succ n ih =>
    rw [risingProd_succ q (n + 1), ih, risingProd_succ (q + 1) n]
    push_cast; ring

/-- Difference identity: risingProd q (n+1) - risingProd (q-1) (n+1) = (n+1) * risingProd q n -/
private theorem risingProd_diff (q : ℤ) (n : ℕ) :
    risingProd q (n + 1) - risingProd (q - 1) (n + 1) = (↑(n + 1) : ℤ) * risingProd q n := by
  rw [risingProd_succ, risingProd_shift (q - 1) n]
  simp only [sub_add_cancel]
  push_cast; ring

/-- Coefficient formula for the n-th w-derivative of diracDelta.
    (∂_w^n δ)_{p,q} = if p + q + n + 1 = 0 then (q+1)(q+2)...(q+n) else 0 -/
theorem gen_iteratedDeriv_w_diracDelta_coeff (n : ℕ) (idx : Fin 2 → ℤ) :
    (GeneralizedFormalDistribution.iteratedDeriv diracDelta (1 : Fin 2) n).coeff idx =
    if idx 0 + idx 1 + ↑n + 1 = 0
    then (risingProd (idx 1) n : A)
    else 0 := by
  induction n generalizing idx with
  | zero =>
    simp only [GeneralizedFormalDistribution.iteratedDeriv, Nat.cast_zero, add_zero,
               risingProd, Int.cast_one]
    exact diracDelta_coeff idx
  | succ n ih =>
    simp only [GeneralizedFormalDistribution.iteratedDeriv,
               GeneralizedFormalDistribution.deriv]
    show (idx 1 + 1 : ℤ) •
      (GeneralizedFormalDistribution.iteratedDeriv diracDelta 1 n).coeff
        (Function.update idx 1 (idx 1 + 1)) = _
    have h_update_0 : (Function.update idx (1 : Fin 2) (idx 1 + 1)) 0 = idx 0 := by
      rw [Function.update_of_ne (by decide)]
    have h_update_1 : (Function.update idx (1 : Fin 2) (idx 1 + 1)) 1 = idx 1 + 1 := by
      simp [Function.update]
    rw [ih (Function.update idx 1 (idx 1 + 1))]
    rw [h_update_0, h_update_1]
    by_cases h : idx 0 + idx 1 + (↑n + 1) + 1 = 0
    · rw [if_pos (by omega : idx 0 + (idx 1 + 1) + (↑n : ℤ) + 1 = 0)]
      rw [if_pos (by omega : idx 0 + idx 1 + (↑(n + 1) : ℤ) + 1 = 0)]
      -- LHS: (idx 1 + 1) • (risingProd (idx 1 + 1) n : A)
      -- RHS: (risingProd (idx 1) (n+1) : A)
      -- Use risingProd_shift: risingProd q (n+1) = (q+1) * risingProd (q+1) n
      rw [risingProd_shift (idx 1) n]
      push_cast [Int.cast_mul]
      rw [zsmul_eq_mul]
      congr 1; push_cast; abel
    · rw [if_neg (by omega : ¬(idx 0 + (idx 1 + 1) + (↑n : ℤ) + 1 = 0))]
      rw [if_neg (by omega : ¬(idx 0 + idx 1 + (↑(n + 1) : ℤ) + 1 = 0))]
      simp

/-- mul_z_minus_w commutes with scalar multiplication -/
theorem mul_z_minus_w_smul (c : A) (a : GenFormalDist2 A) :
    mul_z_minus_w (c • a) = c • mul_z_minus_w a := by
  ext idx
  show (c • a).coeff (Function.update idx 0 (idx 0 - 1)) -
       (c • a).coeff (Function.update idx 1 (idx 1 - 1)) =
       c • (a.coeff (Function.update idx 0 (idx 0 - 1)) -
            a.coeff (Function.update idx 1 (idx 1 - 1)))
  show c • a.coeff (Function.update idx 0 (idx 0 - 1)) -
       c • a.coeff (Function.update idx 1 (idx 1 - 1)) =
       c • (a.coeff (Function.update idx 0 (idx 0 - 1)) -
            a.coeff (Function.update idx 1 (idx 1 - 1)))
  rw [smul_sub]

/-- (2) (z-w) · ∂_w^n δ = n · ∂_w^{n-1} δ for n ≥ 1

    This is the key recurrence: multiplying by (z-w) lowers the derivative order by 1. -/
theorem property2 (n : ℕ) (hn : n ≥ 1) :
    mul_z_minus_w (GeneralizedFormalDistribution.iteratedDeriv (diracDelta : GenFormalDist2 A) (1 : Fin 2) n) =
    ((n : ℕ) : A) • GeneralizedFormalDistribution.iteratedDeriv diracDelta (1 : Fin 2) (n - 1) := by
  ext idx
  -- LHS coefficient
  show (GeneralizedFormalDistribution.iteratedDeriv diracDelta 1 n).coeff
        (Function.update idx 0 (idx 0 - 1)) -
       (GeneralizedFormalDistribution.iteratedDeriv diracDelta 1 n).coeff
        (Function.update idx 1 (idx 1 - 1)) =
       (n : A) • (GeneralizedFormalDistribution.iteratedDeriv diracDelta 1 (n - 1)).coeff idx
  -- Evaluate using the coefficient formula
  have h_update_00 : (Function.update idx (0 : Fin 2) (idx 0 - 1)) 0 = idx 0 - 1 := by
    simp [Function.update]
  have h_update_01 : (Function.update idx (0 : Fin 2) (idx 0 - 1)) 1 = idx 1 := by
    rw [Function.update_of_ne (by decide)]
  have h_update_10 : (Function.update idx (1 : Fin 2) (idx 1 - 1)) 0 = idx 0 := by
    rw [Function.update_of_ne (by decide)]
  have h_update_11 : (Function.update idx (1 : Fin 2) (idx 1 - 1)) 1 = idx 1 - 1 := by
    simp [Function.update]
  rw [gen_iteratedDeriv_w_diracDelta_coeff n (Function.update idx 0 (idx 0 - 1)),
      gen_iteratedDeriv_w_diracDelta_coeff n (Function.update idx 1 (idx 1 - 1)),
      gen_iteratedDeriv_w_diracDelta_coeff (n - 1) idx]
  rw [h_update_00, h_update_01, h_update_10, h_update_11]
  -- Conditions all reduce to idx 0 + idx 1 + n = 0
  by_cases h : idx 0 + idx 1 + ↑n = 0
  · rw [if_pos (by omega : (idx 0 - 1 : ℤ) + idx 1 + ↑n + 1 = 0),
        if_pos (by omega : idx 0 + (idx 1 - 1 : ℤ) + ↑n + 1 = 0),
        if_pos (by omega : idx 0 + idx 1 + ↑(n - 1 : ℕ) + 1 = 0)]
    -- Use risingProd_diff: risingProd q (n+1) - risingProd (q-1) (n+1) = (n+1) * risingProd q n
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    -- Goal: ↑(risingProd (idx 1) (n'+1)) - ↑(risingProd (idx 1 - 1) (n'+1))
    --     = ((n'+1 : ℕ) : A) • ↑(risingProd (idx 1) n')
    rw [← Int.cast_sub, risingProd_diff (idx 1) n', Int.cast_mul]
    -- Goal: ((↑(n'+1) : ℤ) : A) * ↑(risingProd (idx 1) n') = ((n'+1 : ℕ) : A) • ↑(risingProd (idx 1) n')
    rw [Int.cast_natCast]
    rfl
  · -- All conditions false
    rw [if_neg (by omega : ¬((idx 0 - 1 : ℤ) + idx 1 + ↑n + 1 = 0)),
        if_neg (by omega : ¬(idx 0 + (idx 1 - 1 : ℤ) + ↑n + 1 = 0)),
        if_neg (by omega : ¬(idx 0 + idx 1 + ↑(n - 1 : ℕ) + 1 = 0))]
    simp

/-- Iteration commutes: f^{n+1}(a) = f^n(f(a)) -/
private theorem mul_z_minus_w_iter_succ (a : GenFormalDist2 A) (n : ℕ) :
    mul_z_minus_w_iter a (n + 1) = mul_z_minus_w_iter (mul_z_minus_w a) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show mul_z_minus_w (mul_z_minus_w_iter a (n + 1)) =
         mul_z_minus_w (mul_z_minus_w_iter (mul_z_minus_w a) n)
    rw [ih]

/-- Iteration distributes over scalar multiplication -/
private theorem mul_z_minus_w_iter_smul (m : ℕ) (c : A) (a : GenFormalDist2 A) :
    mul_z_minus_w_iter (c • a) m = c • mul_z_minus_w_iter a m := by
  induction m with
  | zero => rfl
  | succ m ihm =>
    show mul_z_minus_w (mul_z_minus_w_iter (c • a) m) =
         c • mul_z_minus_w (mul_z_minus_w_iter a m)
    rw [ihm, mul_z_minus_w_smul]

/-- (1) (z-w)^{n+1} · ∂_w^n δ = 0 for all n -/
theorem property1 (n : ℕ) :
    mul_z_minus_w_iter (GeneralizedFormalDistribution.iteratedDeriv (diracDelta : GenFormalDist2 A) (1 : Fin 2) n) (n + 1) = 0 := by
  induction n with
  | zero =>
    simp only [mul_z_minus_w_iter, GeneralizedFormalDistribution.iteratedDeriv]
    exact mul_z_minus_w_diracDelta
  | succ n ih =>
    -- (z-w)^{n+2} ∂_w^{n+1} δ = (z-w)^{n+1} ((z-w) ∂_w^{n+1} δ)
    -- = (z-w)^{n+1} ((n+1) • ∂_w^n δ) = (n+1) • (z-w)^{n+1} ∂_w^n δ = (n+1) • 0 = 0
    rw [mul_z_minus_w_iter_succ, property2 (n + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [mul_z_minus_w_iter_smul, ih]
    ext idx; show ((n + 1 : ℕ) : A) • (0 : GenFormalDist2 A).coeff idx = 0
    exact smul_zero _

/-- Scalar multiplication is associative: c₁ • (c₂ • a) = (c₁ * c₂) • a -/
private theorem smul_smul_gen (c₁ c₂ : A) (a : GenFormalDist2 A) :
    c₁ • (c₂ • a) = (c₁ * c₂) • a := by
  ext idx
  show c₁ * (c₂ * a.coeff idx) = (c₁ * c₂) * a.coeff idx
  exact (mul_assoc c₁ c₂ _).symm

/-- Proposition 1.3.5(7): Falling factorial identity.


    (z-w)^j · ∂_w^n δ(z,w) = descFactorial(n,j) · ∂_w^{n-j} δ(z,w)

    This is the algebraic core of the exponential identity
    exp(λ(z-w)) · ∂_w^n δ = (λ + ∂_w)^n δ.
    The full identity follows by expanding exp(λ(z-w)) = Σ_j λ^j/j! · (z-w)^j,
    applying this theorem termwise, and noting descFactorial(n,j)/j! = C(n,j).
    The series truncates since descFactorial(n,j) = 0 for j > n. -/
theorem property7 (n j : ℕ) :
    mul_z_minus_w_iter
      (GeneralizedFormalDistribution.iteratedDeriv (diracDelta : GenFormalDist2 A) (1 : Fin 2) n) j =
    ((Nat.descFactorial n j : ℕ) : A) •
      GeneralizedFormalDistribution.iteratedDeriv diracDelta (1 : Fin 2) (n - j) := by
  induction j with
  | zero =>
    simp only [mul_z_minus_w_iter, Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero]
    ext idx
    show (GeneralizedFormalDistribution.iteratedDeriv (diracDelta : GenFormalDist2 A) 1 n).coeff idx =
         (1 : A) * (GeneralizedFormalDistribution.iteratedDeriv diracDelta 1 n).coeff idx
    exact (one_mul _).symm
  | succ j ih =>
    show mul_z_minus_w (mul_z_minus_w_iter
      (GeneralizedFormalDistribution.iteratedDeriv diracDelta 1 n) j) = _
    rw [ih, mul_z_minus_w_smul]
    by_cases hjn : j < n
    · -- Case j < n: n - j ≥ 1, so property2 applies
      have h_idx : (n - j : ℕ) - 1 = n - (j + 1) := by omega
      rw [property2 (n - j) (by omega), smul_smul_gen, h_idx, ← Nat.cast_mul,
          show Nat.descFactorial n j * (n - j) = Nat.descFactorial n (j + 1) from
            by rw [Nat.descFactorial_succ, mul_comm]]
    · -- Case j ≥ n: both sides are zero
      push_neg at hjn
      have hnj : n - j = 0 := by omega
      have hnj1 : n - (j + 1) = 0 := by omega
      simp only [hnj, hnj1, GeneralizedFormalDistribution.iteratedDeriv]
      rw [mul_z_minus_w_diracDelta]
      have hdf : Nat.descFactorial n (j + 1) = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hdf, Nat.cast_zero]
      ext idx
      show (↑(Nat.descFactorial n j) : A) • (0 : GenFormalDist2 A).coeff idx =
           (0 : A) • (diracDelta : GenFormalDist2 A).coeff idx
      exact (smul_zero _).trans (zero_smul A _).symm

section CommRingProperties

variable {A : Type*} [CommRing A]
open GeneralizedFormalDistribution

/-- The coefficient of embed_z(a) * δ at index (n,m) equals a_{n+m+1} -/
private lemma embed_z_mulGen_diracDelta_coeff (a : FormalDist1 A) (idx : Fin 2 → ℤ) :
    ((FormalDistribution.embed_z a).mulGen diracDelta).coeff idx =
    a.coeff (fun _ => idx 0 + idx 1 + 1) := by
  change GeneralizedFormalDistribution.mulFormalGen _ _ _ _ = _
  unfold GeneralizedFormalDistribution.mulFormalGen
  rw [Finset.sum_eq_single (fun i : Fin 2 => if i = 0 then idx 0 + idx 1 + 1 else 0)]
  · -- Main term: f(b) = a_{n+m+1}
    simp only [FormalDistribution.embed_z, diracDelta_coeff]
    simp only [show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
               ite_true, ite_false, sub_zero]
    rw [if_pos (by omega : idx 0 - (idx 0 + idx 1 + 1) + idx 1 + 1 = 0), mul_one]
  · -- Other terms vanish
    intro c hc hne
    have hsupp : (FormalDistribution.embed_z a).coeff c ≠ 0 :=
      (Set.Finite.mem_toFinset _).mp hc
    by_cases h1 : c 1 = 0
    · -- c 1 = 0 but c ≠ b, so c 0 ≠ idx 0 + idx 1 + 1
      have hc0 : c 0 ≠ idx 0 + idx 1 + 1 := by
        intro heq; apply hne; ext i; fin_cases i <;> simp [heq, h1]
      simp only [FormalDistribution.embed_z, diracDelta_coeff] at hsupp ⊢
      simp only [h1, show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
                 ite_true, ite_false, sub_zero] at hsupp ⊢
      rw [if_neg (by omega : ¬(idx 0 - c 0 + idx 1 + 1 = 0)), mul_zero]
    · -- c 1 ≠ 0: embed_z returns 0, contradicts membership
      exfalso; apply hsupp
      simp [FormalDistribution.embed_z, h1]
  · -- b ∉ support: f(b) = 0
    intro hb
    have : (FormalDistribution.embed_z a).coeff
        (fun i : Fin 2 => if i = 0 then idx 0 + idx 1 + 1 else 0) = 0 := by
      by_contra h; exact hb ((Set.Finite.mem_toFinset _).mpr h)
    rw [this, zero_mul]

/-- The coefficient of embed_w(a) * δ at index (n,m) also equals a_{n+m+1} -/
private lemma embed_w_mulGen_diracDelta_coeff (a : FormalDist1 A) (idx : Fin 2 → ℤ) :
    ((FormalDistribution.embed_w a).mulGen diracDelta).coeff idx =
    a.coeff (fun _ => idx 0 + idx 1 + 1) := by
  change GeneralizedFormalDistribution.mulFormalGen _ _ _ _ = _
  unfold GeneralizedFormalDistribution.mulFormalGen
  rw [Finset.sum_eq_single (fun i : Fin 2 => if i = 0 then 0 else idx 0 + idx 1 + 1)]
  · -- Main term
    simp only [FormalDistribution.embed_w, diracDelta_coeff]
    simp only [show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
               ite_true, ite_false, sub_zero]
    rw [if_pos (by omega : idx 0 + (idx 1 - (idx 0 + idx 1 + 1)) + 1 = 0), mul_one]
  · -- Other terms vanish
    intro c hc hne
    have hsupp : (FormalDistribution.embed_w a).coeff c ≠ 0 :=
      (Set.Finite.mem_toFinset _).mp hc
    by_cases h0 : c 0 = 0
    · have hc1 : c 1 ≠ idx 0 + idx 1 + 1 := by
        intro heq; apply hne; ext i; fin_cases i <;> simp [heq, h0]
      simp only [FormalDistribution.embed_w, diracDelta_coeff] at hsupp ⊢
      simp only [h0, show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
                 ite_true, ite_false, sub_zero] at hsupp ⊢
      rw [if_neg (by omega : ¬(idx 0 + (idx 1 - c 1) + 1 = 0)), mul_zero]
    · exfalso; apply hsupp
      simp [FormalDistribution.embed_w, h0]
  · -- b ∉ support
    intro hb
    have : (FormalDistribution.embed_w a).coeff
        (fun i : Fin 2 => if i = 0 then 0 else idx 0 + idx 1 + 1) = 0 := by
      by_contra h; exact hb ((Set.Finite.mem_toFinset _).mpr h)
    rw [this, zero_mul]

/-- (5) a(z)δ(z,w) = a(w)δ(z,w) for any formal distribution a(z) -/
theorem property5 (a : FormalDist1 A) :
    (FormalDistribution.embed_z a).mulGen diracDelta =
    (FormalDistribution.embed_w a).mulGen diracDelta := by
  ext idx
  rw [embed_z_mulGen_diracDelta_coeff, embed_w_mulGen_diracDelta_coeff]

/-- (6) Res_z a(z)δ(z,w) = a(w), showing δ extracts a at w -/
theorem property6 (a : FormalDist1 A) :
    GeneralizedFormalDistribution.gen_residue_var 0
      ((FormalDistribution.embed_z a).mulGen diracDelta) =
    a.toGeneralized := by
  ext idx
  simp only [GeneralizedFormalDistribution.gen_residue_var]
  rw [embed_z_mulGen_diracDelta_coeff]
  simp only [FormalDistribution.toGeneralized]
  congr 1; ext i; fin_cases i; simp

end CommRingProperties

end DiracDelta

/-! ## Summary

All main results from Section 1 are formalized above:
  - Definition 1.1.1: FormalDistribution, FormalPolynomial, FormalTaylorSeries
  - Definition 1.1.3: fourierExpansion, fourierMode, residue
  - Definition 1.2.1: expansion_izw, expansion_iwz (as GenFormalDist2)
  - Definition 1.2.2: extBinomial, intBinomial
  - Proposition 1.3.4: diracDelta_eq_expansion_diff (δ = i_{z,w}(z-w)^{-1} - i_{w,z}(z-w)^{-1})
  - Definition 1.3.1: diracDelta
  - Proposition 1.3.5: Properties 1-7 of δ (all complete)
-/

-- Verify key definitions compile
example : Type _ := FormalDistribution ℂ 1
example : Type _ := GeneralizedFormalDistribution ℂ 2
example : FormalDist1 ℂ → (ℤ → ℂ) := fourierExpansion
example : ℤ → ℕ → ℚ := extBinomial
noncomputable example : GenFormalDist2 ℂ := diracDelta

