/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FormalDistribution.Deriv
import Mathlib.Data.Int.Interval

/-!
# Multiplication of Formal Distributions

This file defines the Cauchy product (convolution) for one- and two-variable
formal distributions, along with ring axioms and embedding operations.

## Main definitions

* `FormalDistribution.mulCoeff1d` - convolution coefficient for 1D distributions
* `Mul (FormalDist1 A)` - multiplication instance for 1D distributions
* `Mul (FormalDist2 A)` - multiplication instance for 2D distributions (CommRing)
* `FormalDistribution.embedFst` - embed 1D into 2D in the first variable
* `FormalDistribution.embedSnd` - embed 1D into 2D in the second variable
* `FormalDistribution.residueAt` - extract residue in a specific variable

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Section 1.1
-/

open scoped BigOperators

variable {A : Type*} [Ring A]

namespace FormalDistribution

/-! ## 1D Multiplication -/

/-- The integer support of a 1D distribution is finite (projection from `Fin 1 → ℤ`). -/
lemma support_ints_unbounded (a : FormalDist1 A) :
    {k : ℤ | a.coeff (fun _ => k) ≠ 0}.Finite :=
  (a.support_finite.image (fun idx : Fin 1 → ℤ => idx 0)).subset
    fun k hk => ⟨fun _ => k, hk, rfl⟩

/-- The convolution support at index `n` is finite for distributions with finite support. -/
lemma convolution_support_finite_1d (a b : FormalDist1 A) (n : ℤ) :
    {k : ℤ | a.coeff (fun _ => k) ≠ 0 ∧ b.coeff (fun _ => n - k) ≠ 0}.Finite :=
  (support_ints_unbounded a).subset fun _ hk => hk.1

/-- Convolution coefficient for the product of 1D formal distributions. -/
noncomputable def mulCoeff1d (a b : FormalDist1 A) (n : ℤ) : A :=
  Finset.sum (convolution_support_finite_1d a b n).toFinset
    (fun k => a.coeff (fun _ => k) * b.coeff (fun _ => n - k))

/-- For any lower bound, the integer support of a 1D distribution above that bound is finite. -/
lemma support_ints_finite (a : FormalDist1 A) (bound_val : ℤ) :
    {k : ℤ | k ≥ bound_val ∧ a.coeff (fun _ => k) ≠ 0}.Finite :=
  (support_ints_unbounded a).subset fun _ hk => hk.2

/-- The support of the product above any bound is finite. -/
lemma mul_support_finite_1d (a b : FormalDist1 A) (bound : ℤ) :
    {n : ℤ | n ≥ bound ∧ mulCoeff1d a b n ≠ 0}.Finite := by
  let k_threshold : ℤ := bound / 2
  let m_threshold : ℤ := bound / 2
  have Ka_finite := support_ints_finite a k_threshold
  have Kb_finite := support_ints_finite b m_threshold
  have h_subset : {n : ℤ | n ≥ bound ∧ mulCoeff1d a b n ≠ 0} ⊆
                  {n : ℤ | ∃ k m : ℤ, (k ≥ k_threshold ∨ m ≥ m_threshold) ∧
                                       a.coeff (fun _ => k) ≠ 0 ∧
                                       b.coeff (fun _ => m) ≠ 0 ∧
                                       n = k + m} := by
    intro n ⟨hn_bound, hn_ne⟩
    unfold mulCoeff1d at hn_ne
    have ⟨k, hk_mem, hk_ne⟩ : ∃ k ∈ (convolution_support_finite_1d a b n).toFinset,
        a.coeff (fun _ => k) * b.coeff (fun _ => n - k) ≠ 0 := by
      by_contra h; push_neg at h; exact hn_ne (Finset.sum_eq_zero h)
    rw [Set.Finite.mem_toFinset] at hk_mem
    obtain ⟨hak, hbk⟩ := hk_mem
    use k, n - k
    refine ⟨?_, hak, hbk, by ring⟩
    by_contra h_neither
    push_neg at h_neither
    have : n < k_threshold + m_threshold := by omega
    have : n < bound := by omega
    omega
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
  · have : {n : ℤ | n ≥ bound ∧ ∃ k m : ℤ, k ≥ k_threshold ∧ a.coeff (fun _ => k) ≠ 0 ∧
                                 b.coeff (fun _ => m) ≠ 0 ∧ n = k + m} ⊆
           ⋃ k ∈ {k : ℤ | k ≥ k_threshold ∧ a.coeff (fun _ => k) ≠ 0},
             {n : ℤ | n ≥ bound ∧ ∃ m : ℤ, b.coeff (fun _ => m) ≠ 0 ∧ n = k + m} := by
      intro n ⟨hn_ge, k, m, hk, hak, hbm, hn_eq⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      use k, ⟨hk, hak⟩, hn_ge, m, hbm, hn_eq
    apply Set.Finite.subset _ this
    apply Set.Finite.biUnion Ka_finite
    intro k hk
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

/-- Multiplication of 1D formal distributions via Cauchy product. -/
noncomputable instance : Mul (FormalDist1 A) where
  mul a b := ⟨
    fun idx => mulCoeff1d a b (idx 0),
    by
      have ha_int := support_ints_unbounded a
      have hb_int := support_ints_unbounded b
      have h_support : {n : ℤ | mulCoeff1d a b n ≠ 0}.Finite := by
        refine (ha_int.biUnion fun k _ =>
          (hb_int.image (· + k)).subset fun n hn => ⟨n - k, hn, by ring⟩).subset ?_
        intro n hn; unfold mulCoeff1d at hn
        have ⟨k, _, hk_ne⟩ : ∃ k ∈ (convolution_support_finite_1d a b n).toFinset,
            a.coeff (fun _ => k) * b.coeff (fun _ => n - k) ≠ 0 := by
          by_contra h; push_neg at h; exact hn (Finset.sum_eq_zero h)
        simp only [Set.mem_iUnion, Set.mem_setOf]
        exact ⟨k, fun h => hk_ne (by simp [h]), fun h => hk_ne (by simp [h])⟩
      exact (h_support.image fun n => fun _ : Fin 1 => n).subset
        fun idx hne => ⟨idx 0, hne, by funext i; fin_cases i; rfl⟩
  ⟩

/-! ### Properties of 1D multiplication -/

/-- The coefficient of a product at index `n` is the convolution sum. -/
theorem mul_coeff (a b : FormalDist1 A) (n : ℤ) :
    (a * b).coeff (fun _ => n) = mulCoeff1d a b n := by
  rfl

/-- Right distributivity: `(a + b) * c = a * c + b * c`. -/
theorem add_mul (a b c : FormalDist1 A) : (a + b) * c = a * c + b * c := by
  ext idx
  show mulCoeff1d (a + b) c (idx 0) = mulCoeff1d a c (idx 0) + mulCoeff1d b c (idx 0)
  unfold mulCoeff1d
  let n := idx 0
  let s_ab := (convolution_support_finite_1d (a + b) c n).toFinset
  let s_a := (convolution_support_finite_1d a c n).toFinset
  let s_b := (convolution_support_finite_1d b c n).toFinset
  let s_union := s_a ∪ s_b
  have lhs_ext : ∑ k ∈ s_ab, (a + b).coeff (fun _ => k) * c.coeff (fun _ => n - k)
               = ∑ k ∈ s_union, (a + b).coeff (fun _ => k) * c.coeff (fun _ => n - k) := by
    refine Finset.sum_subset ?_ ?_
    · intro k hk
      simp only [s_ab, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
      simp only [s_union, Finset.mem_union, s_a, s_b, Set.Finite.mem_toFinset, Set.mem_setOf]
      by_contra h; push_neg at h
      exact hk.1 (show (a + b).coeff (fun _ => k) = 0 by
        change a.coeff _ + b.coeff _ = 0
        rw [show a.coeff (fun _ => k) = 0 from by_contra fun ha => hk.2 (h.1 ha)]
        rw [show b.coeff (fun _ => k) = 0 from by_contra fun hb => hk.2 (h.2 hb)]
        exact zero_add 0)
    · intro k _ hk
      simp only [s_ab, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
      rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  rw [lhs_ext]
  conv_lhs => arg 2; ext k
              rw [show (a + b).coeff (fun _ => k) = a.coeff (fun _ => k) + b.coeff (fun _ => k) by rfl]
  simp only [_root_.add_mul, Finset.sum_add_distrib]
  congr 1
  · refine (Finset.sum_subset Finset.subset_union_left ?_).symm
    intro k _ hk
    simp only [s_a, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
    rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  · refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro k _ hk
    simp only [s_b, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
    rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]

/-- Left distributivity: `a * (b + c) = a * b + a * c`. -/
theorem mul_add (a b c : FormalDist1 A) : a * (b + c) = a * b + a * c := by
  ext idx
  show mulCoeff1d a (b + c) (idx 0) = mulCoeff1d a b (idx 0) + mulCoeff1d a c (idx 0)
  unfold mulCoeff1d
  let n := idx 0
  let s_bc := (convolution_support_finite_1d a (b + c) n).toFinset
  let s_b := (convolution_support_finite_1d a b n).toFinset
  let s_c := (convolution_support_finite_1d a c n).toFinset
  let s_union := s_b ∪ s_c
  have lhs_ext : ∑ k ∈ s_bc, a.coeff (fun _ => k) * (b + c).coeff (fun _ => n - k)
               = ∑ k ∈ s_union, a.coeff (fun _ => k) * (b + c).coeff (fun _ => n - k) := by
    refine Finset.sum_subset ?_ ?_
    · intro k hk
      simp only [s_bc, Set.Finite.mem_toFinset, Set.mem_setOf] at hk
      simp only [s_union, Finset.mem_union, s_b, s_c, Set.Finite.mem_toFinset, Set.mem_setOf]
      by_contra h; push_neg at h
      exact hk.2 (show (b + c).coeff (fun _ => n - k) = 0 by
        change b.coeff _ + c.coeff _ = 0; simp [h.1 hk.1, h.2 hk.1])
    · intro k _ hk
      simp only [s_bc, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
      rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  rw [lhs_ext]
  conv_lhs => arg 2; ext k
              rw [show (b + c).coeff (fun _ => n - k) = b.coeff (fun _ => n - k) + c.coeff (fun _ => n - k) by rfl]
  simp_rw [_root_.mul_add, Finset.sum_add_distrib]
  congr 1
  · refine (Finset.sum_subset Finset.subset_union_left ?_).symm
    intro k _ hk
    simp only [s_b, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
    rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  · refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro k _ hk
    simp only [s_c, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
    rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]

/-- Scalar multiplication commutes with multiplication from the left. -/
theorem smul_mul (r : A) (a b : FormalDist1 A) : (r • a) * b = r • (a * b) := by
  ext idx
  show mulCoeff1d (r • a) b (idx 0) = r • mulCoeff1d a b (idx 0)
  unfold mulCoeff1d
  let n := idx 0
  let s_ra := (convolution_support_finite_1d (r • a) b n).toFinset
  let s_a := (convolution_support_finite_1d a b n).toFinset
  let s_union := s_ra ∪ s_a
  have lhs_ext : ∑ k ∈ s_ra, (r • a).coeff (fun _ => k) * b.coeff (fun _ => n - k)
               = ∑ k ∈ s_union, (r • a).coeff (fun _ => k) * b.coeff (fun _ => n - k) :=
    Finset.sum_subset Finset.subset_union_left fun k _ hk => by
      simp only [s_ra, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
      rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  have rhs_ext : r • ∑ k ∈ s_a, a.coeff (fun _ => k) * b.coeff (fun _ => n - k)
               = ∑ k ∈ s_union, r • (a.coeff (fun _ => k) * b.coeff (fun _ => n - k)) := by
    rw [Finset.smul_sum]; exact Finset.sum_subset Finset.subset_union_right fun k _ hk => by
      simp only [s_a, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
      rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  rw [lhs_ext, rhs_ext]; congr 1; ext k
  simp only [show (r • a).coeff (fun _ => k) = r • a.coeff (fun _ => k) by rfl, smul_mul_assoc]

/-- Scalar multiplication commutes with multiplication from the right (commutative ring). -/
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
               = ∑ k ∈ s_union, a.coeff (fun _ => k) * (r • b).coeff (fun _ => n - k) :=
    Finset.sum_subset Finset.subset_union_left fun k _ hk => by
      simp only [s_rb, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
      rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  have rhs_ext : r • ∑ k ∈ s_b, a.coeff (fun _ => k) * b.coeff (fun _ => n - k)
               = ∑ k ∈ s_union, r • (a.coeff (fun _ => k) * b.coeff (fun _ => n - k)) := by
    rw [Finset.smul_sum]; exact Finset.sum_subset Finset.subset_union_right fun k _ hk => by
      simp only [s_b, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
      rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  rw [lhs_ext, rhs_ext]; congr 1; ext k
  show a.coeff _ * (r • b.coeff _) = r • (a.coeff _ * b.coeff _)
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm (a.coeff _) r, mul_assoc]

/-- Multiplication by zero from the left. -/
theorem zero_mul (a : FormalDist1 A) : (0 : FormalDist1 A) * a = 0 := by
  ext idx
  show mulCoeff1d 0 a (idx 0) = 0
  unfold mulCoeff1d
  apply Finset.sum_eq_zero
  intro k _
  show (0 : FormalDist1 A).coeff (fun _ => k) * a.coeff (fun _ => idx 0 - k) = 0
  rw [show (0 : FormalDist1 A).coeff (fun _ => k) = 0 by rfl]
  exact MulZeroClass.zero_mul _

/-- Multiplication by zero from the right. -/
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

/-! ## 2D Multiplication Infrastructure -/

namespace FormalDistribution

section CommRing
variable {A : Type*} [CommRing A]

/-- Cauchy product coefficient for 2D formal distributions. -/
noncomputable def mulCoeff2d (a b : FormalDist2 A) (n m : ℤ) : A :=
  let support := {(k, l) : ℤ × ℤ | a.coeff (fun i => if i = 0 then k else l) ≠ 0 ∧
                                     b.coeff (fun i => if i = 0 then n - k else m - l) ≠ 0}
  (convolution_support_finite_2d a b n m).toFinset.sum
    fun (k, l) => a.coeff (fun i => if i = 0 then k else l) * b.coeff (fun i => if i = 0 then n - k else m - l)
where
  /-- The set of `(k,l)` contributing to the 2D convolution at `(n,m)` is finite. -/
  convolution_support_finite_2d (a b : FormalDist2 A) (n m : ℤ) :
      {(k, l) : ℤ × ℤ | a.coeff (fun i => if i = 0 then k else l) ≠ 0 ∧
                         b.coeff (fun i => if i = 0 then n - k else m - l) ≠ 0}.Finite := by
    have ha := a.support_finite
    let f : (Fin 2 → ℤ) → ℤ × ℤ := fun idx => (idx 0, idx 1)
    have ha_prod := Set.Finite.image f ha
    apply Set.Finite.subset ha_prod
    intro ⟨k, l⟩ ⟨hak, _⟩
    use (fun i => if i = 0 then k else l)
    exact ⟨hak, rfl⟩

/-- Support above given bounds is finite for 2D distributions. -/
lemma support_pairs_finite (a : FormalDist2 A) (bound0 bound1 : ℤ) :
    {p : ℤ × ℤ | p.1 ≥ bound0 ∧ p.2 ≥ bound1 ∧ a.coeff (fun i => if i = 0 then p.1 else p.2) ≠ 0}.Finite := by
  have ha := a.support_finite
  let f : (Fin 2 → ℤ) → ℤ × ℤ := fun idx => (idx 0, idx 1)
  have ha_prod := Set.Finite.image f ha
  apply Set.Finite.subset ha_prod
  intro ⟨n, m⟩ ⟨_, _, ha_nm⟩
  use (fun i => if i = 0 then n else m)
  exact ⟨ha_nm, by simp [f]⟩

/-- The support of the 2D product above any bound is finite. -/
lemma mul_support_finite_2d (a b : FormalDist2 A) (bound0 bound1 : ℤ) :
    {(n, m) : ℤ × ℤ | n ≥ bound0 ∧ m ≥ bound1 ∧ mulCoeff2d a b n m ≠ 0}.Finite := by
  have ha := a.support_finite
  let f : (Fin 2 → ℤ) → ℤ × ℤ := fun idx => (idx 0, idx 1)
  have ha_prod := Set.Finite.image f ha
  let a_support_prod : Set (ℤ × ℤ) := {kl : ℤ × ℤ | a.coeff (fun i => if i = 0 then kl.1 else kl.2) ≠ 0}
  have ha_support_prod : a_support_prod.Finite := by
    apply Set.Finite.subset ha_prod
    intro ⟨k, l⟩ hkl
    use (fun i => if i = 0 then k else l)
    exact ⟨hkl, rfl⟩
  have : {p : ℤ × ℤ | p.1 ≥ bound0 ∧ p.2 ≥ bound1 ∧ mulCoeff2d a b p.1 p.2 ≠ 0} ⊆
         ⋃ kl ∈ a_support_prod,
           {p : ℤ × ℤ | p.1 ≥ bound0 ∧ p.2 ≥ bound1 ∧
                        b.coeff (fun i => if i = 0 then p.1 - kl.1 else p.2 - kl.2) ≠ 0} := by
    intro ⟨n, m⟩ ⟨hn_ge, hm_ge, hnm_ne⟩
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
  apply Set.Finite.biUnion ha_support_prod
  intro ⟨k, l⟩ _
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

/-- Multiplication of 2D formal distributions. -/
noncomputable instance : Mul (FormalDist2 A) where
  mul a b := ⟨
    fun idx => mulCoeff2d a b (idx 0) (idx 1),
    by
      have ha := a.support_finite
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

/-- Coefficient of the 2D product. -/
theorem mul_coeff_2d (a b : FormalDist2 A) (n m : ℤ) :
    (a * b).coeff (fun i => if i = 0 then n else m) = mulCoeff2d a b n m := by
  rfl

/-- Multiplication by zero from the left (2D). -/
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

/-- Multiplication by zero from the right (2D). -/
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

/-- Right distributivity for 2D: `(a + b) * c = a * c + b * c`. -/
theorem add_mul_2d (a b c : FormalDist2 A) : (a + b) * c = a * c + b * c := by
  ext idx
  show mulCoeff2d (a + b) c (idx 0) (idx 1) =
       mulCoeff2d a c (idx 0) (idx 1) + mulCoeff2d b c (idx 0) (idx 1)
  unfold mulCoeff2d mulCoeff2d.convolution_support_finite_2d
  let s_ab := (mulCoeff2d.convolution_support_finite_2d (a + b) c (idx 0) (idx 1)).toFinset
  let s_a := (mulCoeff2d.convolution_support_finite_2d a c (idx 0) (idx 1)).toFinset
  let s_b := (mulCoeff2d.convolution_support_finite_2d b c (idx 0) (idx 1)).toFinset
  let s_union := s_a ∪ s_b
  have lhs_ext : ∑ p ∈ s_ab, (a + b).coeff (fun i => if i = 0 then p.1 else p.2) *
                              c.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
                 ∑ p ∈ s_union, (a + b).coeff (fun i => if i = 0 then p.1 else p.2) *
                                c.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) := by
    refine Finset.sum_subset ?_ ?_
    · intro ⟨k, l⟩ hkl
      simp only [s_ab, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl
      simp only [s_union, Finset.mem_union, s_a, s_b, Set.Finite.mem_toFinset, Set.mem_setOf]
      by_contra h; push_neg at h
      exact hkl.1 (show (a + b).coeff (fun i => if i = 0 then k else l) = 0 by
        change a.coeff _ + b.coeff _ = 0
        rw [show a.coeff _ = 0 from by_contra fun ha => hkl.2 (h.1 ha)]
        rw [show b.coeff _ = 0 from by_contra fun hb => hkl.2 (h.2 hb)]
        exact zero_add 0)
    · intro ⟨k, l⟩ _ hkl
      simp only [s_ab, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl; rw [not_and_or] at hkl
      rcases hkl.imp not_not.mp not_not.mp with h | h <;> simp [h]
  rw [lhs_ext]
  conv_lhs => arg 2; ext x
              rw [show (a + b).coeff (fun i => if i = 0 then x.1 else x.2) =
                       a.coeff (fun i => if i = 0 then x.1 else x.2) +
                       b.coeff (fun i => if i = 0 then x.1 else x.2) by rfl, _root_.add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · refine (Finset.sum_subset Finset.subset_union_left ?_).symm
    intro ⟨k, l⟩ _ hkl
    simp only [s_a, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl; rw [not_and_or] at hkl
    rcases hkl.imp not_not.mp not_not.mp with h | h <;> simp [h]
  · refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro ⟨k, l⟩ _ hkl
    simp only [s_b, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl; rw [not_and_or] at hkl
    rcases hkl.imp not_not.mp not_not.mp with h | h <;> simp [h]

/-- Left distributivity for 2D: `a * (b + c) = a * b + a * c`. -/
theorem mul_add_2d (a b c : FormalDist2 A) : a * (b + c) = a * b + a * c := by
  ext idx
  show mulCoeff2d a (b + c) (idx 0) (idx 1) =
       mulCoeff2d a b (idx 0) (idx 1) + mulCoeff2d a c (idx 0) (idx 1)
  unfold mulCoeff2d mulCoeff2d.convolution_support_finite_2d
  let s_a_bc := (mulCoeff2d.convolution_support_finite_2d a (b + c) (idx 0) (idx 1)).toFinset
  let s_ab := (mulCoeff2d.convolution_support_finite_2d a b (idx 0) (idx 1)).toFinset
  let s_ac := (mulCoeff2d.convolution_support_finite_2d a c (idx 0) (idx 1)).toFinset
  let s_union := s_ab ∪ s_ac
  have lhs_ext : ∑ p ∈ s_a_bc, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                (b + c).coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
                 ∑ p ∈ s_union, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                (b + c).coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) := by
    refine Finset.sum_subset ?_ ?_
    · intro ⟨k, l⟩ hkl
      simp only [s_a_bc, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl
      simp only [s_union, Finset.mem_union, s_ab, s_ac, Set.Finite.mem_toFinset, Set.mem_setOf]
      by_contra h; push_neg at h
      have ha : a.coeff (fun i => if i = 0 then k else l) ≠ 0 := fun h' => by simp [h'] at hkl
      exact hkl.2 (show (b + c).coeff _ = 0 by change b.coeff _ + c.coeff _ = 0; simp [h.1 ha, h.2 ha])
    · intro ⟨k, l⟩ _ hkl
      simp only [s_a_bc, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl; rw [not_and_or] at hkl
      rcases hkl.imp not_not.mp not_not.mp with h | h <;> simp [h]
  rw [lhs_ext]
  conv_lhs => arg 2; ext x
              rw [show (b + c).coeff (fun i => if i = 0 then idx 0 - x.1 else idx 1 - x.2) =
                       b.coeff (fun i => if i = 0 then idx 0 - x.1 else idx 1 - x.2) +
                       c.coeff (fun i => if i = 0 then idx 0 - x.1 else idx 1 - x.2) by rfl, _root_.mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · refine (Finset.sum_subset Finset.subset_union_left ?_).symm
    intro ⟨k, l⟩ _ hkl
    simp only [s_ab, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl; rw [not_and_or] at hkl
    rcases hkl.imp not_not.mp not_not.mp with h | h <;> simp [h]
  · refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro ⟨k, l⟩ _ hkl
    simp only [s_ac, Set.Finite.mem_toFinset, Set.mem_setOf] at hkl; rw [not_and_or] at hkl
    rcases hkl.imp not_not.mp not_not.mp with h | h <;> simp [h]

/-- Scalar multiplication commutes with left 2D multiplication. -/
theorem smul_mul_2d (r : A) (a b : FormalDist2 A) : (r • a) * b = r • (a * b) := by
  ext idx
  show mulCoeff2d (r • a) b (idx 0) (idx 1) = r * mulCoeff2d a b (idx 0) (idx 1)
  unfold mulCoeff2d mulCoeff2d.convolution_support_finite_2d
  let s_ra := (mulCoeff2d.convolution_support_finite_2d (r • a) b (idx 0) (idx 1)).toFinset
  let s_a := (mulCoeff2d.convolution_support_finite_2d a b (idx 0) (idx 1)).toFinset
  let s_union := s_ra ∪ s_a
  have lhs_ext : ∑ p ∈ s_ra, (r • a).coeff (fun i => if i = 0 then p.1 else p.2) *
                              b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
                 ∑ p ∈ s_union, (r • a).coeff (fun i => if i = 0 then p.1 else p.2) *
                                b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) :=
    Finset.sum_subset Finset.subset_union_left fun ⟨k, l⟩ _ hk => by
      simp only [s_ra, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
      rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  have rhs_ext : r • ∑ p ∈ s_a, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                 b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
                 ∑ p ∈ s_union, r • (a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                     b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2)) := by
    rw [Finset.smul_sum]; exact Finset.sum_subset Finset.subset_union_right fun ⟨k, l⟩ _ hk => by
      simp only [s_a, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
      rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  rw [lhs_ext]
  show ∑ p ∈ s_union, (r • a).coeff (fun i => if i = 0 then p.1 else p.2) *
                       b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
       r • ∑ p ∈ s_a, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                      b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2)
  rw [rhs_ext]; congr 1; ext ⟨k, l⟩
  simp only [show (r • a).coeff (fun i => if i = 0 then k else l) =
                  r • a.coeff (fun i => if i = 0 then k else l) by rfl, smul_mul_assoc]

/-- Scalar multiplication commutes with right 2D multiplication. -/
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
                                (r • b).coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) :=
    Finset.sum_subset Finset.subset_union_left fun ⟨k, l⟩ _ hk => by
      simp only [s_rb, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
      rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  have rhs_ext : r • ∑ p ∈ s_b, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                 b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
                 ∑ p ∈ s_union, r • (a.coeff (fun i => if i = 0 then p.1 else p.2) *
                                     b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2)) := by
    rw [Finset.smul_sum]; exact Finset.sum_subset Finset.subset_union_right fun ⟨k, l⟩ _ hk => by
      simp only [s_b, Set.Finite.mem_toFinset, Set.mem_setOf] at hk; rw [not_and_or] at hk
      rcases hk.imp not_not.mp not_not.mp with h | h <;> simp [h]
  rw [lhs_ext]
  show ∑ p ∈ s_union, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                       (r • b).coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2) =
       r • ∑ p ∈ s_b, a.coeff (fun i => if i = 0 then p.1 else p.2) *
                      b.coeff (fun i => if i = 0 then idx 0 - p.1 else idx 1 - p.2)
  rw [rhs_ext]; congr 1; ext ⟨k, l⟩
  show a.coeff _ * (r • b.coeff _) = r • (a.coeff _ * b.coeff _)
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm (a.coeff _) r, mul_assoc]

/-! ### Embeddings: 1D → n-variable -/

/-- Embed a 1D distribution into an n-variable distribution at position `i`,
setting all other variables to 0. -/
noncomputable def embedAt {n : ℕ} (i : Fin n) (a : FormalDist1 A) : FormalDistribution A n where
  coeff := fun idx => if ∀ j, j ≠ i → idx j = 0 then a.coeff (fun _ => idx i) else 0
  support_finite := by
    apply (a.support_finite.image (fun k : Fin 1 → ℤ => fun j : Fin n => if j = i then k 0 else 0)).subset
    intro idx hne; simp only [Set.mem_setOf_eq] at hne
    split_ifs at hne with hzero
    · refine ⟨fun _ => idx i, hne, ?_⟩
      ext j; simp only; split_ifs with hj <;> [rw [hj]; exact (hzero j hj).symm]
    · simp at hne

/-- Embed in the first variable (alias for `embedAt 0`). -/
noncomputable abbrev embedFst : FormalDist1 A → FormalDist2 A := embedAt 0

/-- Embed in the second variable (alias for `embedAt 1`). -/
noncomputable abbrev embedSnd : FormalDist1 A → FormalDist2 A := embedAt 1

/-- Coefficient of `FormalDistribution.embedAt`. -/
@[simp] lemma embedAt_coeff {n : ℕ} (i : Fin n) (a : FormalDist1 A) (idx : Fin n → ℤ) :
    (embedAt i a).coeff idx = if ∀ j, j ≠ i → idx j = 0 then a.coeff (fun _ => idx i) else 0 := rfl

/-- For 2-variable embeddings, the condition simplifies to checking a single variable. -/
lemma embedFst_coeff' (a : FormalDist1 A) (idx : Fin 2 → ℤ) :
    (embedFst a).coeff idx = if idx 1 = 0 then a.coeff (fun _ => idx 0) else 0 := by
  simp only [embedFst, embedAt_coeff]
  congr 1; ext; constructor
  · intro h; exact h 1 (by decide)
  · intro h j hj; exact (by fin_cases j <;> [exact absurd rfl hj; exact h])

lemma embedSnd_coeff' (a : FormalDist1 A) (idx : Fin 2 → ℤ) :
    (embedSnd a).coeff idx = if idx 0 = 0 then a.coeff (fun _ => idx 1) else 0 := by
  simp only [embedSnd, embedAt_coeff]
  congr 1; ext; constructor
  · intro h; exact h 0 (by decide)
  · intro h j hj; exact (by fin_cases j <;> [exact h; exact absurd rfl hj])

/-! ### Residue in specific variable -/

/-- Extract the residue at variable `i` from an n-variable distribution,
projecting remaining variables onto variable `j`. -/
noncomputable def residueAtPair {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : FormalDistribution A n) :
    FormalDist1 A where
  coeff := fun idx => a.coeff (fun k => if k = i then -1 else if k = j then idx 0 else 0)
  support_finite := by
    apply (a.support_finite.image (fun f : Fin n → ℤ => fun _ : Fin 1 => f j)).subset
    intro idx hne; simp only [Set.mem_setOf_eq] at hne
    exact ⟨fun k => if k = i then -1 else if k = j then idx 0 else 0,
      hne, by funext k; fin_cases k; simp [hij.symm]⟩

/-- Extract the residue in a specific variable from a 2D distribution (alias). -/
noncomputable abbrev residueAt (i : Fin 2) (a : FormalDist2 A) : FormalDist1 A :=
  residueAtPair i (if i = 0 then 1 else 0) (by fin_cases i <;> decide) a

end CommRing

end FormalDistribution
