/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FormalDistribution.Basic
import FormalDistribution.Binomial
import Mathlib.Data.Int.Interval

/-!
# Expansion Operators

This file defines the expansion operators `i_{z,w}` and `i_{w,z}` acting on `(z-w)^k`
for integer `k`, and proves that derivatives commute with these operators.

## Main definitions

* `expansion_izw` - the expansion `i_{z,w}(z-w)^k = ∑_{j≥0} C(k,j)(-1)^j z^{k-j} w^j`
* `expansion_iwz` - the expansion `i_{w,z}(z-w)^k = (-1)^k ∑_{j≥0} C(k,j)(-1)^j z^j w^{k-j}`

## Main results

* `deriv_fst_expansion_izw` - `∂_z i_{z,w}(z-w)^k = k · i_{z,w}(z-w)^{k-1}`
* `deriv_snd_expansion_izw` - `∂_w i_{z,w}(z-w)^k = -k · i_{z,w}(z-w)^{k-1}`
* `deriv_fst_expansion_iwz` - `∂_z i_{w,z}(z-w)^k = k · i_{w,z}(z-w)^{k-1}`
* `deriv_snd_expansion_iwz` - `∂_w i_{w,z}(z-w)^k = -k · i_{w,z}(z-w)^{k-1}`

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Section 1.2, Proposition 1.2.6
-/

variable {A : Type*} [Ring A]

/-! ## Expansion operators -/

/-- Expansion `i_{z,w}(z-w)^k` as a 2-variable generalized formal distribution.

`i_{z,w}(z-w)^k = ∑_{j≥0} C(k,j)(-1)^j z^{k-j} w^j`

Coefficient at `(n,m)`: `C(k,m)(-1)^m` when `n+m=k` and `m≥0`, else `0`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.2.1
-/
noncomputable def expansion_izw (k : ℤ) : GenFormalDist2 A where
  coeff := fun idx =>
    if idx 0 + idx 1 = k ∧ idx 1 ≥ 0
    then ((intBinomial k (idx 1).toNat * (-1) ^ (idx 1).toNat : ℤ) : A)
    else 0
  support_finite := fun bound => by
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

/-- Coefficient of `expansion_izw k` at index `idx`. -/
@[simp]
theorem expansion_izw_coeff (k : ℤ) (idx : Fin 2 → ℤ) :
    (expansion_izw k : GenFormalDist2 A).coeff idx =
    if idx 0 + idx 1 = k ∧ idx 1 ≥ 0
    then ((intBinomial k (idx 1).toNat * (-1) ^ (idx 1).toNat : ℤ) : A)
    else 0 := rfl

/-- Expansion `i_{w,z}(z-w)^k` as a 2-variable generalized formal distribution.

`i_{w,z}(z-w)^k = (-1)^k ∑_{j≥0} C(k,j)(-1)^j z^j w^{k-j}`

Coefficient at `(n,m)`: `C(k,n)(-1)^m` when `n+m=k` and `n≥0`, else `0`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.2.1
-/
noncomputable def expansion_iwz (k : ℤ) : GenFormalDist2 A where
  coeff := fun idx =>
    if idx 0 + idx 1 = k ∧ idx 0 ≥ 0
    then ((intBinomial k (idx 0).toNat * (-1) ^ (k - idx 0).natAbs : ℤ) : A)
    else 0
  support_finite := fun bound => by
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

/-- Coefficient of `expansion_iwz k` at index `idx`. -/
@[simp]
theorem expansion_iwz_coeff (k : ℤ) (idx : Fin 2 → ℤ) :
    (expansion_iwz k : GenFormalDist2 A).coeff idx =
    if idx 0 + idx 1 = k ∧ idx 0 ≥ 0
    then ((intBinomial k (idx 0).toNat * (-1) ^ (k - idx 0).natAbs : ℤ) : A)
    else 0 := rfl

/-! ### Proposition 1.2.6: Derivatives commute with expansion operators -/

/-- Proposition 1.2.6(a): `∂_z i_{z,w}(z-w)^k = k · i_{z,w}(z-w)^{k-1}`. -/
theorem deriv_fst_expansion_izw (k : ℤ) :
    GeneralizedFormalDistribution.deriv (expansion_izw k : GenFormalDist2 A) 0 =
    (k : A) • expansion_izw (k - 1) := by
  ext idx
  show (idx 0 + 1 : ℤ) • (expansion_izw k : GenFormalDist2 A).coeff (Function.update idx 0 (idx 0 + 1))
     = (k : A) • (expansion_izw (k - 1) : GenFormalDist2 A).coeff idx
  rw [expansion_izw_coeff, expansion_izw_coeff]
  simp only [update_eval_same, update_eval_diff idx 0 1 (idx 0 + 1) (by decide)]
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

/-- Proposition 1.2.6(b): `∂_w i_{z,w}(z-w)^k = -k · i_{z,w}(z-w)^{k-1}`. -/
theorem deriv_snd_expansion_izw (k : ℤ) :
    GeneralizedFormalDistribution.deriv (expansion_izw k : GenFormalDist2 A) 1 =
    (-k : A) • expansion_izw (k - 1) := by
  ext idx
  show (idx 1 + 1 : ℤ) • (expansion_izw k : GenFormalDist2 A).coeff (Function.update idx 1 (idx 1 + 1))
     = (-k : A) • (expansion_izw (k - 1) : GenFormalDist2 A).coeff idx
  rw [expansion_izw_coeff, expansion_izw_coeff]
  simp only [update_eval_same, update_eval_diff idx 1 0 (idx 1 + 1) (by decide)]
  by_cases hcond : idx 0 + idx 1 = k - 1 ∧ idx 1 ≥ 0
  · rw [if_pos ⟨by omega, by omega⟩, if_pos hcond]
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
  · rw [if_neg hcond, smul_zero]
    by_cases hlhs : idx 0 + (idx 1 + 1) = k ∧ idx 1 + 1 ≥ 0
    · rw [if_pos hlhs]
      have : (idx 1 + 1 : ℤ) = 0 := by omega
      rw [this, zero_smul]
    · rw [if_neg hlhs, smul_zero]

/-- `(-1)^|a+1| = -(-1)^|a|` for all integers `a`. -/
theorem neg_one_pow_natAbs_succ (a : ℤ) :
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

/-- Proposition 1.2.6(c): `∂_z i_{w,z}(z-w)^k = k · i_{w,z}(z-w)^{k-1}`. -/
theorem deriv_fst_expansion_iwz (k : ℤ) :
    GeneralizedFormalDistribution.deriv (expansion_iwz k : GenFormalDist2 A) 0 =
    (k : A) • expansion_iwz (k - 1) := by
  ext idx
  show (idx 0 + 1 : ℤ) • (expansion_iwz k : GenFormalDist2 A).coeff (Function.update idx 0 (idx 0 + 1))
     = (k : A) • (expansion_iwz (k - 1) : GenFormalDist2 A).coeff idx
  rw [expansion_iwz_coeff, expansion_iwz_coeff]
  simp only [update_eval_same, update_eval_diff idx 0 1 (idx 0 + 1) (by decide)]
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
  · rw [if_neg hcond, smul_zero]
    by_cases hlhs : (idx 0 + 1) + idx 1 = k ∧ idx 0 + 1 ≥ 0
    · rw [if_pos hlhs]
      have : (idx 0 + 1 : ℤ) = 0 := by omega
      rw [this, zero_smul]
    · rw [if_neg hlhs, smul_zero]

/-- Proposition 1.2.6(d): `∂_w i_{w,z}(z-w)^k = -k · i_{w,z}(z-w)^{k-1}`. -/
theorem deriv_snd_expansion_iwz (k : ℤ) :
    GeneralizedFormalDistribution.deriv (expansion_iwz k : GenFormalDist2 A) 1 =
    (-k : A) • expansion_iwz (k - 1) := by
  ext idx
  show (idx 1 + 1 : ℤ) • (expansion_iwz k : GenFormalDist2 A).coeff (Function.update idx 1 (idx 1 + 1))
     = (-k : A) • (expansion_iwz (k - 1) : GenFormalDist2 A).coeff idx
  rw [expansion_iwz_coeff, expansion_iwz_coeff]
  simp only [update_eval_same, update_eval_diff idx 1 0 (idx 1 + 1) (by decide)]
  by_cases hcond : idx 0 + idx 1 = k - 1 ∧ idx 0 ≥ 0
  · rw [if_pos ⟨by omega, hcond.2⟩, if_pos hcond]
    simp only [zsmul_eq_mul, smul_eq_mul, ← Int.cast_neg, ← Int.cast_mul]
    congr 1
    have hm : (↑((idx 0).toNat) : ℤ) = idx 0 := Int.toNat_of_nonneg hcond.2
    have h_key := intBinomial_mul_sub k (idx 0).toNat
    have h_sign := neg_one_pow_natAbs_succ ((k - 1) - idx 0)
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

/-! ### Remark 1.2.4: Expansion equality for non-negative exponents -/

/-- Remark 1.2.4: For non-negative `k`, both expansion operators agree.

When `k ≥ 0`, `(z-w)^k` is a polynomial and both `i_{z,w}` and `i_{w,z}` produce
the same finite expansion. -/
theorem expansion_izw_eq_iwz_of_nonneg (k : ℕ) :
    (expansion_izw (↑k : ℤ) : GenFormalDist2 A) = expansion_iwz ↑k := by
  ext idx
  simp only [expansion_izw_coeff, expansion_iwz_coeff]
  -- If the indices don't sum to k, both sides are zero
  by_cases hsum : idx 0 + idx 1 = ↑k
  · -- On the diagonal n + m = k
    by_cases hm : idx 1 ≥ 0
    · by_cases hn : idx 0 ≥ 0
      · -- Both non-negative: compare using Nat.choose symmetry
        rw [if_pos ⟨hsum, hm⟩, if_pos ⟨hsum, hn⟩]
        have h_sign : (↑k - idx 0).natAbs = (idx 1).toNat := by omega
        rw [h_sign]
        congr 1
        -- intBinomial ↑k m = ↑(Nat.choose k m) for natural k
        have h1 : intBinomial (↑k) (idx 1).toNat = ↑(Nat.choose k (idx 1).toNat) := rfl
        have h2 : intBinomial (↑k) (idx 0).toNat = ↑(Nat.choose k (idx 0).toNat) := rfl
        rw [h1, h2]
        congr 1
        have hsym := Nat.choose_symm (show (idx 1).toNat ≤ k by omega)
        rw [show k - (idx 1).toNat = (idx 0).toNat from by omega] at hsym
        exact_mod_cast hsym.symm
      · -- idx 0 < 0, so idx 1 > k: Nat.choose k m = 0 for m > k
        push_neg at hn
        rw [if_pos ⟨hsum, hm⟩, if_neg (by intro ⟨_, h⟩; exact absurd h (by omega))]
        have h1 : intBinomial (↑k) (idx 1).toNat = ↑(Nat.choose k (idx 1).toNat) := rfl
        rw [h1, Nat.choose_eq_zero_of_lt (by omega : k < (idx 1).toNat)]
        simp
    · push_neg at hm
      by_cases hn : idx 0 ≥ 0
      · -- idx 1 < 0, so idx 0 > k: Nat.choose k n = 0 for n > k
        rw [if_neg (by intro ⟨_, h⟩; exact absurd h (by omega)), if_pos ⟨hsum, hn⟩]
        have h2 : intBinomial (↑k) (idx 0).toNat = ↑(Nat.choose k (idx 0).toNat) := rfl
        rw [h2, Nat.choose_eq_zero_of_lt (by omega : k < (idx 0).toNat)]
        simp
      · -- Both negative: impossible since sum = k ≥ 0
        push_neg at hn; omega
  · -- Off diagonal: both zero
    rw [if_neg (by intro ⟨h, _⟩; exact hsum h),
        if_neg (by intro ⟨h, _⟩; exact hsum h)]
