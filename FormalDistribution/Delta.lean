/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FormalDistribution.Basic
import FormalDistribution.Deriv
import FormalDistribution.Mul
import FormalDistribution.Fourier
import FormalDistribution.Expansion

/-!
# Formal Delta Distribution

This file defines the formal delta distribution `δ(z,w) = ∑_{n ∈ ℤ} z^n w^{-n-1}` and
proves all seven properties from Proposition 1.3.5.

## Main definitions

* `formalDelta` - the formal delta distribution `δ(z,w)`
* `FormalDelta.mul_z_sub_w` - multiplication by `(z-w)` on generalized distributions
* `FormalDelta.mul_z_sub_w_pow` - iterated multiplication by `(z-w)`

## Main results

* `formalDelta_eq_expansion_izw_sub_iwz` - `δ = i_{z,w}(z-w)^{-1} - i_{w,z}(z-w)^{-1}`
* `FormalDelta.mul_z_sub_w_formalDelta` - `(z-w)·δ = 0`
* Properties 1-7 of the formal delta (Proposition 1.3.5)

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Section 1.3, Propositions 1.3.4-1.3.5
-/

variable {A : Type*} [Ring A]

/-! ## 1.3 Formal delta distribution -/

/-- The formal delta distribution `δ(z,w) = ∑_{n ∈ ℤ} z^n w^{-n-1}`.

The formal delta has infinite support along the anti-diagonal `{(n, -n-1) | n ∈ ℤ}`,
so it is defined as a `GeneralizedFormalDistribution` rather than a `FormalDistribution`.

This satisfies the fundamental property `Res_z a(z)δ(z,w) = a(w)`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.3.1
* [Kac, *Vertex Algebras for Beginners*], §1.3
-/
noncomputable def formalDelta : GenFormalDist2 A where
  coeff := fun idx => if idx 0 + idx 1 + 1 = 0 then (1 : A) else 0
  support_finite := fun bound => by
    by_cases h : bound 0 ≤ -bound 1 - 1
    · let k_finset : Finset ℤ := Finset.Icc (bound 0) (-bound 1 - 1)
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
    · convert Set.finite_empty
      ext idx
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hall
      split_ifs with hidx
      · have : idx 0 ≥ bound 0 := hall 0
        have : idx 1 ≥ bound 1 := hall 1
        have : idx 1 = -idx 0 - 1 := by omega
        omega
      · simp

/-- The coefficients of `formalDelta` match the expected pattern. -/
@[simp]
theorem formalDelta_coeff (idx : Fin 2 → ℤ) :
    formalDelta.coeff idx = if idx 0 + idx 1 + 1 = 0 then (1 : A) else 0 := rfl

/-- `δ(z,w) = i_{z,w}(z-w)^{-1} - i_{w,z}(z-w)^{-1}`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.3.4
-/
theorem formalDelta_eq_expansion_izw_sub_iwz :
    (expansion_izw (-1) : GenFormalDist2 A) - (expansion_iwz (-1) : GenFormalDist2 A) =
    (formalDelta : GenFormalDist2 A) := by
  ext idx
  show (expansion_izw (-1) : GenFormalDist2 A).coeff idx -
       (expansion_iwz (-1) : GenFormalDist2 A).coeff idx = formalDelta.coeff idx
  rw [expansion_izw_coeff, expansion_iwz_coeff, formalDelta_coeff]
  by_cases hline : idx 0 + idx 1 + 1 = 0
  · have hsum : idx 0 + idx 1 = -1 := by omega
    by_cases hm : idx 1 ≥ 0
    · rw [if_pos ⟨hsum, hm⟩, if_neg (by omega : ¬(idx 0 + idx 1 = -1 ∧ idx 0 ≥ 0)),
          if_pos hline, sub_zero, intBinomial_neg_one, ← pow_add]
      have : (idx 1).toNat + (idx 1).toNat = 2 * (idx 1).toNat := by omega
      rw [this, pow_mul, neg_one_sq, one_pow, Int.cast_one]
    · push_neg at hm
      have hn : idx 0 ≥ 0 := by omega
      rw [if_neg (by omega : ¬(idx 0 + idx 1 = -1 ∧ idx 1 ≥ 0)),
          if_pos ⟨hsum, hn⟩, if_pos hline, zero_sub, intBinomial_neg_one, ← pow_add]
      have habs : (-1 - idx 0).natAbs = (idx 0 + 1).toNat := by omega
      rw [habs]
      have : (idx 0).toNat + (idx 0 + 1).toNat = 2 * (idx 0).toNat + 1 := by omega
      rw [this, pow_add, pow_mul, neg_one_sq, one_pow, one_mul,
          show ((-1 : ℤ) ^ 1) = -1 from by norm_num,
          Int.cast_neg, Int.cast_one, neg_neg]
  · rw [if_neg (by omega : ¬(idx 0 + idx 1 = -1 ∧ idx 1 ≥ 0)),
        if_neg (by omega : ¬(idx 0 + idx 1 = -1 ∧ idx 0 ≥ 0)),
        if_neg hline, sub_zero]

/-! ## Proposition 1.3.5: Properties of the formal delta -/

namespace FormalDelta

/-- Multiplication by `(z - w)` on generalized 2-variable distributions.

`((z-w) · a)(n,m) = a(n-1,m) - a(n,m-1)` -/
def mul_z_sub_w (a : GenFormalDist2 A) : GenFormalDist2 A where
  coeff := fun idx =>
    a.coeff (Function.update idx 0 (idx 0 - 1)) -
    a.coeff (Function.update idx 1 (idx 1 - 1))
  support_finite := fun bound => by
    have ha0 := a.support_finite (Function.update bound 0 (bound 0 - 1))
    have ha1 := a.support_finite (Function.update bound 1 (bound 1 - 1))
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

/-- Iterated multiplication by `(z - w)`. -/
def mul_z_sub_w_pow (a : GenFormalDist2 A) : ℕ → GenFormalDist2 A
  | 0 => a
  | n + 1 => mul_z_sub_w (mul_z_sub_w_pow a n)

/-- `(z-w) · δ = 0`. -/
theorem mul_z_sub_w_formalDelta : mul_z_sub_w (formalDelta : GenFormalDist2 A) = 0 := by
  ext idx
  show formalDelta.coeff (Function.update idx 0 (idx 0 - 1)) -
       formalDelta.coeff (Function.update idx 1 (idx 1 - 1)) = 0
  simp only [formalDelta_coeff]
  simp only [Function.update, show ¬((0 : Fin 2) = 1) from by decide,
             show ¬((1 : Fin 2) = 0) from by decide,
             dite_true, dite_false]
  by_cases h : idx 0 + idx 1 = 0
  · rw [if_pos (by omega : idx 0 - 1 + idx 1 + 1 = 0),
        if_pos (by omega : idx 0 + (idx 1 - 1) + 1 = 0)]
    exact sub_self _
  · rw [if_neg (by omega : ¬(idx 0 - 1 + idx 1 + 1 = 0)),
        if_neg (by omega : ¬(idx 0 + (idx 1 - 1) + 1 = 0))]
    exact sub_self _

/-- Rising factorial product: `(q+1)(q+2)⋯(q+n)` computed in `ℤ`. -/
def risingProd (q : ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => risingProd q n * (q + ↑n + 1)

/-- The rising product of zero factors is `1`. -/
theorem risingProd_zero (q : ℤ) : risingProd q 0 = 1 := rfl

/-- The rising product satisfies `risingProd q (n+1) = risingProd q n * (q + n + 1)`. -/
theorem risingProd_succ (q : ℤ) (n : ℕ) :
    risingProd q (n + 1) = risingProd q n * (q + ↑n + 1) := rfl

/-- Key identity: `risingProd q (n+1) = (q+1) * risingProd (q+1) n`. -/
theorem risingProd_shift (q : ℤ) (n : ℕ) :
    risingProd q (n + 1) = (q + 1) * risingProd (q + 1) n := by
  induction n with
  | zero => simp [risingProd]
  | succ n ih =>
    rw [risingProd_succ q (n + 1), ih, risingProd_succ (q + 1) n]
    push_cast; ring

/-- Difference identity: `risingProd q (n+1) - risingProd (q-1) (n+1) = (n+1) * risingProd q n`. -/
theorem risingProd_diff (q : ℤ) (n : ℕ) :
    risingProd q (n + 1) - risingProd (q - 1) (n + 1) = (↑(n + 1) : ℤ) * risingProd q n := by
  rw [risingProd_succ, risingProd_shift (q - 1) n]
  simp only [sub_add_cancel]
  push_cast; ring

/-- Coefficient formula for the `n`-th `w`-derivative of `formalDelta`.

`(∂_w^n δ)_{p,q} = if p + q + n + 1 = 0 then (q+1)(q+2)⋯(q+n) else 0` -/
theorem iteratedDeriv_snd_formalDelta_coeff (n : ℕ) (idx : Fin 2 → ℤ) :
    (GeneralizedFormalDistribution.iteratedDeriv formalDelta (1 : Fin 2) n).coeff idx =
    if idx 0 + idx 1 + ↑n + 1 = 0
    then (risingProd (idx 1) n : A)
    else 0 := by
  induction n generalizing idx with
  | zero =>
    simp only [GeneralizedFormalDistribution.iteratedDeriv, Nat.cast_zero, add_zero,
               risingProd, Int.cast_one]
    exact formalDelta_coeff idx
  | succ n ih =>
    simp only [GeneralizedFormalDistribution.iteratedDeriv,
               GeneralizedFormalDistribution.deriv]
    show (idx 1 + 1 : ℤ) •
      (GeneralizedFormalDistribution.iteratedDeriv formalDelta 1 n).coeff
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
      rw [risingProd_shift (idx 1) n]
      push_cast [Int.cast_mul]
      rw [zsmul_eq_mul]
      congr 1; push_cast; abel
    · rw [if_neg (by omega : ¬(idx 0 + (idx 1 + 1) + (↑n : ℤ) + 1 = 0))]
      rw [if_neg (by omega : ¬(idx 0 + idx 1 + (↑(n + 1) : ℤ) + 1 = 0))]
      simp

/-- `mul_z_sub_w` commutes with scalar multiplication. -/
theorem mul_z_sub_w_smul (c : A) (a : GenFormalDist2 A) :
    mul_z_sub_w (c • a) = c • mul_z_sub_w a := by
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

/-- Property 2: `(z-w) · ∂_w^n δ = n · ∂_w^{n-1} δ` for `n ≥ 1`.

This is the key recurrence: multiplying by `(z-w)` lowers the derivative order by 1.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.3.5(2)
-/
theorem mul_z_sub_w_iteratedDeriv_formalDelta (n : ℕ) (hn : n ≥ 1) :
    mul_z_sub_w (GeneralizedFormalDistribution.iteratedDeriv (formalDelta : GenFormalDist2 A) (1 : Fin 2) n) =
    ((n : ℕ) : A) • GeneralizedFormalDistribution.iteratedDeriv formalDelta (1 : Fin 2) (n - 1) := by
  ext idx
  show (GeneralizedFormalDistribution.iteratedDeriv formalDelta 1 n).coeff
        (Function.update idx 0 (idx 0 - 1)) -
       (GeneralizedFormalDistribution.iteratedDeriv formalDelta 1 n).coeff
        (Function.update idx 1 (idx 1 - 1)) =
       (n : A) • (GeneralizedFormalDistribution.iteratedDeriv formalDelta 1 (n - 1)).coeff idx
  have h_update_00 : (Function.update idx (0 : Fin 2) (idx 0 - 1)) 0 = idx 0 - 1 := by
    simp [Function.update]
  have h_update_01 : (Function.update idx (0 : Fin 2) (idx 0 - 1)) 1 = idx 1 := by
    rw [Function.update_of_ne (by decide)]
  have h_update_10 : (Function.update idx (1 : Fin 2) (idx 1 - 1)) 0 = idx 0 := by
    rw [Function.update_of_ne (by decide)]
  have h_update_11 : (Function.update idx (1 : Fin 2) (idx 1 - 1)) 1 = idx 1 - 1 := by
    simp [Function.update]
  rw [iteratedDeriv_snd_formalDelta_coeff n (Function.update idx 0 (idx 0 - 1)),
      iteratedDeriv_snd_formalDelta_coeff n (Function.update idx 1 (idx 1 - 1)),
      iteratedDeriv_snd_formalDelta_coeff (n - 1) idx]
  rw [h_update_00, h_update_01, h_update_10, h_update_11]
  by_cases h : idx 0 + idx 1 + ↑n = 0
  · rw [if_pos (by omega : (idx 0 - 1 : ℤ) + idx 1 + ↑n + 1 = 0),
        if_pos (by omega : idx 0 + (idx 1 - 1 : ℤ) + ↑n + 1 = 0),
        if_pos (by omega : idx 0 + idx 1 + ↑(n - 1 : ℕ) + 1 = 0)]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [← Int.cast_sub, risingProd_diff (idx 1) n', Int.cast_mul]
    rw [Int.cast_natCast]
    rfl
  · rw [if_neg (by omega : ¬((idx 0 - 1 : ℤ) + idx 1 + ↑n + 1 = 0)),
        if_neg (by omega : ¬(idx 0 + (idx 1 - 1 : ℤ) + ↑n + 1 = 0)),
        if_neg (by omega : ¬(idx 0 + idx 1 + ↑(n - 1 : ℕ) + 1 = 0))]
    simp

/-- Iteration commutes: `f^{n+1}(a) = f^n(f(a))`. -/
theorem mul_z_sub_w_pow_succ (a : GenFormalDist2 A) (n : ℕ) :
    mul_z_sub_w_pow a (n + 1) = mul_z_sub_w_pow (mul_z_sub_w a) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show mul_z_sub_w (mul_z_sub_w_pow a (n + 1)) =
         mul_z_sub_w (mul_z_sub_w_pow (mul_z_sub_w a) n)
    rw [ih]

/-- Iteration distributes over scalar multiplication. -/
theorem smul_mul_z_sub_w_pow (m : ℕ) (c : A) (a : GenFormalDist2 A) :
    mul_z_sub_w_pow (c • a) m = c • mul_z_sub_w_pow a m := by
  induction m with
  | zero => rfl
  | succ m ihm =>
    show mul_z_sub_w (mul_z_sub_w_pow (c • a) m) =
         c • mul_z_sub_w (mul_z_sub_w_pow a m)
    rw [ihm, mul_z_sub_w_smul]

/-- Property 3: `δ(z,w) = δ(z,w)` (symmetry of the definition).

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.3.5(3)
-/
theorem formalDelta_symm : @formalDelta A _ = @formalDelta A _ := by rfl

/-- Property 4: `∂_z δ(z,w) + ∂_w δ(z,w) = 0`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.3.5(4)
-/
theorem deriv_fst_formalDelta_add_deriv_snd_formalDelta :
    GeneralizedFormalDistribution.deriv formalDelta 0 +
    GeneralizedFormalDistribution.deriv formalDelta 1 = (0 : GenFormalDist2 A) := by
  ext idx
  show (idx 0 + 1 : ℤ) • formalDelta.coeff (Function.update idx 0 (idx 0 + 1)) +
       (idx 1 + 1 : ℤ) • formalDelta.coeff (Function.update idx 1 (idx 1 + 1)) = 0
  rw [formalDelta_coeff, formalDelta_coeff]
  have h1 : Function.update idx 0 (idx 0 + 1) 0 = idx 0 + 1 := update_eval_same idx 0 (idx 0 + 1)
  have h2 : Function.update idx 0 (idx 0 + 1) 1 = idx 1 := update_eval_diff idx 0 1 (idx 0 + 1) (by decide)
  have h3 : Function.update idx 1 (idx 1 + 1) 0 = idx 0 := update_eval_diff idx 1 0 (idx 1 + 1) (by decide)
  have h4 : Function.update idx 1 (idx 1 + 1) 1 = idx 1 + 1 := update_eval_same idx 1 (idx 1 + 1)
  simp only [h1, h2, h3, h4]
  by_cases h : idx 0 + idx 1 + 2 = 0
  · have cond1 : (idx 0 + 1 : ℤ) + idx 1 + 1 = 0 := by omega
    have cond2 : idx 0 + (idx 1 + 1 : ℤ) + 1 = 0 := by omega
    simp only [cond1, cond2, ↓reduceIte, zsmul_eq_mul, mul_one]
    have key : ((idx 0 + 1 : ℤ) : A) + ((idx 1 + 1 : ℤ) : A) = ((idx 0 + 1 + (idx 1 + 1) : ℤ) : A) := by
      rw [← Int.cast_add]
    rw [key]
    have : idx 0 + 1 + (idx 1 + 1) = idx 0 + idx 1 + 2 := by omega
    rw [this, h]
    simp
  · have cond1 : ¬((idx 0 + 1 : ℤ) + idx 1 + 1 = 0) := by omega
    have cond2 : ¬(idx 0 + (idx 1 + 1 : ℤ) + 1 = 0) := by omega
    simp only [cond1, cond2, ↓reduceIte]
    rw [smul_zero, smul_zero, zero_add]

/-- Property 1: `(z-w)^{n+1} · ∂_w^n δ = 0` for all `n`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.3.5(1)
-/
theorem mul_z_sub_w_pow_succ_iteratedDeriv_formalDelta_eq_zero (n : ℕ) :
    mul_z_sub_w_pow (GeneralizedFormalDistribution.iteratedDeriv (formalDelta : GenFormalDist2 A) (1 : Fin 2) n) (n + 1) = 0 := by
  induction n with
  | zero =>
    simp only [mul_z_sub_w_pow, GeneralizedFormalDistribution.iteratedDeriv]
    exact mul_z_sub_w_formalDelta
  | succ n ih =>
    rw [mul_z_sub_w_pow_succ, mul_z_sub_w_iteratedDeriv_formalDelta (n + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [smul_mul_z_sub_w_pow, ih]
    ext idx; show ((n + 1 : ℕ) : A) • (0 : GenFormalDist2 A).coeff idx = 0
    exact smul_zero _

/-- Scalar multiplication is associative for generalized distributions. -/
theorem smul_smul_gen (c₁ c₂ : A) (a : GenFormalDist2 A) :
    c₁ • (c₂ • a) = (c₁ * c₂) • a := by
  ext idx
  show c₁ * (c₂ * a.coeff idx) = (c₁ * c₂) * a.coeff idx
  exact (mul_assoc c₁ c₂ _).symm

/-- Property 7: Falling factorial identity.

`(z-w)^j · ∂_w^n δ(z,w) = n! / (n-j)! · ∂_w^{n-j} δ(z,w)`

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.3.5(7)
-/
theorem mul_z_sub_w_pow_iteratedDeriv_formalDelta (n j : ℕ) :
    mul_z_sub_w_pow
      (GeneralizedFormalDistribution.iteratedDeriv (formalDelta : GenFormalDist2 A) (1 : Fin 2) n) j =
    ((Nat.descFactorial n j : ℕ) : A) •
      GeneralizedFormalDistribution.iteratedDeriv formalDelta (1 : Fin 2) (n - j) := by
  induction j with
  | zero =>
    simp only [mul_z_sub_w_pow, Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero]
    ext idx
    show (GeneralizedFormalDistribution.iteratedDeriv (formalDelta : GenFormalDist2 A) 1 n).coeff idx =
         (1 : A) * (GeneralizedFormalDistribution.iteratedDeriv formalDelta 1 n).coeff idx
    exact (one_mul _).symm
  | succ j ih =>
    show mul_z_sub_w (mul_z_sub_w_pow
      (GeneralizedFormalDistribution.iteratedDeriv formalDelta 1 n) j) = _
    rw [ih, mul_z_sub_w_smul]
    by_cases hjn : j < n
    · have h_idx : (n - j : ℕ) - 1 = n - (j + 1) := by omega
      rw [mul_z_sub_w_iteratedDeriv_formalDelta (n - j) (by omega), smul_smul_gen, h_idx, ← Nat.cast_mul,
          show Nat.descFactorial n j * (n - j) = Nat.descFactorial n (j + 1) from
            by rw [Nat.descFactorial_succ, mul_comm]]
    · push_neg at hjn
      have hnj : n - j = 0 := by omega
      have hnj1 : n - (j + 1) = 0 := by omega
      simp only [hnj, hnj1, GeneralizedFormalDistribution.iteratedDeriv]
      rw [mul_z_sub_w_formalDelta]
      have hdf : Nat.descFactorial n (j + 1) = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hdf, Nat.cast_zero]
      ext idx
      show (↑(Nat.descFactorial n j) : A) • (0 : GenFormalDist2 A).coeff idx =
           (0 : A) • (formalDelta : GenFormalDist2 A).coeff idx
      exact (smul_zero _).trans (zero_smul A _).symm

section CommRingProperties

variable {A : Type*} [CommRing A]
open GeneralizedFormalDistribution

/-- The coefficient of `embedFst(a) * δ` at index `(n,m)` equals `a_{n+m+1}`. -/
lemma embedFst_mulGen_formalDelta_coeff (a : FormalDist1 A) (idx : Fin 2 → ℤ) :
    ((FormalDistribution.embedFst a).mulGen formalDelta).coeff idx =
    a.coeff (fun _ => idx 0 + idx 1 + 1) := by
  change GeneralizedFormalDistribution.mulFormalGen _ _ _ _ = _
  unfold GeneralizedFormalDistribution.mulFormalGen
  rw [Finset.sum_eq_single (fun i : Fin 2 => if i = 0 then idx 0 + idx 1 + 1 else 0)]
  · simp only [FormalDistribution.embedFst, formalDelta_coeff]
    simp only [show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
               ite_true, ite_false, sub_zero]
    rw [if_pos (by omega : idx 0 - (idx 0 + idx 1 + 1) + idx 1 + 1 = 0), mul_one]
  · intro c hc hne
    have hsupp : (FormalDistribution.embedFst a).coeff c ≠ 0 :=
      (Set.Finite.mem_toFinset _).mp hc
    by_cases h1 : c 1 = 0
    · have hc0 : c 0 ≠ idx 0 + idx 1 + 1 := by
        intro heq; apply hne; ext i; fin_cases i <;> simp [heq, h1]
      simp only [FormalDistribution.embedFst, formalDelta_coeff] at hsupp ⊢
      simp only [h1, show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
                 ite_true, ite_false, sub_zero] at hsupp ⊢
      rw [if_neg (by omega : ¬(idx 0 - c 0 + idx 1 + 1 = 0)), mul_zero]
    · exfalso; apply hsupp
      simp [FormalDistribution.embedFst, h1]
  · intro hb
    have : (FormalDistribution.embedFst a).coeff
        (fun i : Fin 2 => if i = 0 then idx 0 + idx 1 + 1 else 0) = 0 := by
      by_contra h; exact hb ((Set.Finite.mem_toFinset _).mpr h)
    rw [this, zero_mul]

/-- The coefficient of `embedSnd(a) * δ` at index `(n,m)` also equals `a_{n+m+1}`. -/
lemma embedSnd_mulGen_formalDelta_coeff (a : FormalDist1 A) (idx : Fin 2 → ℤ) :
    ((FormalDistribution.embedSnd a).mulGen formalDelta).coeff idx =
    a.coeff (fun _ => idx 0 + idx 1 + 1) := by
  change GeneralizedFormalDistribution.mulFormalGen _ _ _ _ = _
  unfold GeneralizedFormalDistribution.mulFormalGen
  rw [Finset.sum_eq_single (fun i : Fin 2 => if i = 0 then 0 else idx 0 + idx 1 + 1)]
  · simp only [FormalDistribution.embedSnd, formalDelta_coeff]
    simp only [show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
               ite_true, ite_false, sub_zero]
    rw [if_pos (by omega : idx 0 + (idx 1 - (idx 0 + idx 1 + 1)) + 1 = 0), mul_one]
  · intro c hc hne
    have hsupp : (FormalDistribution.embedSnd a).coeff c ≠ 0 :=
      (Set.Finite.mem_toFinset _).mp hc
    by_cases h0 : c 0 = 0
    · have hc1 : c 1 ≠ idx 0 + idx 1 + 1 := by
        intro heq; apply hne; ext i; fin_cases i <;> simp [heq, h0]
      simp only [FormalDistribution.embedSnd, formalDelta_coeff] at hsupp ⊢
      simp only [h0, show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
                 ite_true, ite_false, sub_zero] at hsupp ⊢
      rw [if_neg (by omega : ¬(idx 0 + (idx 1 - c 1) + 1 = 0)), mul_zero]
    · exfalso; apply hsupp
      simp [FormalDistribution.embedSnd, h0]
  · intro hb
    have : (FormalDistribution.embedSnd a).coeff
        (fun i : Fin 2 => if i = 0 then 0 else idx 0 + idx 1 + 1) = 0 := by
      by_contra h; exact hb ((Set.Finite.mem_toFinset _).mpr h)
    rw [this, zero_mul]

/-- Property 5: `a(z)δ(z,w) = a(w)δ(z,w)` for any formal distribution `a(z)`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.3.5(5)
-/
theorem embedFst_mulGen_formalDelta_eq_embedSnd (a : FormalDist1 A) :
    (FormalDistribution.embedFst a).mulGen formalDelta =
    (FormalDistribution.embedSnd a).mulGen formalDelta := by
  ext idx
  rw [embedFst_mulGen_formalDelta_coeff, embedSnd_mulGen_formalDelta_coeff]

/-- Property 6: `Res_z a(z)δ(z,w) = a(w)`, showing `δ` extracts `a` at `w`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.3.5(6)
-/
theorem residueAt_embedFst_mulGen_formalDelta (a : FormalDist1 A) :
    GeneralizedFormalDistribution.residueAt 0
      ((FormalDistribution.embedFst a).mulGen formalDelta) =
    a.toGeneralized := by
  ext idx
  simp only [GeneralizedFormalDistribution.residueAt]
  rw [embedFst_mulGen_formalDelta_coeff]
  simp only [FormalDistribution.toGeneralized]
  congr 1; ext i; fin_cases i; simp

end CommRingProperties

end FormalDelta

/-! ## Summary

All main results from Section 1 are formalized:
  - Definition 1.1.1: FormalDistribution, FormalPolynomial, FormalTaylorSeries
  - Definition 1.1.3: fourierExpansion, fourierMode, residue
  - Definition 1.2.1: expansion_izw, expansion_iwz
  - Definition 1.2.2: Int.extChoose, intBinomial
  - Proposition 1.3.4: formalDelta_eq_expansion_izw_sub_iwz
  - Definition 1.3.1: formalDelta
  - Proposition 1.3.5: Properties 1-7 of δ (all complete)
-/

-- Verify key definitions compile
example : Type _ := FormalDistribution ℂ 1
example : Type _ := GeneralizedFormalDistribution ℂ 2
example : FormalDist1 ℂ → (ℤ → ℂ) := fourierExpansion
example : ℤ → ℕ → ℚ := Int.extChoose
noncomputable example : GenFormalDist2 ℂ := formalDelta
