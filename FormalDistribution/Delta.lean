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

/-! ## Multiplication by variable differences (n-variable) -/

/-- Multiplication by `(x_i - x_j)` on n-variable generalized distributions.

`((x_i - x_j) · a)(idx) = a(idx with idx_i - 1) - a(idx with idx_j - 1)` -/
def mul_var_sub {n : ℕ} (i j : Fin n) (_hij : i ≠ j)
    (a : GeneralizedFormalDistribution A n) : GeneralizedFormalDistribution A n where
  coeff := fun idx =>
    a.coeff (Function.update idx i (idx i - 1)) -
    a.coeff (Function.update idx j (idx j - 1))
  support_finite := fun bound => by
    have shift_mem (k : Fin n) (idx : Fin n → ℤ)
        (hge : ∀ i, idx i ≥ bound i) (hne : a.coeff (Function.update idx k (idx k - 1)) ≠ 0) :
        idx ∈ (fun idx' => Function.update idx' k (idx' k + 1)) ''
          {f | (∀ i, f i ≥ (Function.update bound k (bound k - 1)) i) ∧ a.coeff f ≠ 0} := by
      refine ⟨Function.update idx k (idx k - 1), ⟨fun i => ?_, hne⟩, ?_⟩
      · by_cases hi : i = k <;> simp [Function.update, hi] <;> [linarith [hge k]; exact hge i]
      · ext i; by_cases hi : i = k <;> simp [Function.update, hi]
    apply Set.Finite.subset ((a.support_finite (Function.update bound i (bound i - 1))).image _
      |>.union ((a.support_finite (Function.update bound j (bound j - 1))).image _))
    intro idx ⟨hge, hne⟩
    by_cases h0 : a.coeff (Function.update idx i (idx i - 1)) ≠ 0
    · exact Or.inl (shift_mem i idx hge h0)
    · exact Or.inr (shift_mem j idx hge
        (by push_neg at h0; intro h1; exact hne (by simp [h0, h1])))

/-- Iterated multiplication by `(x_i - x_j)`. -/
def mul_var_sub_pow {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (a : GeneralizedFormalDistribution A n) : ℕ → GeneralizedFormalDistribution A n
  | 0 => a
  | k + 1 => mul_var_sub i j hij (mul_var_sub_pow i j hij a k)

/-- `mul_var_sub` commutes with scalar multiplication. -/
theorem mul_var_sub_smul {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : A)
    (a : GeneralizedFormalDistribution A n) :
    mul_var_sub i j hij (c • a) = c • mul_var_sub i j hij a := by
  ext idx; show c • a.coeff _ - c • a.coeff _ = c • (a.coeff _ - a.coeff _)
  rw [smul_sub]

/-- Iteration commutes: `f^{k+1}(a) = f^k(f(a))`. -/
theorem mul_var_sub_pow_succ {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (a : GeneralizedFormalDistribution A n) (k : ℕ) :
    mul_var_sub_pow i j hij a (k + 1) =
    mul_var_sub_pow i j hij (mul_var_sub i j hij a) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show mul_var_sub i j hij (mul_var_sub_pow i j hij a (k + 1)) =
         mul_var_sub i j hij (mul_var_sub_pow i j hij (mul_var_sub i j hij a) k)
    rw [ih]

/-- Iteration distributes over scalar multiplication. -/
theorem smul_mul_var_sub_pow {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (m : ℕ) (c : A) (a : GeneralizedFormalDistribution A n) :
    mul_var_sub_pow i j hij (c • a) m = c • mul_var_sub_pow i j hij a m := by
  induction m with
  | zero => rfl
  | succ m ihm =>
    show mul_var_sub i j hij (mul_var_sub_pow i j hij (c • a) m) =
         c • mul_var_sub i j hij (mul_var_sub_pow i j hij a m)
    rw [ihm, mul_var_sub_smul]

/-! ## Formal delta distribution (n-variable and 2-variable) -/

/-- The formal delta distribution in variables `i` and `j` of an n-variable space.

`δ(z_i, z_j)` has support on `{idx | idx_i + idx_j + 1 = 0}` with all other indices zero. -/
noncomputable def formalDeltaPair {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    GeneralizedFormalDistribution A n where
  coeff := fun idx =>
    if idx i + idx j + 1 = 0 ∧ (∀ k, k ≠ i → k ≠ j → idx k = 0) then (1 : A) else 0
  support_finite := fun bound => by
    apply ((Finset.Icc (bound i) (-bound j - 1)).finite_toSet.image
      (fun k => fun l : Fin n => if l = i then k else if l = j then -k - 1 else 0)).subset
    intro idx ⟨hall, hne⟩
    split_ifs at hne with hidx
    · obtain ⟨hsum, hzero⟩ := hidx
      have hj := hall j
      refine ⟨idx i, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hall i, by omega⟩), ?_⟩
      ext l
      by_cases hli : l = i
      · subst hli; simp
      · by_cases hlj : l = j
        · simp [hlj]; omega
        · simp [hli, hlj, hzero l hli hlj]
    · simp at hne

/-- The formal delta distribution `δ(z,w) = ∑_{n ∈ ℤ} z^n w^{-n-1}` (alias).

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.3.1
-/
noncomputable abbrev formalDelta : GenFormalDist2 A :=
  formalDeltaPair 0 1 (by decide)

/-- The coefficients of `formalDelta` match the expected pattern. -/
@[simp]
theorem formalDelta_coeff (idx : Fin 2 → ℤ) :
    formalDelta.coeff idx = if idx 0 + idx 1 + 1 = 0 then (1 : A) else 0 := by
  show (formalDeltaPair 0 1 (by decide)).coeff idx = _
  simp only [formalDeltaPair]
  congr 1; ext
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h; exact ⟨h, fun k hk0 hk1 => by fin_cases k <;> simp_all⟩

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

/-- Multiplication by `(z - w)` on generalized 2-variable distributions (alias). -/
abbrev mul_z_sub_w (a : GenFormalDist2 A) : GenFormalDist2 A :=
  mul_var_sub 0 1 (by decide) a

/-- Iterated multiplication by `(z - w)` (alias). -/
abbrev mul_z_sub_w_pow (a : GenFormalDist2 A) (n : ℕ) : GenFormalDist2 A :=
  mul_var_sub_pow 0 1 (by decide) a n

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
    rw [ih (Function.update idx 1 (idx 1 + 1)),
        Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
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
    mul_z_sub_w (c • a) = c • mul_z_sub_w a :=
  mul_var_sub_smul 0 1 (by decide) c a

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
  rw [iteratedDeriv_snd_formalDelta_coeff n (Function.update idx 0 (idx 0 - 1)),
      iteratedDeriv_snd_formalDelta_coeff n (Function.update idx 1 (idx 1 - 1)),
      iteratedDeriv_snd_formalDelta_coeff (n - 1) idx]
  simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
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
    mul_z_sub_w_pow a (n + 1) = mul_z_sub_w_pow (mul_z_sub_w a) n :=
  mul_var_sub_pow_succ 0 1 (by decide) a n

/-- Iteration distributes over scalar multiplication. -/
theorem smul_mul_z_sub_w_pow (m : ℕ) (c : A) (a : GenFormalDist2 A) :
    mul_z_sub_w_pow (c • a) m = c • mul_z_sub_w_pow a m :=
  smul_mul_var_sub_pow 0 1 (by decide) m c a

/-- Swap the two variables of a 2-variable generalized distribution: `a(z,w) ↦ a(w,z)`. -/
noncomputable def swap2 (a : GenFormalDist2 A) : GenFormalDist2 A where
  coeff idx := a.coeff (fun i : Fin 2 => if i = 0 then idx 1 else idx 0)
  support_finite bound := by
    have ha := a.support_finite (fun i : Fin 2 => if i = 0 then bound 1 else bound 0)
    apply (ha.image (fun f : Fin 2 → ℤ => fun i : Fin 2 => if i = 0 then f 1 else f 0)).subset
    intro idx ⟨hge, hne⟩
    refine ⟨fun i : Fin 2 => if i = 0 then idx 1 else idx 0, ⟨fun i => ?_, hne⟩, ?_⟩
    · fin_cases i <;> simp <;> [exact hge 1; exact hge 0]
    · funext i; fin_cases i <;> simp

/-- Property 3 (symmetry): `δ(z,w) = δ(w,z)`.

Swapping the two variables of the formal delta yields the same distribution,
because the support condition `n + m + 1 = 0` is symmetric.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.3.5(3)
-/
theorem formalDelta_swap : swap2 (formalDelta : GenFormalDist2 A) = formalDelta := by
  ext idx
  show (formalDelta : GenFormalDist2 A).coeff
    (fun i : Fin 2 => if i = 0 then idx 1 else idx 0) = formalDelta.coeff idx
  rw [formalDelta_coeff, formalDelta_coeff]
  simp only [show (1 : Fin 2) = 0 ↔ False from by decide, ite_true, ite_false]
  exact if_congr ⟨by omega, by omega⟩ rfl rfl

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
  simp only [formalDelta_coeff, Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  by_cases h : idx 0 + idx 1 + 2 = 0
  · simp only [show (idx 0 + 1 : ℤ) + idx 1 + 1 = 0 from by omega,
               show idx 0 + (idx 1 + 1 : ℤ) + 1 = 0 from by omega, ↓reduceIte, zsmul_eq_mul, mul_one,
               ← Int.cast_add, show idx 0 + 1 + (idx 1 + 1) = idx 0 + idx 1 + 2 from by omega, h,
               Int.cast_zero]
  · simp only [show ¬((idx 0 + 1 : ℤ) + idx 1 + 1 = 0) from by omega,
               show ¬(idx 0 + (idx 1 + 1 : ℤ) + 1 = 0) from by omega, ↓reduceIte,
               smul_zero, zero_add]

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
  · simp only [FormalDistribution.embedFst_coeff', formalDelta_coeff]
    simp only [show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
               ite_true, ite_false, sub_zero]
    rw [if_pos (by omega : idx 0 - (idx 0 + idx 1 + 1) + idx 1 + 1 = 0), mul_one]
  · intro c hc hne
    have hsupp : (FormalDistribution.embedFst a).coeff c ≠ 0 :=
      (Set.Finite.mem_toFinset _).mp hc
    by_cases h1 : c 1 = 0
    · have hc0 : c 0 ≠ idx 0 + idx 1 + 1 := by
        intro heq; apply hne; ext i; fin_cases i <;> simp [heq, h1]
      simp only [FormalDistribution.embedFst_coeff', formalDelta_coeff] at hsupp ⊢
      simp only [h1, show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
                 ite_true, ite_false, sub_zero] at hsupp ⊢
      rw [if_neg (by omega : ¬(idx 0 - c 0 + idx 1 + 1 = 0)), mul_zero]
    · exfalso; apply hsupp
      simp [h1]
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
  · simp only [FormalDistribution.embedSnd_coeff', formalDelta_coeff]
    simp only [show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
               ite_true, ite_false, sub_zero]
    rw [if_pos (by omega : idx 0 + (idx 1 - (idx 0 + idx 1 + 1)) + 1 = 0), mul_one]
  · intro c hc hne
    have hsupp : (FormalDistribution.embedSnd a).coeff c ≠ 0 :=
      (Set.Finite.mem_toFinset _).mp hc
    by_cases h0 : c 0 = 0
    · have hc1 : c 1 ≠ idx 0 + idx 1 + 1 := by
        intro heq; apply hne; ext i; fin_cases i <;> simp [heq, h0]
      simp only [FormalDistribution.embedSnd_coeff', formalDelta_coeff] at hsupp ⊢
      simp only [h0, show (1 : Fin 2) = (0 : Fin 2) ↔ False from by decide,
                 ite_true, ite_false, sub_zero] at hsupp ⊢
      rw [if_neg (by omega : ¬(idx 0 + (idx 1 - c 1) + 1 = 0)), mul_zero]
    · exfalso; apply hsupp
      simp [h0]
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
  rw [GeneralizedFormalDistribution.residueAt_coeff]
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
  - Definition 1.2.2: intBinomial (via Ring.choose)
  - Proposition 1.3.4: formalDelta_eq_expansion_izw_sub_iwz
  - Definition 1.3.1: formalDelta
  - Proposition 1.3.5: Properties 1-7 of δ (all complete)
-/

-- Verify key definitions compile
example : Type _ := FormalDistribution ℂ 1
example : Type _ := GeneralizedFormalDistribution ℂ 2
example : FormalDist1 ℂ → (ℤ → ℂ) := fourierExpansion
example : ℤ → ℕ → ℤ := intBinomial
noncomputable example : GenFormalDist2 ℂ := formalDelta
