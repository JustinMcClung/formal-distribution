/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FormalDistribution.Delta

/-!
# Decomposition Theorem (Proposition 1.3.6)

If `(z-w)^N · f = 0` for a generalized formal distribution `f`, then `f` can be
uniquely decomposed as a finite sum involving generalized binomial coefficients.

At the coefficient level, the decomposition reads:
`f(p,q) = ∑_{j<N} C(-p-1, j) · c_j(p+q+j+1)`
where `c_j(m) = ((z-w)^j f)(-1, m)` and `C` is the generalized binomial coefficient.

## Main results

* `antidiag_const_of_mul_z_sub_w_zero` - base case: `(z-w)f = 0` implies anti-diagonal constancy
* `decomposition_theorem` - the full decomposition formula

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.3.6
-/

open scoped BigOperators

variable {A : Type*} [Ring A]

/-! ### Coefficient accessor for n-variable distributions -/

/-- Access the coefficient of an n-variable distribution at positions `(p, q)` in variables `i, j`,
with all other variables set to `0`. -/
def coeffPair {n : ℕ} (i j : Fin n) (_hij : i ≠ j)
    (f : GeneralizedFormalDistribution A n) (p q : ℤ) : A :=
  f.coeff (fun k => if k = i then p else if k = j then q else 0)

@[simp] lemma coeffPair_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j) (p q : ℤ) :
    coeffPair i j hij (0 : GeneralizedFormalDistribution A n) p q = 0 := rfl

/-- The `mul_var_sub` operation in terms of `coeffPair`:
`((x_i - x_j)·f)(p,q) = f(p-1,q) - f(p,q-1)`. -/
lemma mul_var_sub_coeffPair {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (f : GeneralizedFormalDistribution A n) (p q : ℤ) :
    coeffPair i j hij (mul_var_sub i j hij f) p q =
    coeffPair i j hij f (p - 1) q - coeffPair i j hij f p (q - 1) := by
  simp only [coeffPair]
  have key : ∀ g : Fin n → ℤ, (mul_var_sub i j hij f).coeff g =
      f.coeff (Function.update g i (g i - 1)) - f.coeff (Function.update g j (g j - 1)) :=
    fun _ => rfl
  rw [key]; simp only [hij.symm, ite_false, ite_true]
  congr 1 <;> congr 1 <;> funext k <;> by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [Function.update, hki, hkj, hij, hij.symm]

/-! ### Antidiagonal constancy (general) -/

omit [Ring A] in
/-- If `D(p,q) = D(p+1, q-1)` for all `p, q`, then `D(p,q) = D(-1, p+q+1)`. -/
lemma antidiag_const_fun' (D : ℤ → ℤ → A)
    (hshift : ∀ p q, D p q = D (p + 1) (q - 1))
    (p q : ℤ) : D p q = D (-1) (p + q + 1) := by
  suffices h : ∀ k : ℤ, D p q = D (p + k) (q - k) by
    have := h (-(p + 1))
    rwa [show p + -(p + 1) = -1 from by omega,
         show q - -(p + 1) = p + q + 1 from by omega] at this
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [ih, hshift]; congr 1 <;> omega
  | pred n ih =>
    rw [ih]; have := (hshift (p + (-↑n - 1)) (q - (-↑n - 1))).symm
    rwa [show p + (-↑n - 1) + 1 = p + -↑n from by omega,
         show q - (-↑n - 1) - 1 = q - -↑n from by omega] at this

/-- Shift property: if `(x_i - x_j)·f = 0`, then `coeffPair f p q = coeffPair f (p+1) (q-1)`. -/
lemma shift_of_mul_var_sub_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (f : GeneralizedFormalDistribution A n) (hf : mul_var_sub i j hij f = 0)
    (p q : ℤ) : coeffPair i j hij f p q = coeffPair i j hij f (p + 1) (q - 1) := by
  have h := mul_var_sub_coeffPair i j hij f (p + 1) q
  rw [show p + 1 - 1 = p from by omega] at h
  simp only [hf, coeffPair_zero] at h
  exact sub_eq_zero.mp h.symm

/-- If `(x_i - x_j)·f = 0`, then `coeffPair f p q = coeffPair f (-1) (p+q+1)`. -/
theorem antidiag_const_of_mul_var_sub_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (f : GeneralizedFormalDistribution A n) (hf : mul_var_sub i j hij f = 0)
    (p q : ℤ) : coeffPair i j hij f p q = coeffPair i j hij f (-1) (p + q + 1) :=
  antidiag_const_fun' _ (shift_of_mul_var_sub_zero i j hij f hf) p q

/-! ### Decomposition Theorem (n-variable, Proposition 1.3.6) -/

/-- **Decomposition Theorem** (n-variable version of Proposition 1.3.6).

If `(x_i - x_j)^N · f = 0` for a generalized n-variable distribution `f`, then:
`coeffPair f p q = ∑_{j'<N} C(-p-1, j') · coeffPair ((x_i-x_j)^{j'} · f) (-1) (p+q+j'+1)` -/
theorem decomposition_theorem_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (f : GeneralizedFormalDistribution A n) (N : ℕ)
    (hf : mul_var_sub_pow i j hij f N = 0) (p q : ℤ) :
    coeffPair i j hij f p q = ∑ j' ∈ Finset.range N,
      (↑(intBinomial (-p - 1) j') : A) *
        coeffPair i j hij (mul_var_sub_pow i j hij f j') (-1) (p + q + ↑j' + 1) := by
  induction N generalizing f p q with
  | zero =>
    simp only [Finset.sum_range_zero]
    rw [show f = 0 from hf]; exact coeffPair_zero i j hij p q
  | succ N ih =>
    have hg : mul_var_sub_pow i j hij (mul_var_sub i j hij f) N = 0 := by
      rw [← mul_var_sub_pow_succ]; exact hf
    have ih_g := fun p' q' => ih (mul_var_sub i j hij f) hg p' q'
    have hgj : ∀ j', mul_var_sub_pow i j hij (mul_var_sub i j hij f) j' =
        mul_var_sub_pow i j hij f (j' + 1) :=
      fun j' => (mul_var_sub_pow_succ i j hij f j').symm
    let F : ℤ → ℤ → A := fun p' q' => ∑ j' ∈ Finset.range (N + 1),
      (↑(intBinomial (-p' - 1) j') : A) *
        coeffPair i j hij (mul_var_sub_pow i j hij f j') (-1) (p' + q' + ↑j' + 1)
    let D : ℤ → ℤ → A := fun p' q' => coeffPair i j hij f p' q' - F p' q'
    suffices hDzero : ∀ p' q', D p' q' = 0 by exact sub_eq_zero.mp (hDzero p q)
    -- Step 1: D(-1, q') = 0 for all q'
    have heval : ∀ q', D (-1) q' = 0 := by
      intro q'; show coeffPair i j hij f (-1) q' - F (-1) q' = 0; rw [sub_eq_zero]
      show coeffPair i j hij f (-1) q' = ∑ j' ∈ Finset.range (N + 1),
        (↑(intBinomial (-(-1 : ℤ) - 1) j') : A) *
          coeffPair i j hij (mul_var_sub_pow i j hij f j') (-1) (-1 + q' + ↑j' + 1)
      rw [show -(-1 : ℤ) - 1 = 0 from by omega]
      rw [Finset.sum_eq_single 0
        (fun j' _ hj' => by cases j' with | zero => exact absurd rfl hj' | succ j'' => simp)
        (fun h => absurd (Finset.mem_range.mpr (Nat.zero_lt_succ N)) h)]
      simp only [intBinomial_zero, Int.cast_one, one_mul, Nat.cast_zero, mul_var_sub_pow]
      congr 1; omega
    -- Step 2: D(p',q') = D(p'+1, q'-1)
    have hshift : ∀ p' q', D p' q' = D (p' + 1) (q' - 1) := by
      intro p' q'
      show coeffPair i j hij f p' q' - F p' q' =
           coeffPair i j hij f (p' + 1) (q' - 1) - F (p' + 1) (q' - 1)
      have h1 : coeffPair i j hij f p' q' - coeffPair i j hij f (p' + 1) (q' - 1) =
          coeffPair i j hij (mul_var_sub i j hij f) (p' + 1) q' := by
        have h := mul_var_sub_coeffPair i j hij f (p' + 1) q'
        rw [show p' + 1 - 1 = p' from by omega] at h; exact h.symm
      have h2 : F p' q' - F (p' + 1) (q' - 1) =
          coeffPair i j hij (mul_var_sub i j hij f) (p' + 1) q' := by
        have hF2 : F (p' + 1) (q' - 1) = ∑ j' ∈ Finset.range (N + 1),
            (↑(intBinomial (-p' - 2) j') : A) *
              coeffPair i j hij (mul_var_sub_pow i j hij f j') (-1)
                (p' + q' + ↑j' + 1) := by
          apply Finset.sum_congr rfl; intro j' _
          congr 1
          · congr 1; congr 1; omega
          · congr 1; omega
        rw [hF2, ← Finset.sum_sub_distrib]; simp_rw [← sub_mul]
        rw [Finset.sum_range_succ']
        simp only [intBinomial_zero, Int.cast_one, sub_self, zero_mul, add_zero]
        rw [Finset.sum_congr rfl fun j' (_ : j' ∈ Finset.range N) => show
            ((↑(intBinomial (-p' - 1) (j' + 1)) : A) -
              ↑(intBinomial (-p' - 2) (j' + 1))) * _ =
            (↑(intBinomial (-p' - 2) j') : A) * _ from by
          congr 1; rw [← Int.cast_sub]; congr 1
          have := intBinomial_pascal (-p' - 2) j'
          rw [show (-p' - 2 : ℤ) + 1 = -p' - 1 from by omega] at this; omega]
        rw [ih_g (p' + 1) q']
        apply Finset.sum_congr rfl; intro j' _
        rw [hgj j']; congr 1
        · congr 1; congr 1; omega
        · congr 1; push_cast; omega
      have h_eq := sub_eq_zero.mpr (show coeffPair i j hij f p' q' -
          coeffPair i j hij f (p' + 1) (q' - 1) =
          F p' q' - F (p' + 1) (q' - 1) from by rw [h1, h2])
      rw [sub_sub_sub_comm] at h_eq; exact sub_eq_zero.mp h_eq
    -- Step 3: Conclude D ≡ 0
    intro p' q'
    have := antidiag_const_fun' D hshift p' q'
    rw [this, heval]

namespace FormalDelta

/-! ### Coefficient accessor for 2D distributions -/

/-- Access the coefficient of a 2D generalized distribution at `(p, q)`. -/
def coeff2 (f : GenFormalDist2 A) (p q : ℤ) : A :=
  f.coeff (fun i : Fin 2 => if i = 0 then p else q)

@[simp] lemma coeff2_zero (p q : ℤ) : coeff2 (0 : GenFormalDist2 A) p q = 0 := rfl

/-- Two 2D distributions are equal iff `coeff2` agrees everywhere. -/
lemma coeff2_ext {f g : GenFormalDist2 A} (h : ∀ p q, coeff2 f p q = coeff2 g p q) : f = g := by
  ext idx
  have := h (idx 0) (idx 1)
  simp only [coeff2] at this
  have hfun : (fun i : Fin 2 => if i = 0 then idx 0 else idx 1) = idx := by
    funext i; fin_cases i <;> simp
  rwa [hfun] at this

/-! ### Relating mul_z_sub_w to coeff2 -/

/-- The `mul_z_sub_w` operation in terms of `coeff2`:
`((z-w)·f)(p,q) = f(p-1,q) - f(p,q-1)`. -/
lemma mul_z_sub_w_coeff2 (f : GenFormalDist2 A) (p q : ℤ) :
    coeff2 (mul_z_sub_w f) p q = coeff2 f (p - 1) q - coeff2 f p (q - 1) := by
  unfold coeff2
  change f.coeff (Function.update (fun i : Fin 2 => if i = 0 then p else q) 0 (p - 1)) -
         f.coeff (Function.update (fun i : Fin 2 => if i = 0 then p else q) 1 (q - 1)) =
         f.coeff (fun i : Fin 2 => if i = 0 then p - 1 else q) -
         f.coeff (fun i : Fin 2 => if i = 0 then p else q - 1)
  congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;>
    simp [Function.update, show ¬((0 : Fin 2) = 1) from by decide,
          show ¬((1 : Fin 2) = 0) from by decide]

/-- Shift property: if `(z-w)·f = 0`, then `f(p,q) = f(p+1, q-1)`. -/
lemma shift_of_mul_z_sub_w_zero (f : GenFormalDist2 A) (hf : mul_z_sub_w f = 0)
    (p q : ℤ) : coeff2 f p q = coeff2 f (p + 1) (q - 1) := by
  have h := mul_z_sub_w_coeff2 f (p + 1) q
  rw [show p + 1 - 1 = p from by omega] at h
  simp only [hf, coeff2_zero] at h
  exact sub_eq_zero.mp h.symm

/-- If `(z-w)·f = 0`, then `f` is constant on anti-diagonals:
`f(p,q) = f(-1, p+q+1)` for all `p, q`. -/
theorem antidiag_const_of_mul_z_sub_w_zero (f : GenFormalDist2 A) (hf : mul_z_sub_w f = 0)
    (p q : ℤ) : coeff2 f p q = coeff2 f (-1) (p + q + 1) := by
  suffices h : ∀ k : ℤ, coeff2 f p q = coeff2 f (p + k) (q - k) by
    have := h (-(p + 1))
    rwa [show p + -(p + 1) = -1 from by omega,
         show q - -(p + 1) = p + q + 1 from by omega] at this
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [ih, shift_of_mul_z_sub_w_zero f hf]
    congr 1 <;> omega
  | pred n ih =>
    rw [ih]
    have := (shift_of_mul_z_sub_w_zero f hf (p + (-↑n - 1)) (q - (-↑n - 1))).symm
    rwa [show p + (-↑n - 1) + 1 = p + -↑n from by omega,
         show q - (-↑n - 1) - 1 = q - -↑n from by omega] at this

/-! ### Antidiagonal constancy for functions -/

omit [Ring A] in
/-- If a function `D : ℤ → ℤ → A` satisfies `D(p,q) = D(p+1, q-1)` for all `p, q`,
then `D(p,q) = D(-1, p+q+1)`. -/
private lemma antidiag_const_fun (D : ℤ → ℤ → A)
    (hshift : ∀ p q, D p q = D (p + 1) (q - 1))
    (p q : ℤ) : D p q = D (-1) (p + q + 1) := by
  suffices h : ∀ k : ℤ, D p q = D (p + k) (q - k) by
    have := h (-(p + 1))
    rwa [show p + -(p + 1) = -1 from by omega,
         show q - -(p + 1) = p + q + 1 from by omega] at this
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [ih, hshift]; congr 1 <;> omega
  | pred n ih =>
    rw [ih]; have := (hshift (p + (-↑n - 1)) (q - (-↑n - 1))).symm
    rwa [show p + (-↑n - 1) + 1 = p + -↑n from by omega,
         show q - (-↑n - 1) - 1 = q - -↑n from by omega] at this

/-! ### Decomposition Theorem (Proposition 1.3.6) -/

/-- **Decomposition Theorem** (Proposition 1.3.6).

If `(z-w)^N · f = 0` for a generalized 2D distribution `f`, then:
`f(p,q) = ∑_{j<N} C(-p-1, j) · c_j(p+q+j+1)`
where `c_j(m) = ((z-w)^j · f)(-1, m)` is the `j`-th residue coefficient.

This is the coefficient-level formulation avoiding division by factorials. -/
theorem decomposition_theorem (f : GenFormalDist2 A) (N : ℕ)
    (hf : mul_z_sub_w_pow f N = 0) (p q : ℤ) :
    coeff2 f p q = ∑ j ∈ Finset.range N,
      (↑(intBinomial (-p - 1) j) : A) *
        coeff2 (mul_z_sub_w_pow f j) (-1) (p + q + ↑j + 1) := by
  induction N generalizing f p q with
  | zero =>
    simp only [Finset.sum_range_zero]
    have hf0 : f = 0 := hf
    rw [hf0]; exact coeff2_zero p q
  | succ N ih =>
    -- g := mul_z_sub_w f satisfies the hypothesis for N
    have hg : mul_z_sub_w_pow (mul_z_sub_w f) N = 0 := by
      rw [← mul_z_sub_w_pow_succ]; exact hf
    -- IH for g
    have ih_g : ∀ p' q', coeff2 (mul_z_sub_w f) p' q' = ∑ j ∈ Finset.range N,
        (↑(intBinomial (-p' - 1) j) : A) *
          coeff2 (mul_z_sub_w_pow (mul_z_sub_w f) j) (-1) (p' + q' + ↑j + 1) :=
      fun p' q' => ih (mul_z_sub_w f) hg p' q'
    -- Relate mul_z_sub_w_pow (mul_z_sub_w f) j to mul_z_sub_w_pow f (j+1)
    have hgj : ∀ j, mul_z_sub_w_pow (mul_z_sub_w f) j = mul_z_sub_w_pow f (j + 1) := by
      intro j; exact (mul_z_sub_w_pow_succ f j).symm
    -- Define the "formula" and "error" functions
    let F : ℤ → ℤ → A := fun p' q' => ∑ j ∈ Finset.range (N + 1),
      (↑(intBinomial (-p' - 1) j) : A) *
        coeff2 (mul_z_sub_w_pow f j) (-1) (p' + q' + ↑j + 1)
    let D : ℤ → ℤ → A := fun p' q' => coeff2 f p' q' - F p' q'
    -- Goal: D p q = 0
    suffices hDzero : ∀ p' q', D p' q' = 0 by
      exact sub_eq_zero.mp (hDzero p q)
    -- Step 1: D(-1, q') = 0 for all q'
    have heval : ∀ q', D (-1) q' = 0 := by
      intro q'
      show coeff2 f (-1) q' - F (-1) q' = 0
      rw [sub_eq_zero]
      -- F(-1, q') = ∑_j intBinomial(0)(j) * c_j(-1+q'+j+1)
      -- Only j=0 survives since intBinomial(0)(j) = 0 for j ≥ 1
      show coeff2 f (-1) q' = ∑ j ∈ Finset.range (N + 1),
        (↑(intBinomial (-(-1 : ℤ) - 1) j) : A) *
          coeff2 (mul_z_sub_w_pow f j) (-1) (-1 + q' + ↑j + 1)
      rw [show -(-1 : ℤ) - 1 = 0 from by omega]
      rw [Finset.sum_eq_single 0
        (fun j _ hj => by
          cases j with
          | zero => exact absurd rfl hj
          | succ j' => simp)
        (fun h => absurd (Finset.mem_range.mpr (Nat.zero_lt_succ N)) h)]
      simp only [intBinomial_zero, Int.cast_one, one_mul, Nat.cast_zero, mul_z_sub_w_pow]
      congr 1; omega
    -- Step 2: D(p',q') = D(p'+1, q'-1) for all p', q' (shift property)
    have hshift : ∀ p' q', D p' q' = D (p' + 1) (q' - 1) := by
      intro p' q'
      show coeff2 f p' q' - F p' q' = coeff2 f (p' + 1) (q' - 1) - F (p' + 1) (q' - 1)
      -- Part 1: f(p',q') - f(p'+1,q'-1) = coeff2(mul_z_sub_w f)(p'+1)(q')
      have h1 : coeff2 f p' q' - coeff2 f (p' + 1) (q' - 1) =
          coeff2 (mul_z_sub_w f) (p' + 1) q' := by
        have h := mul_z_sub_w_coeff2 f (p' + 1) q'
        rw [show p' + 1 - 1 = p' from by omega] at h; exact h.symm
      -- Part 2: F(p',q') - F(p'+1,q'-1) = coeff2(mul_z_sub_w f)(p'+1)(q')
      have h2 : F p' q' - F (p' + 1) (q' - 1) =
          coeff2 (mul_z_sub_w f) (p' + 1) q' := by
        have hF2 : F (p' + 1) (q' - 1) = ∑ j ∈ Finset.range (N + 1),
            (↑(intBinomial (-p' - 2) j) : A) *
              coeff2 (mul_z_sub_w_pow f j) (-1) (p' + q' + ↑j + 1) := by
          apply Finset.sum_congr rfl; intro j _
          congr 1
          · congr 1; congr 1; omega
          · congr 1; omega
        rw [hF2, ← Finset.sum_sub_distrib]; simp_rw [← sub_mul]
        rw [Finset.sum_range_succ']
        simp only [intBinomial_zero, Int.cast_one, sub_self, zero_mul, add_zero]
        rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.range N) => show
            ((↑(intBinomial (-p' - 1) (j + 1)) : A) - ↑(intBinomial (-p' - 2) (j + 1))) * _ =
            (↑(intBinomial (-p' - 2) j) : A) * _ from by
          congr 1; rw [← Int.cast_sub]; congr 1
          have := intBinomial_pascal (-p' - 2) j
          rw [show (-p' - 2 : ℤ) + 1 = -p' - 1 from by omega] at this; omega]
        rw [ih_g (p' + 1) q']
        apply Finset.sum_congr rfl; intro j _
        rw [hgj j]; congr 1
        · congr 1; congr 1; omega
        · congr 1; push_cast; omega
      have h_eq := (sub_eq_zero.mpr (show coeff2 f p' q' - coeff2 f (p' + 1) (q' - 1) =
          F p' q' - F (p' + 1) (q' - 1) from by rw [h1, h2]))
      rw [sub_sub_sub_comm] at h_eq; exact sub_eq_zero.mp h_eq
    -- Step 3: Conclude D ≡ 0
    intro p' q'
    have := antidiag_const_fun D hshift p' q'
    rw [this, heval]

end FormalDelta
