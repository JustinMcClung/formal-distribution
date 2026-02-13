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
          | succ j' => simp [intBinomial_zero_left])
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
        -- Rewrite F(p'+1)(q'-1) with simplified indices
        have hF2 : F (p' + 1) (q' - 1) = ∑ j ∈ Finset.range (N + 1),
            (↑(intBinomial (-p' - 2) j) : A) *
              coeff2 (mul_z_sub_w_pow f j) (-1) (p' + q' + ↑j + 1) := by
          apply Finset.sum_congr rfl; intro j _
          congr 1
          · congr 1; congr 1; omega  -- -(p'+1)-1 = -p'-2
          · congr 1; omega  -- (p'+1)+(q'-1)+j+1 = p'+q'+j+1
        rw [hF2, ← Finset.sum_sub_distrib]
        -- Factor: a*c - b*c = (a - b)*c
        simp_rw [← sub_mul]
        -- Split off j=0 term (vanishes since intBinomial(_,0) = 1)
        rw [Finset.sum_range_succ']
        simp only [intBinomial_zero, Int.cast_one, sub_self, zero_mul, add_zero]
        -- Apply Pascal: C(-p'-1, j+1) - C(-p'-2, j+1) = C(-p'-2, j)
        have hpascal_rw : ∀ j ∈ Finset.range N,
            ((↑(intBinomial (-p' - 1) (j + 1)) : A) - ↑(intBinomial (-p' - 2) (j + 1))) *
              coeff2 (mul_z_sub_w_pow f (j + 1)) (-1) (p' + q' + ↑(j + 1) + 1) =
            (↑(intBinomial (-p' - 2) j) : A) *
              coeff2 (mul_z_sub_w_pow f (j + 1)) (-1) (p' + q' + ↑(j + 1) + 1) := by
          intro j _
          congr 1
          rw [← Int.cast_sub]
          congr 1
          have h_pascal := intBinomial_pascal (-p' - 2) j
          rw [show (-p' - 2 : ℤ) + 1 = -p' - 1 from by omega] at h_pascal
          omega
        rw [Finset.sum_congr rfl hpascal_rw]
        -- Match with IH for g = mul_z_sub_w f
        rw [ih_g (p' + 1) q']
        apply Finset.sum_congr rfl; intro j _
        rw [hgj j]
        congr 1
        · congr 1; congr 1; omega  -- -(p'+1)-1 = -p'-2
        · congr 1; push_cast; omega  -- (p'+1)+q'+j+1 = p'+q'+(j+1)+1
      -- Combine: a - b = c - d → a - c = b - d
      have h_eq : coeff2 f p' q' - coeff2 f (p' + 1) (q' - 1) =
          F p' q' - F (p' + 1) (q' - 1) := by rw [h1, h2]
      have h0 := sub_eq_zero.mpr h_eq
      rw [sub_sub_sub_comm] at h0
      exact sub_eq_zero.mp h0
    -- Step 3: Conclude D ≡ 0
    intro p' q'
    have := antidiag_const_fun D hshift p' q'
    rw [this, heval]

end FormalDelta
