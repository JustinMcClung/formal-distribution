/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FormalDistribution.Locality
import Mathlib.Algebra.Algebra.Basic

/-!
# Fourier Transform (Section 1.5)

The Fourier transform `F_z^λ` converts formal distributions in `z` to polynomials in `λ`,
providing a generating function for the modes:
`F_z^λ(a(z)) = Res_z e^{λz} a(z) = ∑_{n≥0} λ^n/n! · a_n`.

This requires the coefficient ring to be a `ℚ`-algebra (for division by factorials).

## Main definitions

* `fourierTransformCoeff` - the n-th coefficient `(1/n!) · a_n` of the Fourier transform
* `twoVarFourierCoeff` - the j-th coefficient of the two-variable Fourier transform

## Main results

* `fourierTransformCoeff_deriv_zero` - F(∂a) has zero constant term
* `fourierTransformCoeff_deriv` - F(∂a)_n = -F(a)_{n-1} (Proposition 1.5.2)
* `fourierTransformCoeff_reflect` - F(a(-z))_n = (-1)^{n+1} F(a)_n (Proposition 1.5.2(3))
* `twoVarFourierCoeff_commutator_eq` - two-variable FT of commutator equals scaled j-th product
* `twoVarFourierCoeff_deriv_fst` - F(∂_z f)_{j+1} = -F(f)_j (Proposition 1.5.4(2))
* `twoVarFourierCoeff_eq_zero_of_local` - lambda-bracket is polynomial for local distributions

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Section 1.5
-/

open scoped BigOperators

namespace FormalDelta

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-! ## One-variable Fourier transform (Definition 1.5.1) -/

/-- The n-th coefficient of the one-variable Fourier transform.

For a distribution `a(z) = ∑_n a_n z^{-n-1}`, the Fourier transform is
`F_z^λ(a) = ∑_{n≥0} (λ^n / n!) · a_n`. This function gives the n-th coefficient
`(1/n!) · a_n` where `a_n = fourierMode a n`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.5.1
-/
noncomputable def fourierTransformCoeff (a : FormalDist1 A) (n : ℕ) : A :=
  algebraMap ℚ A (1 / ↑(Nat.factorial n)) * fourierMode a ↑n

/-- The 0-th Fourier transform coefficient of a derivative is zero.

This is the `n = 0` case of Proposition 1.5.2: since the Fourier transform
maps `∂_z` to multiplication by `-λ`, the constant term of `F(∂a)` vanishes. -/
theorem fourierTransformCoeff_deriv_zero (a : FormalDist1 A) :
    fourierTransformCoeff (FormalDistribution.deriv a 0) 0 = 0 := by
  unfold fourierTransformCoeff
  rw [fourierMode_deriv]
  simp [mul_zero]

/-- **Proposition 1.5.2**: The Fourier transform converts derivatives to multiplication by `-λ`.

At the coefficient level: the n-th coefficient of `F(∂a)` equals minus the `(n-1)`-th
coefficient of `F(a)`, for `n ≥ 1`.

This is the formal-variable analogue of the classical property that the Fourier transform
converts differentiation to multiplication by the dual variable.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.5.2
-/
theorem fourierTransformCoeff_deriv (a : FormalDist1 A) (n : ℕ) (hn : n ≥ 1) :
    fourierTransformCoeff (FormalDistribution.deriv a 0) n =
    -fourierTransformCoeff a (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [fourierTransformCoeff, Nat.add_sub_cancel]
  rw [fourierMode_deriv, show (↑(k + 1) : ℤ) - 1 = ↑k from by push_cast; omega]
  -- Goal: algebraMap ℚ A (1/↑((k+1)!)) * ((-(↑(k+1) : ℤ)) • fourierMode a ↑k)
  --     = -(algebraMap ℚ A (1/↑(k!)) * fourierMode a ↑k)
  rw [zsmul_eq_mul, Int.cast_neg, Int.cast_natCast]
  -- LHS: algebraMap ... * (-(↑(k+1) : A) * fourierMode a ↑k)
  rw [neg_mul, mul_neg, ← mul_assoc]
  -- Both sides now: -(... * fourierMode a ↑k)
  congr 1
  congr 1
  -- Goal: algebraMap ℚ A (1 / ↑((k+1)!)) * ↑(k+1) = algebraMap ℚ A (1 / ↑(k!))
  rw [← map_natCast (algebraMap ℚ A) (k + 1), ← map_mul]
  congr 1
  -- ℚ arithmetic: (1 / ↑((k+1)!)) * ↑(k+1) = 1 / ↑(k!)
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hk1 : (↑(k + 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [one_div, one_div, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hk1, mul_one]

/-! ## Reflection symmetry (Proposition 1.5.2(3)) -/

/-- The reflection of a 1D formal distribution: `a(z) ↦ a(-z)`.

At the coefficient level: `(reflect a)_m = (-1)^|m| · a_m`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Section 1.5
-/
def reflect (a : FormalDist1 A) : FormalDist1 A where
  coeff := fun idx => (-1 : A) ^ (idx 0).natAbs * a.coeff idx
  support_finite := by
    apply Set.Finite.subset a.support_finite
    intro idx hne
    simp only [Set.mem_setOf_eq] at hne ⊢
    intro h; exact hne (by rw [h, mul_zero])

omit [Algebra ℚ A] in
/-- The Fourier mode of the reflected distribution:
`(a(-z))_n = (-1)^{n+1} · a_n`. -/
theorem fourierMode_reflect (a : FormalDist1 A) (n : ℤ) :
    fourierMode (reflect a) n = (-1 : A) ^ (n + 1).natAbs * fourierMode a n := by
  simp only [fourierMode, reflect]
  show (-1 : A) ^ (-n - 1).natAbs * a.coeff _ = (-1 : A) ^ (n + 1).natAbs * a.coeff _
  congr 1; congr 1
  show (-n - 1).natAbs = (n + 1).natAbs
  rw [show (-n - 1 : ℤ) = -(n + 1) from by omega, Int.natAbs_neg]

/-- **Proposition 1.5.2(3)**: Reflection symmetry of the Fourier transform.

`F_z^λ(a(-z)) = -F_z^{-λ}(a(z))`

At the coefficient level: the n-th FT coefficient of the reflected distribution
equals `(-1)^{n+1}` times the n-th FT coefficient of the original.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.5.2(3)
-/
theorem fourierTransformCoeff_reflect (a : FormalDist1 A) (n : ℕ) :
    fourierTransformCoeff (reflect a) n =
    (-1 : A) ^ (n + 1) * fourierTransformCoeff a n := by
  unfold fourierTransformCoeff
  rw [fourierMode_reflect, show (↑n + 1 : ℤ).natAbs = n + 1 from by omega]
  exact mul_left_comm _ _ _

/-! ## Two-variable Fourier transform (Definition 1.5.3) -/

/-- The j-th coefficient of the two-variable Fourier transform of a 2D distribution.

`F_{z,w}^λ(f) = ∑_{j≥0} λ^j/j! · Res_z (z-w)^j f(z,w)`

The j-th coefficient is `(1/j!) · Res_z (z-w)^j f`, which is a 1D generalized
distribution in `w`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.5.3
-/
noncomputable def twoVarFourierCoeff (f : GenFormalDist2 A) (j : ℕ) : GenFormalDist1 A :=
  algebraMap ℚ A (1 / ↑(Nat.factorial j)) •
    GeneralizedFormalDistribution.residueAt 0 (mul_z_sub_w_pow f j)

/-- **Proposition 1.5.4** (coefficient level): The two-variable Fourier transform of
the commutator equals the scaled j-th product.

`F_{z,w}^λ([a(z), b(w)])_j = (1/j!) · a_{(j)} b`

This shows that the lambda-bracket `[a_λ b] = F_{z,w}^λ([a(z), b(w)])` packages
the j-th products with divided-power coefficients.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.5.4
-/
theorem twoVarFourierCoeff_commutator_eq (a b : FormalDist1 A) (j : ℕ) :
    twoVarFourierCoeff (formalCommutator a b).toGeneralized j =
    algebraMap ℚ A (1 / ↑(Nat.factorial j)) • nthProduct a b j := by
  rfl

/-! ## Two-variable FT derivative properties (Proposition 1.5.4(2)) -/

/-- The 0-th two-variable FT coefficient of `∂_z f` vanishes. -/
theorem twoVarFourierCoeff_deriv_fst_zero (f : GenFormalDist2 A) :
    twoVarFourierCoeff (GeneralizedFormalDistribution.deriv f 0) 0 = 0 := by
  unfold twoVarFourierCoeff
  rw [show mul_z_sub_w_pow (GeneralizedFormalDistribution.deriv f 0) 0 =
      GeneralizedFormalDistribution.deriv f 0 from rfl,
    residueAt_deriv_fst]
  ext idx; show algebraMap ℚ A _ * (0 : A) = 0; exact mul_zero _

/-- **Proposition 1.5.4(2)**: The two-variable Fourier transform maps `∂_z` to
multiplication by `-λ`.

At the coefficient level: `F_{z,w}^λ(∂_z f)_{j+1} = -F_{z,w}^λ(f)_j`.

Combined with the `j = 0` case `twoVarFourierCoeff_deriv_fst_zero`, this shows
that the full two-variable FT satisfies `F(∂_z f) = -λ · F(f)`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Proposition 1.5.4(2)
-/
theorem twoVarFourierCoeff_deriv_fst (f : GenFormalDist2 A) (j : ℕ) :
    twoVarFourierCoeff (GeneralizedFormalDistribution.deriv f 0) (j + 1) =
    -twoVarFourierCoeff f j := by
  ext idx
  show algebraMap ℚ A (1 / ↑(Nat.factorial (j + 1))) *
      coeff2 (mul_z_sub_w_pow (GeneralizedFormalDistribution.deriv f 0) (j + 1)) (-1) (idx 0) =
    -(algebraMap ℚ A (1 / ↑(Nat.factorial j)) *
      coeff2 (mul_z_sub_w_pow f j) (-1) (idx 0))
  rw [integration_by_parts, neg_mul, mul_neg, ← mul_assoc]
  congr 1; congr 1
  -- Goal: algebraMap ℚ A (1/↑((j+1)!)) * ↑(j+1) = algebraMap ℚ A (1/↑(j!))
  rw [← map_natCast (algebraMap ℚ A) (j + 1), ← map_mul]
  congr 1
  -- ℚ arithmetic: (1/↑((j+1)!)) * ↑(j+1) = 1/↑(j!)
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hj1 : (↑(j + 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [one_div, one_div, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hj1, mul_one]

/-- The lambda-bracket coefficients vanish for `j ≥ N` when the distributions
are mutually local of order `N`. This means the lambda-bracket is a polynomial in `λ`. -/
theorem twoVarFourierCoeff_eq_zero_of_local (a b : FormalDist1 A) (N j : ℕ)
    (hlocal : IsLocalOfOrder (formalCommutator a b).toGeneralized N) (hj : j ≥ N) :
    twoVarFourierCoeff (formalCommutator a b).toGeneralized j = 0 := by
  rw [twoVarFourierCoeff_commutator_eq, nthProduct_eq_zero_of_local a b N j hlocal hj]
  ext idx
  show algebraMap ℚ A _ * (0 : A) = 0
  exact mul_zero _

end FormalDelta
