/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FormalDistribution.Deriv

/-!
# Fourier Expansion of Formal Distributions

This file defines the Fourier expansion, Fourier modes, and residue of
one-variable formal distributions, along with their properties.

## Main definitions

* `fourierExpansion` - the coefficient function `a(z) = ∑ aₙ zⁿ ↦ n ↦ aₙ`
* `fourierMode` - the mode `a_{(n)} = a_{-n-1}`
* `residue` - the residue `Res_z a(z) = a_{-1}`

## Main results

* `fourierExpansion_deriv` - Fourier expansion of the derivative
* `fourierMode_deriv` - Fourier mode of the derivative
* `residue_deriv` - residue of a derivative is zero

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.1.3
-/

variable {A : Type*} [Ring A]

/-! ## 1.1.3 Fourier expansion -/

/-- Fourier expansion of a one-variable formal distribution.

For `a(z) = ∑ aₙ zⁿ`, this maps `n ↦ aₙ`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.1.3
-/
def fourierExpansion (a : FormalDist1 A) : ℤ → A :=
  fun n => a.coeff (fun _ => n)

/-- Fourier modes of a one-variable formal distribution.

Defined as `a_{(n)} = Res_{z} z^n a(z) = a_{-n-1}`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.1.3
-/
def fourierMode (a : FormalDist1 A) (n : ℤ) : A :=
  a.coeff (fun _ => -n - 1)

/-- Residue of a one-variable formal distribution.

`Res_z a(z) = a_{-1}`, the coefficient of `z^{-1}`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.1.3
-/
def residue (a : FormalDist1 A) : A :=
  a.coeff (fun _ => -1)

/-! ### Linearity properties -/

/-- Fourier expansion distributes over addition. -/
@[simp]
theorem fourierExpansion_add (a b : FormalDist1 A) (n : ℤ) :
    fourierExpansion (a + b) n = fourierExpansion a n + fourierExpansion b n := by
  rfl

/-- Fourier expansion commutes with scalar multiplication. -/
@[simp]
theorem fourierExpansion_smul (c : A) (a : FormalDist1 A) (n : ℤ) :
    fourierExpansion (c • a) n = c * fourierExpansion a n := by
  rfl

/-- Fourier expansion of zero is zero. -/
@[simp]
theorem fourierExpansion_zero (n : ℤ) :
    fourierExpansion (0 : FormalDist1 A) n = 0 := by
  rfl

/-- Fourier mode distributes over addition. -/
@[simp]
theorem fourierMode_add (a b : FormalDist1 A) (n : ℤ) :
    fourierMode (a + b) n = fourierMode a n + fourierMode b n := by
  rfl

/-- Fourier mode commutes with scalar multiplication. -/
@[simp]
theorem fourierMode_smul (c : A) (a : FormalDist1 A) (n : ℤ) :
    fourierMode (c • a) n = c * fourierMode a n := by
  rfl

/-- Fourier mode of zero is zero. -/
@[simp]
theorem fourierMode_zero (n : ℤ) :
    fourierMode (0 : FormalDist1 A) n = 0 := by
  rfl

/-- Residue distributes over addition. -/
@[simp]
theorem residue_add (a b : FormalDist1 A) :
    residue (a + b) = residue a + residue b := by
  rfl

/-- Residue commutes with scalar multiplication. -/
@[simp]
theorem residue_smul (c : A) (a : FormalDist1 A) :
    residue (c • a) = c * residue a := by
  rfl

/-- Residue of zero is zero. -/
@[simp]
theorem residue_zero :
    residue (0 : FormalDist1 A) = 0 := by
  rfl

/-! ### Relationship between Fourier modes and coefficients -/

/-- Fourier expansion extracts the coefficient directly. -/
theorem fourierExpansion_eq_coeff (a : FormalDist1 A) (n : ℤ) :
    fourierExpansion a n = a.coeff (fun _ => n) := by
  rfl

/-- Fourier mode is the coefficient at `-n-1`. -/
theorem fourierMode_eq_coeff (a : FormalDist1 A) (n : ℤ) :
    fourierMode a n = a.coeff (fun _ => -n - 1) := by
  rfl

/-- Residue is the coefficient at `-1`. -/
theorem residue_eq_coeff (a : FormalDist1 A) :
    residue a = a.coeff (fun _ => -1) := by
  rfl

/-- Residue equals the 0-th Fourier mode. -/
theorem residue_eq_fourierMode_zero (a : FormalDist1 A) :
    residue a = fourierMode a 0 := by
  rfl

/-! ### Derivatives and Fourier modes -/

/-- The Fourier expansion of the derivative satisfies
`(∂_z a)_n = (n+1) · a_{n+1}`. -/
theorem fourierExpansion_deriv (a : FormalDist1 A) (n : ℤ) :
    fourierExpansion (FormalDistribution.deriv a 0) n = (n + 1 : ℤ) • fourierExpansion a (n + 1) := by
  unfold fourierExpansion FormalDistribution.deriv
  simp only []
  have h : Function.update (fun _ : Fin 1 => n) 0 ((fun _ : Fin 1 => n) 0 + 1) = (fun _ : Fin 1 => n + 1) := by
    funext i
    fin_cases i
    simp [Function.update]
  simp only [h]

/-- The Fourier mode of the derivative satisfies
`(∂_z a)_{(n)} = -n · a_{(n-1)}`. -/
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

/-- The residue of a derivative is zero.

This is the formal analogue of `∫ f'(z) dz = 0` on a closed contour. -/
theorem residue_deriv (a : FormalDist1 A) :
    residue (FormalDistribution.deriv a 0) = 0 := by
  unfold residue FormalDistribution.deriv
  simp only [show (-1 : ℤ) + 1 = 0 by norm_num, zero_smul]

/-- The residue of any iterated derivative is zero. -/
theorem residue_iteratedDeriv (a : FormalDist1 A) (k : ℕ) (hk : k > 0) :
    residue (FormalDistribution.iteratedDeriv a 0 k) = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    simp [FormalDistribution.iteratedDeriv]
    rw [residue_deriv]

/-- Fourier expansion is linear for linear combinations. -/
theorem fourierExpansion_linear (a b : FormalDist1 A) (c d : A) (n : ℤ) :
    fourierExpansion (c • a + d • b) n = c * fourierExpansion a n + d * fourierExpansion b n := by
  simp

/-- Fourier mode is linear for linear combinations. -/
theorem fourierMode_linear (a b : FormalDist1 A) (c d : A) (n : ℤ) :
    fourierMode (c • a + d • b) n = c * fourierMode a n + d * fourierMode b n := by
  simp

/-- Residue is linear for linear combinations. -/
theorem residue_linear (a b : FormalDist1 A) (c d : A) :
    residue (c • a + d • b) = c * residue a + d * residue b := by
  simp

/-! ### More Fourier mode relationships -/

/-- Fourier expansion and Fourier mode are related by index transformation. -/
theorem fourierExpansion_eq_fourierMode_neg (a : FormalDist1 A) (n : ℤ) :
    fourierExpansion a n = fourierMode a (-n - 1) := by
  unfold fourierExpansion fourierMode
  congr 1
  funext i
  fin_cases i
  simp

/-- Coefficient extraction via Fourier expansion. -/
theorem coeff_eq_fourierExpansion (a : FormalDist1 A) (n : ℤ) :
    a.coeff (fun _ => n) = fourierExpansion a n := by
  rfl

/-- Zero distribution has all Fourier modes zero. -/
theorem fourierMode_zero_dist (n : ℤ) :
    fourierMode (0 : FormalDist1 A) n = 0 := by
  rfl

/-- Zero distribution has all Fourier expansions zero. -/
theorem fourierExpansion_zero_dist (n : ℤ) :
    fourierExpansion (0 : FormalDist1 A) n = 0 := by
  rfl
