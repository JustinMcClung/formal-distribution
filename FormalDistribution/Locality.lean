/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FormalDistribution.Delta
import FormalDistribution.Decomposition

/-!
# Locality (Section 1.4)

This file defines the notion of mutual locality for formal distributions and proves
that the formal delta distribution and its derivatives are local.

## Main definitions

* `externalProduct` - the formal product `a(z)·b(w)` of two 1D distributions as a 2D distribution
* `formalCommutator` - the commutator `[a(z), b(w)] = a(z)b(w) - b(w)a(z)`
* `IsLocal` - a 2D generalized distribution `f` is local if `(z-w)^N · f = 0` for some `N`
* `MutuallyLocal` - two 1D distributions are mutually local

## Main results

* `formalDelta_isLocal` - `δ(z,w)` is local with `N = 1`
* `iteratedDeriv_formalDelta_isLocal` - `∂_w^n δ(z,w)` is local with `N = n + 1`
* `isLocal_deriv_snd` - derivatives of local distributions are local
* `commRing_mutuallyLocal` - all pairs are mutually local over a commutative ring
* `leibniz_deriv_fst_coeff2` - Leibniz rule for `∂_z` and `(z-w)^j`
* `integration_by_parts` - `Res_z (z-w)^{j+1} ∂_z f = -(j+1) · Res_z (z-w)^j f`

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Section 1.4
-/

open scoped BigOperators

variable {A : Type*} [Ring A]

namespace FormalDelta

/-! ## External product of 1D distributions -/

/-- The external (tensor) product of two 1D distributions `a(z)` and `b(w)`.

The coefficient at `(p, q)` is `a_p · b_q`. This is the formal product `a(z) · b(w)`
viewed as a 2D distribution. -/
noncomputable def externalProduct (a b : FormalDist1 A) : FormalDist2 A where
  coeff := fun idx => a.coeff (fun _ => idx 0) * b.coeff (fun _ => idx 1)
  support_finite := by
    have ha := a.support_finite
    have hb := b.support_finite
    have h_subset : {idx : Fin 2 → ℤ |
        a.coeff (fun _ => idx 0) * b.coeff (fun _ => idx 1) ≠ 0} ⊆
      (fun (p : (Fin 1 → ℤ) × (Fin 1 → ℤ)) => fun i : Fin 2 =>
        if i = 0 then p.1 0 else p.2 0) ''
      ({idx_a | a.coeff idx_a ≠ 0} ×ˢ {idx_b | b.coeff idx_b ≠ 0}) := by
      intro idx hne
      simp only [Set.mem_setOf_eq] at hne
      have ha_ne : a.coeff (fun _ => idx 0) ≠ 0 := left_ne_zero_of_mul hne
      have hb_ne : b.coeff (fun _ => idx 1) ≠ 0 := right_ne_zero_of_mul hne
      exact ⟨(fun _ => idx 0, fun _ => idx 1),
        ⟨ha_ne, hb_ne⟩,
        by ext i; fin_cases i <;> simp⟩
    exact Set.Finite.subset (Set.Finite.image _ (ha.prod hb)) h_subset

/-- Coefficient of the external product. -/
@[simp]
theorem externalProduct_coeff (a b : FormalDist1 A) (idx : Fin 2 → ℤ) :
    (externalProduct a b).coeff idx =
    a.coeff (fun _ => idx 0) * b.coeff (fun _ => idx 1) := rfl

/-- The formal commutator `[a(z), b(w)] = a(z)b(w) - b(w)a(z)` as a 2D distribution.

The coefficient at `(p, q)` is `a_p · b_q - b_q · a_p`. The multiplication order
in the coefficient ring is reversed (not the index order), matching the standard
commutator `a(z)b(w) - b(w)a(z)` in the formal distribution sense. -/
noncomputable def formalCommutator (a b : FormalDist1 A) : FormalDist2 A where
  coeff := fun idx =>
    a.coeff (fun _ => idx 0) * b.coeff (fun _ => idx 1) -
    b.coeff (fun _ => idx 1) * a.coeff (fun _ => idx 0)
  support_finite := by
    have ha := a.support_finite
    have hb := b.support_finite
    apply Set.Finite.subset (Set.Finite.image
      (fun (p : (Fin 1 → ℤ) × (Fin 1 → ℤ)) => fun i : Fin 2 =>
        if i = 0 then p.1 0 else p.2 0)
      (ha.prod hb))
    intro idx hne
    simp only [Set.mem_setOf_eq] at hne
    have : a.coeff (fun _ => idx 0) * b.coeff (fun _ => idx 1) ≠ 0 ∨
           b.coeff (fun _ => idx 1) * a.coeff (fun _ => idx 0) ≠ 0 := by
      by_contra h; push_neg at h; exact hne (by rw [h.1, h.2, sub_self])
    rcases this with h | h
    · exact ⟨(fun _ => idx 0, fun _ => idx 1),
        ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩,
        by ext i; fin_cases i <;> simp⟩
    · exact ⟨(fun _ => idx 0, fun _ => idx 1),
        ⟨right_ne_zero_of_mul h, left_ne_zero_of_mul h⟩,
        by ext i; fin_cases i <;> simp⟩

/-! ## Locality -/

/-- A 2D generalized formal distribution `f` is **local** if there exists `N`
such that `(z-w)^N · f = 0`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.4.1
-/
def IsLocal (f : GenFormalDist2 A) : Prop :=
  ∃ N : ℕ, mul_z_sub_w_pow f N = 0

/-- A 2D generalized distribution `f` is local with order at most `N`. -/
def IsLocalOfOrder (f : GenFormalDist2 A) (N : ℕ) : Prop :=
  mul_z_sub_w_pow f N = 0

/-- Two 1D formal distributions `a(z)` and `b(w)` are **mutually local** if
their commutator `[a(z), b(w)] = a(z)b(w) - b(w)a(z)` is annihilated by
some power of `(z-w)`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Definition 1.4.1
-/
def MutuallyLocal (a b : FormalDist1 A) : Prop :=
  IsLocal (formalCommutator a b).toGeneralized

/-! ## Example 1.4.2: Delta and its derivatives are local -/

/-- The formal delta `δ(z,w)` is local with `N = 1`. -/
theorem formalDelta_isLocal : IsLocal (formalDelta : GenFormalDist2 A) :=
  ⟨1, by rw [mul_z_sub_w_pow]; exact mul_z_sub_w_formalDelta⟩

/-- The `n`-th derivative `∂_w^n δ(z,w)` is local with `N = n + 1`. -/
theorem iteratedDeriv_formalDelta_isLocal (n : ℕ) :
    IsLocal (GeneralizedFormalDistribution.iteratedDeriv formalDelta 1 n : GenFormalDist2 A) :=
  ⟨n + 1, mul_z_sub_w_pow_succ_iteratedDeriv_formalDelta_eq_zero n⟩

/-! ## Linearity of mul_z_sub_w -/

/-- `(z-w) · 0 = 0`. -/
theorem mul_z_sub_w_zero : mul_z_sub_w (0 : GenFormalDist2 A) = 0 := by
  ext idx; show (0 : A) - 0 = 0; exact sub_self 0

/-- `(z-w)` distributes over addition. -/
theorem mul_z_sub_w_add (a b : GenFormalDist2 A) :
    mul_z_sub_w (a + b) = mul_z_sub_w a + mul_z_sub_w b := by
  ext idx
  -- (a+b)(p-1,q) - (a+b)(p,q-1) = (a(p-1,q) - a(p,q-1)) + (b(p-1,q) - b(p,q-1))
  change a.coeff _ + b.coeff _ - (a.coeff _ + b.coeff _) =
         (a.coeff _ - a.coeff _) + (b.coeff _ - b.coeff _)
  abel

/-- `(z-w)^N · 0 = 0`. -/
theorem mul_z_sub_w_pow_zero (N : ℕ) : mul_z_sub_w_pow (0 : GenFormalDist2 A) N = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => show mul_z_sub_w (mul_z_sub_w_pow 0 N) = 0; rw [ih, mul_z_sub_w_zero]

/-- `(z-w)^N` distributes over addition. -/
theorem mul_z_sub_w_pow_add (a b : GenFormalDist2 A) (N : ℕ) :
    mul_z_sub_w_pow (a + b) N = mul_z_sub_w_pow a N + mul_z_sub_w_pow b N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    show mul_z_sub_w (mul_z_sub_w_pow (a + b) N) =
         mul_z_sub_w (mul_z_sub_w_pow a N) + mul_z_sub_w (mul_z_sub_w_pow b N)
    rw [ih, mul_z_sub_w_add]

/-- `a + 0 = a` for generalized 2D distributions. -/
private theorem gen_add_zero (a : GenFormalDist2 A) : a + 0 = a := by
  ext idx; show a.coeff idx + 0 = a.coeff idx; exact add_zero _

/-- `∂_w 0 = 0` for generalized 2D distributions. -/
private theorem gen_deriv_snd_zero :
    GeneralizedFormalDistribution.deriv (0 : GenFormalDist2 A) (1 : Fin 2) = 0 := by
  ext idx; show (_ : ℤ) • (0 : A) = 0; exact smul_zero _

/-! ## Derivative-locality interaction -/

/-- Helper: coefficient of `∂_w f` in terms of `coeff2`. -/
private lemma deriv_snd_coeff2 (f : GenFormalDist2 A) (p q : ℤ) :
    coeff2 (GeneralizedFormalDistribution.deriv f (1 : Fin 2)) p q =
    (q + 1 : ℤ) • coeff2 f p (q + 1) := by
  simp only [coeff2, GeneralizedFormalDistribution.deriv]
  -- After simp, the LHS has `if (1 : Fin 2) = 0 then p else q` which reduces to `q`
  simp only [show ¬((1 : Fin 2) = (0 : Fin 2)) from by decide, ite_false]
  -- Now goal: (q + 1) • f.coeff (update ... 1 (q + 1)) = (q + 1) • f.coeff (...)
  congr 2
  funext i; fin_cases i
  · simp [Function.update, show ¬((0 : Fin 2) = 1) from by decide]
  · simp [Function.update]

/-- Multiplying by `(z-w)` commutes with taking the `w`-derivative up to a correction term.

More precisely: `(z-w) · ∂_w f = ∂_w ((z-w) · f) + f`. -/
lemma mul_z_sub_w_deriv_snd (f : GenFormalDist2 A) :
    mul_z_sub_w (GeneralizedFormalDistribution.deriv f 1) =
    GeneralizedFormalDistribution.deriv (mul_z_sub_w f) 1 +
    f := by
  apply coeff2_ext; intro p q
  -- Expand LHS using coeff2 lemmas
  rw [mul_z_sub_w_coeff2, deriv_snd_coeff2, deriv_snd_coeff2,
      show (q - 1 + 1 : ℤ) = q from by omega]
  -- LHS = (q + 1) • coeff2 f (p - 1) (q + 1) - q • coeff2 f p q
  -- Expand RHS: coeff2 (a + b) p q = coeff2 a p q + coeff2 b p q (definitional)
  change _ = coeff2 (GeneralizedFormalDistribution.deriv (mul_z_sub_w f) (1 : Fin 2)) p q +
             coeff2 f p q
  rw [deriv_snd_coeff2, mul_z_sub_w_coeff2, show (q + 1 - 1 : ℤ) = q from by omega]
  -- RHS = (q + 1) • (coeff2 f (p - 1) (q + 1) - coeff2 f p q) + coeff2 f p q
  -- Goal: (q+1)•X - q•Y = (q+1)•(X - Y) + Y where X = coeff2 f (p-1)(q+1), Y = coeff2 f p q
  rw [smul_sub]
  -- Goal: (q+1)•X - q•Y = (q+1)•X - (q+1)•Y + Y
  have key : (q + 1 : ℤ) • coeff2 f p q = q • coeff2 f p q + coeff2 f p q := by
    rw [add_zsmul, one_zsmul]
  rw [key]; abel

/-! ## z-derivative interaction with mul_z_sub_w -/

/-- Helper: coefficient of `∂_z f` in terms of `coeff2`. -/
private lemma deriv_fst_coeff2 (f : GenFormalDist2 A) (p q : ℤ) :
    coeff2 (GeneralizedFormalDistribution.deriv f (0 : Fin 2)) p q =
    (p + 1 : ℤ) • coeff2 f (p + 1) q := by
  unfold coeff2 GeneralizedFormalDistribution.deriv
  dsimp only []
  congr 2
  funext i; fin_cases i
  · simp [Function.update]
  · simp [Function.update, show ¬((1 : Fin 2) = (0 : Fin 2)) from by decide]

/-- Multiplying by `(z-w)` commutes with taking the `z`-derivative up to a correction term.

`(z-w) · ∂_z f = ∂_z ((z-w) · f) - f` -/
lemma mul_z_sub_w_deriv_fst (f : GenFormalDist2 A) :
    mul_z_sub_w (GeneralizedFormalDistribution.deriv f 0) =
    GeneralizedFormalDistribution.deriv (mul_z_sub_w f) 0 - f := by
  apply coeff2_ext; intro p q
  rw [mul_z_sub_w_coeff2, deriv_fst_coeff2, deriv_fst_coeff2,
      show (p - 1 + 1 : ℤ) = p from by omega]
  -- LHS = p • coeff2 f p q - (p+1) • coeff2 f (p+1) (q-1)
  -- Expand RHS
  change _ = coeff2 (GeneralizedFormalDistribution.deriv (mul_z_sub_w f) (0 : Fin 2)) p q -
             coeff2 f p q
  rw [deriv_fst_coeff2, mul_z_sub_w_coeff2, show (p + 1 - 1 : ℤ) = p from by omega]
  -- RHS = (p+1) • (coeff2 f p q - coeff2 f (p+1)(q-1)) - coeff2 f p q
  rw [smul_sub]
  have key : (p + 1 : ℤ) • coeff2 f p q = p • coeff2 f p q + coeff2 f p q := by
    rw [add_zsmul, one_zsmul]
  rw [key]; abel

/-- The residue in the `z`-variable of a `z`-derivative vanishes:
`Res_z ∂_z f = 0`.

This is because the coefficient at `z^{-1}` of `∂_z f` involves `(-1+1) = 0`. -/
lemma residueAt_deriv_fst (f : GenFormalDist2 A) :
    GeneralizedFormalDistribution.residueAt 0
      (GeneralizedFormalDistribution.deriv f 0) = 0 := by
  ext idx
  change coeff2 (GeneralizedFormalDistribution.deriv f (0 : Fin 2)) (-1) (idx 0) = 0
  rw [deriv_fst_coeff2, show (-1 : ℤ) + 1 = 0 from by omega]
  exact zero_smul _ _

/-! ## Integration by parts -/

/-- Leibniz rule at the coefficient level: for all `j`, `p`, `q`,
`coeff2 ((z-w)^{j+1} ∂_z f) p q = (p+1) · coeff2 ((z-w)^{j+1} f) (p+1) q - (j+1) · coeff2 ((z-w)^j f) p q`.

Specializing to `p = -1` gives integration by parts. -/
theorem leibniz_deriv_fst_coeff2 (f : GenFormalDist2 A) (j : ℕ) (p q : ℤ) :
    coeff2 (mul_z_sub_w_pow (GeneralizedFormalDistribution.deriv f 0) (j + 1)) p q =
    (p + 1 : ℤ) • coeff2 (mul_z_sub_w_pow f (j + 1)) (p + 1) q -
    (↑(j + 1 : ℕ) : A) * coeff2 (mul_z_sub_w_pow f j) p q := by
  induction j generalizing p q with
  | zero =>
    show coeff2 (mul_z_sub_w (GeneralizedFormalDistribution.deriv f 0)) p q =
         (p + 1 : ℤ) • coeff2 (mul_z_sub_w f) (p + 1) q - (↑(1 : ℕ) : A) * coeff2 f p q
    rw [mul_z_sub_w_coeff2, deriv_fst_coeff2, deriv_fst_coeff2,
        show (p - 1 + 1 : ℤ) = p from by omega,
        mul_z_sub_w_coeff2, show (p + 1 - 1 : ℤ) = p from by omega]
    simp only [Nat.cast_one, one_mul, smul_sub]
    have key : (p + 1 : ℤ) • coeff2 f p q = p • coeff2 f p q + coeff2 f p q := by
      rw [add_zsmul, one_zsmul]
    rw [key]; abel
  | succ j ih =>
    -- Expand LHS via mul_z_sub_w_coeff2 and IH
    have lhs_eq : coeff2 (mul_z_sub_w_pow
        (GeneralizedFormalDistribution.deriv f 0) (j + 1 + 1)) p q =
      p • coeff2 (mul_z_sub_w_pow f (j + 1)) p q
      - (↑(j + 1 : ℕ) : A) * coeff2 (mul_z_sub_w_pow f j) (p - 1) q
      - ((p + 1 : ℤ) • coeff2 (mul_z_sub_w_pow f (j + 1)) (p + 1) (q - 1)
         - (↑(j + 1 : ℕ) : A) * coeff2 (mul_z_sub_w_pow f j) p (q - 1)) := by
      change coeff2 (mul_z_sub_w (mul_z_sub_w_pow _ (j + 1))) p q = _
      rw [mul_z_sub_w_coeff2, ih (p - 1) q, ih p (q - 1),
          show (p - 1 + 1 : ℤ) = p from by omega]
    rw [lhs_eq]
    -- Factor G terms: G(p-1,q) - G(p,q-1) = F(p,q) via mul_z_sub_w
    have hG : coeff2 (mul_z_sub_w_pow f j) (p - 1) q -
              coeff2 (mul_z_sub_w_pow f j) p (q - 1) =
              coeff2 (mul_z_sub_w_pow f (j + 1)) p q :=
      (mul_z_sub_w_coeff2 _ p q).symm
    -- Expand RHS: coeff2(f^{j+2})(p+1,q) via mul_z_sub_w
    have hF : coeff2 (mul_z_sub_w_pow f (j + 1 + 1)) (p + 1) q =
        coeff2 (mul_z_sub_w_pow f (j + 1)) p q -
        coeff2 (mul_z_sub_w_pow f (j + 1)) (p + 1) (q - 1) := by
      change coeff2 (mul_z_sub_w (mul_z_sub_w_pow f (j + 1))) (p + 1) q = _
      rw [mul_z_sub_w_coeff2, show (p + 1 - 1 : ℤ) = p from by omega]
    rw [hF, show (↑(j + 1 + 1 : ℕ) : A) = (↑(j + 1 : ℕ) : A) + 1 from by push_cast; ring]
    -- Factor c * (G1 - G2) = c * F in the LHS
    have step : (↑(j + 1 : ℕ) : A) * coeff2 (mul_z_sub_w_pow f j) (p - 1) q -
                (↑(j + 1 : ℕ) : A) * coeff2 (mul_z_sub_w_pow f j) p (q - 1) =
                (↑(j + 1 : ℕ) : A) * coeff2 (mul_z_sub_w_pow f (j + 1)) p q := by
      rw [← mul_sub, hG]
    -- Rearrange LHS: a - b - (c - d) = a - c - (b - d), then substitute step
    rw [sub_sub_sub_comm, step, smul_sub, add_mul, one_mul]
    -- LHS: p • F' - (p+1) • S - c * F'
    -- RHS: (p+1) • F' - (p+1) • S - (c * F' + F')
    have hp1 : (p + 1 : ℤ) • coeff2 (mul_z_sub_w_pow f (j + 1)) p q =
        p • coeff2 (mul_z_sub_w_pow f (j + 1)) p q +
        coeff2 (mul_z_sub_w_pow f (j + 1)) p q := by
      rw [add_zsmul, one_zsmul]
    rw [hp1]; abel

/-- **Integration by parts** for formal distributions:
`Res_z (z-w)^{j+1} ∂_z f = -(j+1) · Res_z (z-w)^j f`.

This is the key identity relating the two-variable Fourier transform of `∂_z f`
to that of `f`. -/
theorem integration_by_parts (f : GenFormalDist2 A) (j : ℕ) (q : ℤ) :
    coeff2 (mul_z_sub_w_pow (GeneralizedFormalDistribution.deriv f 0) (j + 1)) (-1) q =
    -(↑(j + 1 : ℕ) : A) * coeff2 (mul_z_sub_w_pow f j) (-1) q := by
  rw [leibniz_deriv_fst_coeff2, show (-1 : ℤ) + 1 = 0 from by omega, zero_smul, zero_sub,
      neg_mul]

/-- If `f` is local of order `N`, then `∂_w f` is local of order `N + 1`.

From `(z-w)^N · f = 0`, we show `(z-w)^{N+1} · ∂_w f = 0`
using the commutation relation between `(z-w)` and `∂_w`. -/
theorem isLocal_deriv_snd (f : GenFormalDist2 A) (N : ℕ) (hf : IsLocalOfOrder f N) :
    IsLocalOfOrder (GeneralizedFormalDistribution.deriv f 1) (N + 1) := by
  induction N generalizing f with
  | zero =>
    -- hf : f = 0
    show mul_z_sub_w (GeneralizedFormalDistribution.deriv f 1) = 0
    rw [show f = 0 from hf, gen_deriv_snd_zero, mul_z_sub_w_zero]
  | succ N ih =>
    -- hf : mul_z_sub_w_pow f (N + 1) = 0
    -- Goal: mul_z_sub_w_pow (deriv f 1) (N + 2) = 0
    -- Definitionally: mul_z_sub_w (mul_z_sub_w_pow (deriv f 1) (N + 1)) = 0
    show mul_z_sub_w (mul_z_sub_w_pow (GeneralizedFormalDistribution.deriv f 1) (N + 1)) = 0
    -- Rewrite inner mul_z_sub_w_pow using pow_succ to expose mul_z_sub_w (deriv f 1)
    rw [mul_z_sub_w_pow_succ, mul_z_sub_w_deriv_snd, mul_z_sub_w_pow_add, mul_z_sub_w_add]
    -- Goal: mul_z_sub_w (mul_z_sub_w_pow (deriv (mul_z_sub_w f) 1) N) +
    --       mul_z_sub_w (mul_z_sub_w_pow f N) = 0
    -- The second term is mul_z_sub_w_pow f (N+1) = 0 by hf
    have h1 : mul_z_sub_w (mul_z_sub_w_pow f N) = 0 := hf
    rw [h1, gen_add_zero]
    -- Goal: mul_z_sub_w (mul_z_sub_w_pow (deriv (mul_z_sub_w f) 1) N) = 0
    -- This is IsLocalOfOrder (deriv (mul_z_sub_w f) 1) (N + 1), apply IH
    exact ih (mul_z_sub_w f) (by show mul_z_sub_w_pow (mul_z_sub_w f) N = 0; rwa [← mul_z_sub_w_pow_succ])

/-- If a 2D generalized distribution is local, then its `w`-derivative is also local. -/
theorem IsLocal.deriv_snd {f : GenFormalDist2 A} (hf : IsLocal f) :
    IsLocal (GeneralizedFormalDistribution.deriv f 1) := by
  obtain ⟨N, hN⟩ := hf
  exact ⟨N + 1, isLocal_deriv_snd f N hN⟩

/-! ## Mutual locality in commutative rings -/

section CommRing
variable {A : Type*} [CommRing A]

/-- Over a commutative ring, the formal commutator is zero since `a·b = b·a`. -/
theorem formalCommutator_eq_zero (a b : FormalDist1 A) :
    formalCommutator a b = 0 := by
  ext idx
  show a.coeff (fun _ => idx 0) * b.coeff (fun _ => idx 1) -
       b.coeff (fun _ => idx 1) * a.coeff (fun _ => idx 0) = 0
  rw [mul_comm (b.coeff _) (a.coeff _), sub_self]

/-- Over a commutative ring, all pairs of distributions are mutually local (with `N = 0`).

This is because `a(z)b(w) = b(w)a(z)` when the coefficient ring is commutative,
so the commutator is zero. -/
theorem commRing_mutuallyLocal (a b : FormalDist1 A) : MutuallyLocal a b := by
  use 0
  show (formalCommutator a b).toGeneralized = 0
  rw [formalCommutator_eq_zero]
  rfl

end CommRing

/-! ## Connection to Theorem 1.4.3 (Decomposition) -/

/-- **Theorem 1.4.3** (Decomposition for local distributions).

Any local 2D distribution can be decomposed using generalized binomial coefficients.
This is a restatement of `decomposition_theorem` from the Decomposition module
using the locality terminology. -/
theorem local_decomposition (f : GenFormalDist2 A) (N : ℕ) (hf : IsLocalOfOrder f N)
    (p q : ℤ) :
    coeff2 f p q = ∑ j ∈ Finset.range N,
      (↑(intBinomial (-p - 1) j) : A) *
        coeff2 (mul_z_sub_w_pow f j) (-1) (p + q + ↑j + 1) :=
  decomposition_theorem f N hf p q

/-! ## Monotonicity of locality order -/

/-- If `(z-w)^N · f = 0` and `j ≥ N`, then `(z-w)^j · f = 0`. -/
theorem mul_z_sub_w_pow_zero_of_ge (f : GenFormalDist2 A) (N j : ℕ)
    (hf : mul_z_sub_w_pow f N = 0) (hj : j ≥ N) :
    mul_z_sub_w_pow f j = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    show mul_z_sub_w (mul_z_sub_w_pow f (N + k)) = 0
    rw [ih (Nat.le_add_right N k)]
    exact mul_z_sub_w_zero

/-! ## j-th product (Remark 1.4.4) -/

/-- The j-th product of two formal distributions:
`a_{(j)} b(w) = Res_z (z-w)^j [a(z), b(w)]`.

This is the fundamental algebraic operation in vertex algebra theory.
When `a` and `b` are mutually local of order `N`, the j-th product vanishes for `j ≥ N`.

## References
* [Nozaradan, *Introduction to Vertex Algebras*], Remark 1.4.4
-/
noncomputable def nthProduct (a b : FormalDist1 A) (j : ℕ) : GenFormalDist1 A :=
  GeneralizedFormalDistribution.residueAt 0
    (mul_z_sub_w_pow (formalCommutator a b).toGeneralized j)

/-- If `a` and `b` are mutually local of order `N`, then the j-th product
vanishes for all `j ≥ N`. -/
theorem nthProduct_eq_zero_of_local (a b : FormalDist1 A) (N j : ℕ)
    (hlocal : IsLocalOfOrder (formalCommutator a b).toGeneralized N) (hj : j ≥ N) :
    nthProduct a b j = 0 := by
  unfold nthProduct
  rw [mul_z_sub_w_pow_zero_of_ge _ N j hlocal hj]
  ext idx; rfl

end FormalDelta
