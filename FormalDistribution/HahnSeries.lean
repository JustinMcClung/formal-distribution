/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FormalDistribution.Mul
import Mathlib.RingTheory.HahnSeries.Addition
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Algebra.Ring.InjSurj

/-!
# Compatibility with Hahn Series

This file provides conversions between the `FormalDistribution` types defined in this library
and Mathlib's `HahnSeries`, enabling interoperability with vertex operator definitions
in `Mathlib.Algebra.Vertex.VertexOperator`.

## Main definitions

* `FormalDistribution.toHahnSeries` - convert a 1D formal distribution to a Hahn series
* `FormalDistribution.ofHahnSeries` - convert a finitely-supported Hahn series back

## Main results

* `toHahnSeries_add` - preserves addition
* `toHahnSeries_mul` - preserves the Cauchy product
* `CommRing (FormalDist1 R)` - full commutative ring structure via `Function.Injective.commRing`
* `toHahnSeries_ofHahnSeries` - round-trip identity (Hahn → Dist → Hahn)
* `ofHahnSeries_toHahnSeries` - round-trip identity (Dist → Hahn → Dist)

## References

* [Carnahan, *Mathlib.Algebra.Vertex.VertexOperator*]
-/

namespace FormalDistribution

variable {R : Type*} [CommRing R]

/-! ### Conversions -/

/-- Convert a one-dimensional formal distribution to a Hahn series.

Finite support implies partial well-ordering via `Set.Finite.isPWO`. -/
noncomputable def toHahnSeries (a : FormalDist1 R) : HahnSeries ℤ R where
  coeff := fun n => a.coeff (fun _ => n)
  isPWO_support' := by
    apply Set.Finite.isPWO
    exact (a.support_finite.image (· 0)).subset fun n hn => ⟨fun _ => n, hn, rfl⟩

/-- Coefficient extraction for `toHahnSeries`. -/
@[simp]
theorem toHahnSeries_coeff (a : FormalDist1 R) (n : ℤ) :
    (toHahnSeries a).coeff n = a.coeff (fun _ => n) := rfl

/-- Convert a Hahn series with finite support to a formal distribution. -/
noncomputable def ofHahnSeries (f : HahnSeries ℤ R) (hf : f.support.Finite) : FormalDist1 R where
  coeff := fun idx => f.coeff (idx 0)
  support_finite := by
    exact (hf.image (fun n => (fun _ : Fin 1 => n))).subset fun idx hidx =>
      ⟨idx 0, hidx, funext fun i => by fin_cases i; rfl⟩

/-! ### Multiplicative identity -/

/-- The multiplicative identity for 1D formal distributions: coefficient `1` at index `0`. -/
noncomputable instance : One (FormalDist1 R) where
  one := ⟨fun idx => if idx 0 = 0 then 1 else 0, by
    apply (Set.finite_singleton (fun _ : Fin 1 => (0 : ℤ))).subset
    intro idx hidx
    simp only [Set.mem_setOf_eq] at hidx
    simp only [Set.mem_singleton_iff]
    split_ifs at hidx with h
    · funext i; fin_cases i; exact h
    · exact absurd rfl hidx⟩

/-! ### Preservation of algebraic structure -/

/-- `toHahnSeries` sends the zero distribution to the zero Hahn series. -/
theorem toHahnSeries_zero : (0 : FormalDist1 R).toHahnSeries = 0 := by
  ext n; rfl

/-- `toHahnSeries` preserves addition. -/
theorem toHahnSeries_add (a b : FormalDist1 R) :
    (a + b).toHahnSeries = a.toHahnSeries + b.toHahnSeries := by
  ext n; rfl

/-- `toHahnSeries` sends the multiplicative identity to `1 : HahnSeries ℤ R`. -/
theorem toHahnSeries_one : (1 : FormalDist1 R).toHahnSeries = 1 := by
  ext n
  simp only [toHahnSeries_coeff, HahnSeries.coeff_one]
  show (if n = (0 : ℤ) then (1 : R) else 0) = _
  by_cases h : n = 0 <;> simp [h]

/-- `toHahnSeries` preserves the Cauchy product multiplication.

The proof establishes a bijection between the convolution support
`{k | a_k ≠ 0 ∧ b_{n-k} ≠ 0}` and the Hahn series antidiagonal
`{(i,j) | i + j = n ∧ a_i ≠ 0 ∧ b_j ≠ 0}` via `k ↦ (k, n-k)`. -/
theorem toHahnSeries_mul (a b : FormalDist1 R) :
    (a * b).toHahnSeries = a.toHahnSeries * b.toHahnSeries := by
  ext n
  -- LHS is definitionally mulCoeff1d a b n
  change mulCoeff1d a b n = _
  rw [show (a.toHahnSeries * b.toHahnSeries).coeff n =
    ∑ ij ∈ Finset.addAntidiagonal a.toHahnSeries.isPWO_support b.toHahnSeries.isPWO_support n,
      a.toHahnSeries.coeff ij.fst * b.toHahnSeries.coeff ij.snd from HahnSeries.coeff_mul]
  unfold mulCoeff1d
  apply Finset.sum_nbij' (fun k => (k, n - k)) Prod.fst
  · -- Forward: convolution support → antidiagonal
    intro k hk
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hk
    rw [Finset.mem_addAntidiagonal]
    exact ⟨(HahnSeries.mem_support _ _).mpr hk.1, (HahnSeries.mem_support _ _).mpr hk.2, by omega⟩
  · -- Backward: antidiagonal → convolution support
    intro ij hij
    rw [Finset.mem_addAntidiagonal] at hij
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    refine ⟨(HahnSeries.mem_support _ _).mp hij.1, ?_⟩
    have h_eq : n - ij.fst = ij.snd := by omega
    rw [h_eq]
    exact (HahnSeries.mem_support _ _).mp hij.2.1
  · -- Left inverse
    intro k _; rfl
  · -- Right inverse
    intro ij hij
    rw [Finset.mem_addAntidiagonal] at hij
    exact Prod.ext rfl (show n - ij.fst = ij.snd by omega)
  · -- Summands agree
    intro k _; rfl

/-- `toHahnSeries` preserves negation. -/
theorem toHahnSeries_neg (a : FormalDist1 R) :
    (-a).toHahnSeries = -a.toHahnSeries := by
  ext n; rfl

/-- `toHahnSeries` preserves subtraction. -/
theorem toHahnSeries_sub (a b : FormalDist1 R) :
    (a - b).toHahnSeries = a.toHahnSeries - b.toHahnSeries := by
  ext n; rfl

/-- `toHahnSeries` preserves natural number scalar multiplication. -/
theorem toHahnSeries_nsmul (k : ℕ) (a : FormalDist1 R) :
    (k • a).toHahnSeries = k • a.toHahnSeries := by
  ext n; rfl

/-- `toHahnSeries` preserves integer scalar multiplication. -/
theorem toHahnSeries_zsmul (k : ℤ) (a : FormalDist1 R) :
    (k • a).toHahnSeries = k • a.toHahnSeries := by
  ext n; rfl

/-- `toHahnSeries` is injective. -/
theorem toHahnSeries_injective : Function.Injective (toHahnSeries : FormalDist1 R → HahnSeries ℤ R) := by
  intro a b hab
  ext idx
  have h : (toHahnSeries a).coeff (idx 0) = (toHahnSeries b).coeff (idx 0) := by rw [hab]
  simp only [toHahnSeries_coeff] at h
  convert h using 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl

/-! ### Additional instances for CommRing transfer -/

/-- Auxiliary recursive definition for natural number power. -/
private noncomputable def npow (a : FormalDist1 R) : ℕ → FormalDist1 R
  | 0 => 1
  | n + 1 => a * npow a n

/-- Natural number power via iterated multiplication. -/
noncomputable instance : Pow (FormalDist1 R) ℕ where
  pow := npow

/-- `toHahnSeries` preserves natural number powers. -/
theorem toHahnSeries_pow (a : FormalDist1 R) (n : ℕ) :
    (a ^ n).toHahnSeries = a.toHahnSeries ^ n := by
  induction n with
  | zero => exact toHahnSeries_one
  | succ n ih =>
    show (a * a ^ n).toHahnSeries = a.toHahnSeries ^ (n + 1)
    rw [toHahnSeries_mul, ih, pow_succ, mul_comm]

/-- Natural number cast into 1D formal distributions. -/
noncomputable instance : NatCast (FormalDist1 R) where
  natCast n := ⟨fun idx => if idx 0 = 0 then (n : R) else 0, by
    apply (Set.finite_singleton (fun _ : Fin 1 => (0 : ℤ))).subset
    intro idx hidx
    simp only [Set.mem_setOf_eq] at hidx
    simp only [Set.mem_singleton_iff]
    split_ifs at hidx with h
    · funext i; fin_cases i; exact h
    · exact absurd rfl hidx⟩

/-- Integer cast into 1D formal distributions. -/
noncomputable instance : IntCast (FormalDist1 R) where
  intCast n := ⟨fun idx => if idx 0 = 0 then (n : R) else 0, by
    apply (Set.finite_singleton (fun _ : Fin 1 => (0 : ℤ))).subset
    intro idx hidx
    simp only [Set.mem_setOf_eq] at hidx
    simp only [Set.mem_singleton_iff]
    split_ifs at hidx with h
    · funext i; fin_cases i; exact h
    · exact absurd rfl hidx⟩

/-- Coefficient formula for natural number casts in `HahnSeries ℤ R`. -/
private lemma hahnSeries_natCast_coeff (n : ℕ) (k : ℤ) :
    ((n : HahnSeries ℤ R)).coeff k = if k = 0 then (n : R) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, HahnSeries.coeff_add, ih, HahnSeries.coeff_one]
    by_cases h : k = 0
    · simp [h, Nat.cast_succ]
    · simp [h]

/-- `toHahnSeries` preserves natural number casts. -/
theorem toHahnSeries_natCast (n : ℕ) :
    toHahnSeries (n : FormalDist1 R) = (n : HahnSeries ℤ R) := by
  ext k
  simp only [toHahnSeries_coeff]
  change (if k = 0 then (n : R) else 0) = _
  rw [hahnSeries_natCast_coeff]

/-- `toHahnSeries` preserves integer casts. -/
theorem toHahnSeries_intCast (n : ℤ) :
    toHahnSeries (n : FormalDist1 R) = (n : HahnSeries ℤ R) := by
  ext k
  simp only [toHahnSeries_coeff]
  change (if k = 0 then (n : R) else 0) = _
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    rw [hahnSeries_natCast_coeff]
  | negSucc m =>
    simp only [Int.cast_negSucc]
    rw [show (-((↑(m + 1) : ℕ) : HahnSeries ℤ R)).coeff k =
            -((↑(m + 1) : ℕ) : HahnSeries ℤ R).coeff k from rfl,
        hahnSeries_natCast_coeff]
    by_cases h : k = 0 <;> simp [h]

/-! ### CommRing instance -/

/-- `FormalDist1 R` forms a commutative ring, transferred from `HahnSeries ℤ R`
via the injective map `toHahnSeries`.

This gives `FormalDist1 R` the full `CommRing` structure including associativity
and commutativity of multiplication, which would be difficult to prove directly
from the Cauchy product definition. -/
noncomputable instance : CommRing (FormalDist1 R) :=
  toHahnSeries_injective.commRing toHahnSeries
    toHahnSeries_zero toHahnSeries_one toHahnSeries_add toHahnSeries_mul
    toHahnSeries_neg toHahnSeries_sub toHahnSeries_nsmul toHahnSeries_zsmul
    toHahnSeries_pow toHahnSeries_natCast toHahnSeries_intCast

/-! ### Support and round-trip lemmas -/

/-- The support of `toHahnSeries a` is finite. -/
theorem toHahnSeries_support_finite (a : FormalDist1 R) :
    (toHahnSeries a).support.Finite :=
  (a.support_finite.image (· 0)).subset fun n hn =>
    ⟨fun _ => n, (HahnSeries.mem_support _ _).mp hn, rfl⟩

/-- Converting a Hahn series to a distribution and back yields the original series. -/
theorem toHahnSeries_ofHahnSeries (f : HahnSeries ℤ R) (hf : f.support.Finite) :
    (ofHahnSeries f hf).toHahnSeries = f := by
  ext n; rfl

/-- Converting a distribution to a Hahn series and back yields the original distribution. -/
theorem ofHahnSeries_toHahnSeries (a : FormalDist1 R) :
    ofHahnSeries a.toHahnSeries (toHahnSeries_support_finite a) = a := by
  ext idx
  show a.coeff (fun _ => idx 0) = a.coeff idx
  congr 1
  funext i; fin_cases i; rfl

end FormalDistribution
