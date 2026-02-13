# Final Status: Mathlib-Compatible Formal Distribution Library

## Build Status

- **`lake build`**: SUCCESS (1395 jobs, 0 errors)
- **Axioms**: 0
- **Sorries**: 0
- **Date**: 2026-02-13

## Project Overview

A Lean 4 formalization of formal distributions from Nozaradan's *Introduction to Vertex Algebras* (Section 1), refactored from a monolithic 2737-line file into 8 mathlib-compatible submodules with a Hahn Series interoperability bridge.

## File Structure

| File | Lines | Description |
|------|------:|-------------|
| `FormalDistribution.lean` | 35 | Root re-export of all submodules |
| `FormalDistribution/Basic.lean` | 431 | Core types, type aliases, `Zero`/`Add`/`SMul` instances |
| `FormalDistribution/Deriv.lean` | 181 | Formal derivatives (`deriv`, `iteratedDeriv`) |
| `FormalDistribution/Mul.lean` | 955 | 1D/2D multiplication, ring axioms, embeddings, residues |
| `FormalDistribution/Fourier.lean` | 231 | Fourier expansion, Fourier modes, residue extraction |
| `FormalDistribution/Binomial.lean` | 177 | Extended binomial coefficient `Int.extChoose` |
| `FormalDistribution/Expansion.lean` | 251 | `expansion_izw`, `expansion_iwz` operators |
| `FormalDistribution/Delta.lean` | 540 | `formalDelta`, all 7 properties of Section 1.3 |
| `FormalDistribution/HahnSeries.lean` | 149 | Bridge to `Mathlib.RingTheory.HahnSeries` |
| **Total** | **2950** | |

## Key Types

```lean
-- Finite-support formal distributions (enables axiom-free multiplication)
@[ext]
structure FormalDistribution (A : Type*) [Ring A] (nvars : ℕ) where
  coeff : (Fin nvars → ℤ) → A
  support_finite : {idx : Fin nvars → ℤ | coeff idx ≠ 0}.Finite

-- Bounded-finite support (accommodates formalDelta's infinite support)
@[ext]
structure GeneralizedFormalDistribution (A : Type*) [Ring A] (nvars : ℕ) where
  coeff : (Fin nvars → ℤ) → A
  support_finite : ∀ (bound : Fin nvars → ℤ),
    {idx : Fin nvars → ℤ | (∀ i, idx i ≥ bound i) ∧ coeff idx ≠ 0}.Finite
```

## Mathematical Content

### Definitions (Section 1.1-1.2)
- `FormalDistribution`, `GeneralizedFormalDistribution`, `FormalDist1`, `GenFormalDist2`
- `fourierExpansion`, `fourierMode`, `residue`
- `Int.extChoose` (extended binomial coefficient)
- `expansion_izw`, `expansion_iwz`

### Multiplication (Section 1.1)
- 1D Cauchy product (`mulCoeff1d`, `Mul (FormalDist1 A)`)
- 2D multiplication (`mulCoeff2d`, generalized `mulGen`)
- Ring axioms: `add_mul`, `mul_add`, `smul_mul`, `mul_smul` (1D and 2D)
- All proofs axiom-free via finite support

### Formal Delta (Section 1.3)
- `formalDelta : GenFormalDist2 A` (defined as `GeneralizedFormalDistribution`, no axiom needed)
- `formalDelta_coeff` proved by `rfl`
- All 7 properties from Nozaradan Section 1.3 proved:
  1. `formalDelta_eq_expansion_izw_sub_iwz`
  2. `mul_z_sub_w_formalDelta` ($(z-w)\delta = 0$)
  3. `formalDelta_symm`
  4. `deriv_fst_formalDelta_add_deriv_snd_formalDelta` ($\partial_z\delta + \partial_w\delta = 0$)
  5. `embedFst_mulGen_formalDelta_eq_embedSnd` ($a(z)\delta = a(w)\delta$)
  6. `residueAt_embedFst_mulGen_formalDelta` ($\text{Res}_z\, a(z)\delta = a(w)$)
  7. `mul_z_sub_w_pow_iteratedDeriv_formalDelta` ($(z-w)^j \partial_w^n\delta$ formula)

### Hahn Series Bridge
- `toHahnSeries : FormalDist1 R -> HahnSeries Z R`
- `ofHahnSeries : HahnSeries Z R -> FormalDist1 R` (finite support)
- Preserves: zero, one, addition, multiplication (Cauchy product)
- Round-trip identities in both directions
- Enables interop with `Mathlib.Algebra.Vertex.VertexOperator`

## Mathlib Conventions

- **Naming**: snake_case throughout; `Int.extChoose`, `formalDelta`, `embedFst`/`embedSnd`, `residueAt`
- **Attributes**: `@[ext]` on structures, `@[simp]` on canonical reduction lemmas
- **Documentation**: `/-- ... -/` docstrings on all public declarations, `/-! ... -/` module docs on all files
- **Style**: `variable` at section level, `open scoped BigOperators`, no `private`, no `open Complex`
- **Imports**: minimal per-file; root file re-exports all submodules
- **No axioms, no sorry, no admits**

## Verification

```bash
lake build
# Build completed successfully (1395 jobs).

grep -rn "sorry\|axiom\|admit" FormalDistribution/
# (No output)
```

### Compilation examples (Delta.lean)
```lean
example : Type _ := FormalDistribution C 1
example : Type _ := GeneralizedFormalDistribution C 2
example : FormalDist1 C -> (Z -> C) := fourierExpansion
example : Z -> N -> Q := Int.extChoose
noncomputable example : GenFormalDist2 C := formalDelta
```

## References

- Nozaradan, *Introduction to Vertex Algebras*, Section 1
- Carnahan, `Mathlib.Algebra.Vertex.VertexOperator`
