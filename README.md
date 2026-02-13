# FormalDistribution -- Lean 4 Formalization of Formal Calculus

An axiom-free Lean 4 formalization covering most of **Section 1: Formal Calculus** from
Nozaradan's *Introduction to Vertex Algebras*, structured as a mathlib-compatible library
with a bridge to `Mathlib.RingTheory.HahnSeries`.

Propositions 1.2.3, 1.2.5, and 1.3.6 are omitted (they require topological or Laurent
series machinery beyond the algebraic scope). Definition 1.3.3 is also omitted as
Proposition 1.3.4 is proved directly without it.

## Build

Requires Lean 4 (v4.28.0-rc1) with Mathlib.

```bash
lake exe cache get   # fetch Mathlib oleans
lake build           # 1395 jobs, 0 errors
```

## File Structure

```
FormalDistribution.lean              -- root re-export
FormalDistribution/
  Basic.lean          (431 lines)    -- core types, Zero/Add/SMul instances
  Deriv.lean          (181 lines)    -- formal derivatives
  Mul.lean            (955 lines)    -- 1D/2D multiplication, ring axioms
  Fourier.lean        (231 lines)    -- Fourier expansion, modes, residue
  Binomial.lean       (177 lines)    -- extended binomial Int.extChoose
  Expansion.lean      (251 lines)    -- expansion operators i_{z,w}, i_{w,z}
  Delta.lean          (540 lines)    -- formal delta, all 7 properties
  HahnSeries.lean     (149 lines)   -- bridge to Mathlib HahnSeries
```

**2950 lines total. 0 axioms. 0 sorry. 0 admits.**

## Mathematical Content

### Section 1.1 -- Formal Distributions

- `FormalDistribution A n` -- distributions with finite support
- `GeneralizedFormalDistribution A n` -- bounded-finite support (for delta)
- Type aliases: `FormalDist1`, `FormalDist2`, `GenFormalDist2`
- Arithmetic: addition, scalar multiplication, formal derivatives
- 1D and 2D Cauchy product multiplication with full ring axioms

### Section 1.2 -- Expansion Operators

- `fourierExpansion`, `fourierMode`, `residue`
- `Int.extChoose` -- extended binomial coefficient for integers
- `expansion_izw`, `expansion_iwz` -- expansion operators

### Section 1.3 -- Formal Delta

- `formalDelta : GenFormalDist2 A`
- Proposition 1.3.4: `formalDelta_eq_expansion_izw_sub_iwz`
- All 7 properties from Proposition 1.3.5:
  1. `mul_z_sub_w_pow_succ_iteratedDeriv_formalDelta_eq_zero` -- (z-w)^{n+1} d^n delta = 0
  2. `mul_z_sub_w_iteratedDeriv_formalDelta` -- (z-w) d^n delta = n d^{n-1} delta
  3. `formalDelta_symm` -- symmetry (definitional, by `rfl`)
  4. `deriv_fst_formalDelta_add_deriv_snd_formalDelta` -- d_z delta + d_w delta = 0
  5. `embedFst_mulGen_formalDelta_eq_embedSnd` -- a(z) delta = a(w) delta
  6. `residueAt_embedFst_mulGen_formalDelta` -- Res_z a(z) delta = a(w)
  7. `mul_z_sub_w_pow_iteratedDeriv_formalDelta` -- falling factorial identity

### Hahn Series Bridge

- `toHahnSeries : FormalDist1 R -> HahnSeries Z R`
- `ofHahnSeries` (inverse for finite-support series)
- Preserves zero, one, addition, and multiplication
- Round-trip identities in both directions

## Usage

```lean
import FormalDistribution

-- One-variable formal distribution
example : Type _ := FormalDist1 C

-- Fourier expansion extracts coefficients
example : FormalDist1 C -> (Z -> C) := fourierExpansion

-- Extended binomial coefficient
example : Z -> N -> Q := Int.extChoose

-- Formal delta distribution
noncomputable example : GenFormalDist2 C := formalDelta

-- Convert to Mathlib's HahnSeries
noncomputable example (a : FormalDist1 C) : HahnSeries Z C :=
  FormalDistribution.toHahnSeries a
```

## Design

Two structure types handle the finite-vs-infinite support tension:

- **`FormalDistribution`** requires globally finite support, enabling axiom-free
  multiplication proofs via `Set.Finite.biUnion`.
- **`GeneralizedFormalDistribution`** requires bounded-finite support (finite above
  any bound), accommodating `formalDelta` whose support is the infinite line
  `{(k, -k-1) | k in Z}`.

All multiplication and ring axiom proofs are completely axiom-free.

## Mathlib Compatibility

The library follows mathlib conventions: snake_case naming, `@[ext]`/`@[simp]`
attributes, docstrings on all public declarations, `open scoped BigOperators`,
minimal imports per file. The Hahn Series bridge enables interoperability with
`Mathlib.Algebra.Vertex.VertexOperator`.

## References

- Nozaradan, C. *Introduction to Vertex Algebras*. Section 1: Formal Calculus.
- Carnahan, S. `Mathlib.Algebra.Vertex.VertexOperator`.

## License

Released under Apache 2.0 license.
