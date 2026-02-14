# FormalDistribution -- Lean 4 Formalization of Formal Calculus

An axiom-free Lean 4 formalization of **Chapter 1: Formal Calculus** from
Nozaradan's *Introduction to Vertex Algebras*, structured as a mathlib-compatible library
with a bridge to `Mathlib.RingTheory.HahnSeries`.

Propositions 1.2.3 and 1.2.5 are omitted (they require topological machinery
beyond the algebraic scope). Definition 1.3.3 is also omitted as Proposition 1.3.4
is proved directly without it.

## Build

Requires Lean 4 (v4.28.0-rc1) with Mathlib.

```bash
lake exe cache get   # fetch Mathlib oleans
lake build           # 1398 jobs, 0 errors
```

## File Structure

```
FormalDistribution.lean                 -- root re-export
FormalDistribution/
  Basic.lean            (462 lines)     -- core types, Zero/Add/Neg/Sub/SMul instances
  Deriv.lean            (181 lines)     -- formal derivatives
  Mul.lean              (955 lines)     -- 1D/2D multiplication, ring axioms
  Fourier.lean          (231 lines)     -- Fourier expansion, modes, residue
  Binomial.lean         (195 lines)     -- extended/generalized binomial coefficients
  Expansion.lean        (298 lines)     -- expansion operators i_{z,w}, i_{w,z}, Remark 1.2.4
  Delta.lean            (559 lines)     -- formal delta, all 7 properties, swap symmetry
  HahnSeries.lean       (271 lines)    -- bridge to Mathlib HahnSeries, CommRing instance
  Decomposition.lean    (231 lines)    -- Proposition 1.3.6: decomposition theorem
  Locality.lean         (440 lines)    -- Section 1.4: locality, commutator, j-th product
  FourierTransform.lean (224 lines)    -- Section 1.5: Fourier transform, lambda-bracket
```

**4088 lines total. 0 axioms. 0 sorry. 0 admits.**

## Mathematical Content

### Section 1.1 -- Formal Distributions

- `FormalDistribution A n` -- distributions with finite support
- `GeneralizedFormalDistribution A n` -- bounded-finite support (for delta)
- Type aliases: `FormalDist1`, `FormalDist2`, `GenFormalDist2`
- Arithmetic: addition, negation, subtraction, scalar multiplication, formal derivatives
- 1D and 2D Cauchy product multiplication with full ring axioms
- `CommRing (FormalDist1 R)` via HahnSeries bridge

### Section 1.2 -- Expansion Operators

- `fourierExpansion`, `fourierMode`, `residue`
- `Int.extChoose` -- extended binomial coefficient for integers
- `intBinomial` -- integer-valued generalized binomial with Pascal's rule
- `expansion_izw`, `expansion_iwz` -- expansion operators
- Remark 1.2.4: `expansion_izw_eq_iwz_of_nonneg` -- both operators agree for non-negative exponents

### Section 1.3 -- Formal Delta

- `formalDelta : GenFormalDist2 A`
- Proposition 1.3.4: `formalDelta_eq_expansion_izw_sub_iwz`
- All 7 properties from Proposition 1.3.5:
  1. `mul_z_sub_w_pow_succ_iteratedDeriv_formalDelta_eq_zero` -- (z-w)^{n+1} d^n delta = 0
  2. `mul_z_sub_w_iteratedDeriv_formalDelta` -- (z-w) d^n delta = n d^{n-1} delta
  3. `formalDelta_swap` -- variable-swap symmetry
  4. `deriv_fst_formalDelta_add_deriv_snd_formalDelta` -- d_z delta + d_w delta = 0
  5. `embedFst_mulGen_formalDelta_eq_embedSnd` -- a(z) delta = a(w) delta
  6. `residueAt_embedFst_mulGen_formalDelta` -- Res_z a(z) delta = a(w)
  7. `mul_z_sub_w_pow_iteratedDeriv_formalDelta` -- falling factorial identity
- Proposition 1.3.6: `decomposition_theorem` -- if (z-w)^N f = 0 then f decomposes as
  a finite sum involving generalized binomial coefficients (no `[Algebra ℚ A]` needed)

### Section 1.4 -- Locality

- `externalProduct` -- tensor product a(z)b(w) of two 1D distributions
- `formalCommutator` -- commutator [a(z), b(w)] = a(z)b(w) - b(w)a(z)
- `IsLocal`, `IsLocalOfOrder`, `MutuallyLocal` -- locality definitions (Definition 1.4.1)
- `formalDelta_isLocal` -- delta is local with N = 1 (Example 1.4.2)
- `iteratedDeriv_formalDelta_isLocal` -- d^n delta is local with N = n + 1 (Example 1.4.2)
- `isLocal_deriv_snd` -- derivatives of local distributions are local
- `commRing_mutuallyLocal` -- all pairs are mutually local over CommRing
- `nthProduct` -- j-th product a_{(j)} b (Remark 1.4.4)
- `local_decomposition` -- decomposition for local distributions (Theorem 1.4.3)
- `leibniz_deriv_fst_coeff2` -- Leibniz rule for z-derivative and (z-w)^j
- `integration_by_parts` -- Res_z (z-w)^{j+1} d_z f = -(j+1) Res_z (z-w)^j f

### Section 1.5 -- Fourier Transform

- `fourierTransformCoeff` -- n-th coefficient (1/n!)·a_n of F_z^λ(a) (Definition 1.5.1)
- `fourierTransformCoeff_deriv` -- F(∂a)_n = -F(a)_{n-1} (Proposition 1.5.2)
- `reflect`, `fourierTransformCoeff_reflect` -- F(a(-z)) = -F(-λ,a) (Proposition 1.5.2(3))
- `twoVarFourierCoeff` -- j-th coefficient of two-variable FT (Definition 1.5.3)
- `twoVarFourierCoeff_commutator_eq` -- lambda-bracket = (1/j!)·a_{(j)}b (Proposition 1.5.4)
- `twoVarFourierCoeff_deriv_fst` -- F(∂_z f)_{j+1} = -F(f)_j (Proposition 1.5.4(2))
- `twoVarFourierCoeff_eq_zero_of_local` -- lambda-bracket is polynomial for local distributions

### Hahn Series Bridge

- `toHahnSeries : FormalDist1 R -> HahnSeries Z R`
- `ofHahnSeries` (inverse for finite-support series)
- Preserves zero, one, addition, multiplication, negation, powers, casts
- `CommRing (FormalDist1 R)` transferred via `Function.Injective.commRing`
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
