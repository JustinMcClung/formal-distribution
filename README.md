# FormalDistribution -- Lean 4 Formalization of Formal Calculus

An axiom-free Lean 4 formalization of **Chapter 1: Formal Calculus** from
Nozaradan's *Introduction to Vertex Algebras*, structured as a mathlib-compatible library
with a bridge to `Mathlib.RingTheory.HahnSeries`.

Three items are intentionally omitted:

- **Proposition 1.2.3** is analytic motivation showing that formal expansion
  operators recover classical Laurent expansions in `|z| > |w|`. Formalizing it
  would require `Complex`, `HasSum`, and geometric series convergence -- a
  substantial analysis detour with no payoff for the algebraic theory. All
  downstream consequences (Remark 1.2.4, Propositions 1.2.6, 1.3.4) are
  already formalized.
- **Remark 1.2.5** is a notational convention about how other references write
  expansion operators. It has no mathematical content.
- **Definition 1.3.3** (delta via limits) is bypassed; Proposition 1.3.4 is
  proved directly from the coefficient-level definition.

## Build

Requires Lean 4 (v4.28.0) with Mathlib.

```bash
lake exe cache get   # fetch Mathlib oleans
lake build           # 1498 jobs, 0 errors
```

## File Structure

```
FormalDistribution.lean                  -- root re-export
FormalDistribution/
  Basic.lean             (456 lines)    -- core types, embeddings, Zero/Add/Neg/Sub/SMul
  Deriv.lean             (181 lines)    -- formal derivatives
  Mul.lean               (718 lines)    -- 1D/2D multiplication, ring axioms
  Fourier.lean           (231 lines)    -- Fourier expansion, modes, residue
  Binomial.lean           (80 lines)    -- generalized binomial via Mathlib Ring.choose
  Expansion.lean         (285 lines)    -- expansion operators i_{z,w}, i_{w,z}, Remark 1.2.4
  Delta.lean             (540 lines)    -- formal delta, all 7 properties, swap symmetry
  HahnSeries.lean        (271 lines)    -- bridge to Mathlib HahnSeries, CommRing instance
  Decomposition.lean     (357 lines)    -- Proposition 1.3.6: decomposition theorem
  Locality.lean          (479 lines)    -- Section 1.4: locality, commutator, j-th product
  FourierTransform.lean  (255 lines)    -- Section 1.5: Fourier transform, lambda-bracket
```

**3853 lines total. 0 axioms. 0 sorry. 0 admits.**

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
- `intBinomial` -- integer-valued generalized binomial via Mathlib's `Ring.choose`
- `expansion_izw`, `expansion_iwz` -- expansion operators
- Remark 1.2.4: `expansion_izw_eq_iwz_of_nonneg` -- both operators agree for non-negative exponents

### Section 1.3 -- Formal Delta

- `formalDeltaPair {n} (i j : Fin n) (hij)` -- n-variable formal delta for any pair
- `formalDelta : GenFormalDist2 A` -- 2-variable alias
- Proposition 1.3.4: `formalDelta_eq_expansion_izw_sub_iwz`
- All 7 properties from Proposition 1.3.5:
  1. `mul_z_sub_w_pow_succ_iteratedDeriv_formalDelta_eq_zero` -- (z-w)^{n+1} d^n delta = 0
  2. `mul_z_sub_w_iteratedDeriv_formalDelta` -- (z-w) d^n delta = n d^{n-1} delta
  3. `formalDelta_swap` -- variable-swap symmetry
  4. `deriv_fst_formalDelta_add_deriv_snd_formalDelta` -- d_z delta + d_w delta = 0
  5. `embedFst_mulGen_formalDelta_eq_embedSnd` -- a(z) delta = a(w) delta
  6. `residueAt_embedFst_mulGen_formalDelta` -- Res_z a(z) delta = a(w)
  7. `mul_z_sub_w_pow_iteratedDeriv_formalDelta` -- falling factorial identity
- `decomposition_theorem_pair` -- n-variable decomposition: if (x_i - x_j)^N f = 0
  then f decomposes as a finite sum involving generalized binomial coefficients
- `decomposition_theorem` -- 2-variable alias (no `[Algebra ℚ A]` needed)

### Section 1.4 -- Locality

- `IsLocalForPairOfOrder`, `IsLocalForPair` -- n-variable locality for any pair (i, j)
- `IsLocal`, `IsLocalOfOrder`, `MutuallyLocal` -- 2-variable aliases (Definition 1.4.1)
- `externalProduct` -- tensor product a(z)b(w) of two 1D distributions
- `formalCommutator` -- commutator [a(z), b(w)] = a(z)b(w) - b(w)a(z)
- `formalDelta_isLocal` -- delta is local with N = 1 (Example 1.4.2)
- `iteratedDeriv_formalDelta_isLocal` -- d^n delta is local with N = n + 1 (Example 1.4.2)
- `isLocal_deriv_snd` -- derivatives of local distributions are local
- `commRing_mutuallyLocal` -- all pairs are mutually local over CommRing
- `nthProductAt` -- n-variable j-th product; `nthProduct` is the 2-variable alias
- `local_decomposition` -- decomposition for local distributions (Theorem 1.4.3)
- `leibniz_deriv_fst_coeff2` -- Leibniz rule for z-derivative and (z-w)^j
- `integration_by_parts` -- Res_z (z-w)^{j+1} d_z f = -(j+1) Res_z (z-w)^j f

### Section 1.5 -- Fourier Transform

- `fourierTransformCoeff` -- n-th coefficient (1/n!)·a_n of F_z^λ(a) (Definition 1.5.1)
- `fourierTransformCoeff_deriv` -- F(∂a)_n = -F(a)_{n-1} (Proposition 1.5.2)
- `reflect`, `fourierTransformCoeff_reflect` -- F(a(-z)) = -F(-λ,a) (Proposition 1.5.2(3))
- `twoVarFourierCoeffAt` -- n-variable FT coefficient for any pair (i, j)
- `twoVarFourierCoeff` -- 2-variable alias (Definition 1.5.3)
- `twoVarFourierCoeff_commutator_eq` -- lambda-bracket = (1/j!)·a_{(j)}b (Proposition 1.5.4)
- `twoVarFourierCoeff_deriv_fst` -- F(∂_z f)_{j+1} = -F(f)_j (Proposition 1.5.4(2))
- `twoVarFourierCoeffAt_eq_zero_of_local` -- lambda-bracket is polynomial for local distributions

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

-- Formal delta distribution
noncomputable example : GenFormalDist2 C := formalDelta

-- N-variable locality: delta in variables (i, j) of an n-variable expression
noncomputable example {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    GeneralizedFormalDistribution C n := formalDeltaPair i j hij

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

Locality, delta, decomposition, j-th products, and Fourier coefficients are defined
for an arbitrary pair of variables `(i, j)` in an `n`-variable distribution. The
classic 2-variable API (`formalDelta`, `IsLocal`, `nthProduct`, etc.) is recovered
via `abbrev` aliases at `n = 2, i = 0, j = 1`, so all existing code continues to work.

## Mathlib Compatibility

The library follows mathlib conventions: snake_case naming, `@[ext]`/`@[simp]`
attributes, docstrings on all public declarations, `open scoped BigOperators`,
minimal imports per file. The Hahn Series bridge enables interoperability with
`Mathlib.Algebra.Vertex.VertexOperator`.

## Acknowledgments

Dr. Scott Carnahan reviewed an earlier version and suggested three improvements that
shaped the current design:

1. **Mathlib `BinomialRing` API** -- The custom 195-line binomial module was replaced
   by Mathlib's `Ring.choose`, reducing `Binomial.lean` to ~80 lines.
2. **Proof conciseness** -- Verbose proofs across `Mul.lean`, `Delta.lean`,
   `Expansion.lean`, and `Decomposition.lean` were compressed by factoring shared
   patterns and eliminating redundant case analysis.
3. **N-variable locality** -- Locality, delta, decomposition, j-th products, and
   Fourier coefficients were generalized from 2-variable to arbitrary pairs
   `(i, j)` in an `n`-variable distribution, supporting downstream results such as
   Lemma 1.5.4 / Corollary 2.4.2 of Matsuo--Nagatomo. Backward-compatible `abbrev`
   aliases preserve the original 2-variable API.

## References

- Nozaradan, C. *Introduction to Vertex Algebras*. Section 1: Formal Calculus.
- Carnahan, S. `Mathlib.Algebra.Vertex.VertexOperator`.

## License

Released under Apache 2.0 license.
