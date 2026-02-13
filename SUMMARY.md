# Summary: Formal Distribution Library

An axiom-free Lean 4 formalization covering most of Section 1 (Formal Calculus) from
Nozaradan's *Introduction to Vertex Algebras*, refactored into 8 mathlib-compatible
modules with a Hahn Series interoperability bridge. Propositions 1.2.3, 1.2.5, 1.3.6
and Definition 1.3.3 are intentionally omitted (see "Not Formalized" below).

## At a Glance

- **2950 lines** across 8 submodules + root re-export
- **0 axioms, 0 sorry, 0 admits**
- **~150 public declarations** (definitions, theorems, instances)
- **`lake build`**: 1395 jobs, 0 errors
- Follows mathlib conventions throughout

## Modules

| Module | Lines | Contents |
|--------|------:|---------|
| `Basic.lean` | 431 | `FormalDistribution`, `GeneralizedFormalDistribution`, type aliases, `Zero`/`Add`/`SMul` instances |
| `Deriv.lean` | 181 | `deriv`, `iteratedDeriv`, linearity and commutativity lemmas |
| `Mul.lean` | 955 | 1D/2D Cauchy product, ring axioms, `embedFst`/`embedSnd`, `residueAt`, `mulGen` |
| `Fourier.lean` | 231 | `fourierExpansion`, `fourierMode`, `residue`, linearity, derivative interaction |
| `Binomial.lean` | 177 | `Int.extChoose`, recursion, agreement with `Nat.choose` |
| `Expansion.lean` | 251 | `expansion_izw`, `expansion_iwz`, derivative commutation |
| `Delta.lean` | 540 | `formalDelta`, all 7 properties of Proposition 1.3.5 |
| `HahnSeries.lean` | 149 | `toHahnSeries`/`ofHahnSeries`, preserves `+`/`*`/`0`/`1`, round-trips |

## Mathematical Coverage

### Section 1.1 -- Formal Distributions
- Two-tier type system: `FormalDistribution` (finite support, enables axiom-free multiplication) and `GeneralizedFormalDistribution` (bounded-finite support, accommodates `formalDelta`)
- Full arithmetic: `Zero`, `Add`, `SMul`, `Mul` instances
- 1D and 2D multiplication with complete ring axioms (`add_mul`, `mul_add`, `smul_mul`, `mul_smul`, zero absorption)

### Section 1.2 -- Expansion Operators
- Fourier expansion, modes, and residue with linearity proofs
- Extended binomial `Int.extChoose` for integer arguments
- Expansion operators `expansion_izw`/`expansion_iwz` with derivative commutation (Proposition 1.2.6)

### Section 1.3 -- Formal Delta
- `formalDelta : GenFormalDist2 A` with `formalDelta_coeff` by `rfl`
- Proposition 1.3.4: `formalDelta_eq_expansion_izw_sub_iwz`
- All 7 properties of Proposition 1.3.5 proved:
  1. `mul_z_sub_w_pow_succ_iteratedDeriv_formalDelta_eq_zero` -- $(z-w)^{n+1} \partial_w^n\delta = 0$
  2. `mul_z_sub_w_iteratedDeriv_formalDelta` -- $(z-w) \partial_w^n\delta = n \partial_w^{n-1}\delta$
  3. `formalDelta_symm` -- symmetry (definitional, by `rfl`)
  4. `deriv_fst_formalDelta_add_deriv_snd_formalDelta` -- $\partial_z\delta + \partial_w\delta = 0$
  5. `embedFst_mulGen_formalDelta_eq_embedSnd` -- $a(z)\delta = a(w)\delta$
  6. `residueAt_embedFst_mulGen_formalDelta` -- $\operatorname{Res}_z a(z)\delta = a(w)$
  7. `mul_z_sub_w_pow_iteratedDeriv_formalDelta` -- $(z-w)^j \partial_w^n\delta$ falling factorial formula

### Hahn Series Bridge
- `toHahnSeries : FormalDist1 R -> HahnSeries Z R` (finite support implies PWO via `Set.Finite.isPWO`)
- Preserves zero, one, addition, and Cauchy product multiplication
- Inverse `ofHahnSeries` for finite-support Hahn series
- Round-trip identities in both directions
- Enables interoperability with `Mathlib.Algebra.Vertex.VertexOperator`

## Design Decisions

1. **Finite support for `FormalDistribution`** -- enables axiom-free multiplication via `Set.Finite.biUnion`, at the cost of requiring `GeneralizedFormalDistribution` for `formalDelta`.

2. **`GeneralizedFormalDistribution` for delta** -- `formalDelta` has infinite support along `{(k, -k-1) | k in Z}`, which is bounded-finite but not globally finite. This avoids any axioms.

3. **Modular file structure** -- each file has minimal imports, following mathlib's one-concept-per-file convention.

4. **`HahnSeries` bridge** -- maps 1D formal distributions into mathlib's `HahnSeries Z R`, connecting to Carnahan's vertex operator formalization.

## Not Formalized

Intentionally omitted from Section 1:

- **Proposition 1.2.3** (expansion formulas via power series evaluation) -- requires topological/analytic machinery beyond the algebraic scope
- **Proposition 1.2.5** (uniqueness of expansion) -- same dependency
- **Definition 1.3.3** (alternative delta via limits) -- not needed; Proposition 1.3.4 is proved directly
- **Proposition 1.3.6** (decomposition theorem) -- requires formal Laurent series machinery

## Future Directions

- Vertex algebra definition (Nozaradan Section 4) using the Hahn Series bridge
- Conformal field theory (Sections 2-3): Virasoro algebra, OPE, normal ordering
- Upstream selected results to mathlib
