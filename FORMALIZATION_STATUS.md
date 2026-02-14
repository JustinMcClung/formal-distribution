# Formalization Status: Nozaradan Chapter 1 -- Formal Calculus

**11 modules** under `FormalDistribution/` | **4088 lines** | **0 errors | 0 sorry | 0 axioms**

Everything below is fully proved and compiles cleanly with `lake build` (1398 jobs).

---

## Definitions

| # | Reference | Lean Name | Module |
|---|-----------|-----------|--------|
| 1 | Def 1.1.1 | `FormalDistribution A n` | Basic |
| 2 | Def 1.1.1 | `GeneralizedFormalDistribution A n` | Basic |
| 3 | Def 1.1.1 | `FormalPolynomial A vars` | Basic |
| 4 | Def 1.1.1 | `FormalTaylorSeries A vars` | Basic |
| 5 | Def 1.1.3 | `fourierExpansion`, `fourierMode`, `residue` | Fourier |
| 6 | Def 1.2.1 | `expansion_izw k`, `expansion_iwz k` | Expansion |
| 7 | Def 1.2.2 | `Int.extChoose j n` | Binomial |
| 8 | Def 1.3.1 | `formalDelta` | Delta |
| 9 | Def 1.4.1 | `IsLocal`, `IsLocalOfOrder`, `MutuallyLocal` | Locality |
| 10 | Rem 1.4.4 | `nthProduct` (j-th product) | Locality |
| 11 | Def 1.5.1 | `fourierTransformCoeff` | FourierTransform |
| 12 | Def 1.5.3 | `twoVarFourierCoeff` | FourierTransform |

## Type Aliases

| Alias | Expansion | Module |
|-------|-----------|--------|
| `FormalDist1 A` | `FormalDistribution A 1` | Basic |
| `FormalDist2 A` | `FormalDistribution A 2` | Basic |
| `GenFormalDist1 A` | `GeneralizedFormalDistribution A 1` | Basic |
| `GenFormalDist2 A` | `GeneralizedFormalDistribution A 2` | Basic |

## Algebraic Instances

### `GeneralizedFormalDistribution A n`
- `Zero`, `Add`, `Neg`, `Sub`, `SMul A`

### `FormalDistribution A n`
- `Zero`, `Add`, `Neg`, `Sub`, `SMul A`

### `FormalDist1 A` (`[Ring A]`)
- `Mul` (Cauchy product)

### `FormalDist1 A` (`[CommRing A]`)
- `One`, `CommRing` (via HahnSeries bridge)

### `FormalDist2 A` (`[CommRing A]`)
- `Mul` (2D Cauchy product)

## Theorems -- Multiplication

### 1D (`Ring A`)

| Theorem | Statement | Module |
|---------|-----------|--------|
| `zero_mul` | `0 * a = 0` | Mul |
| `mul_zero` | `a * 0 = 0` | Mul |
| `add_mul` | `(a + b) * c = a * c + b * c` | Mul |
| `mul_add` | `a * (b + c) = a * b + a * c` | Mul |
| `smul_mul` | `(r • a) * b = r • (a * b)` | Mul |

### 1D (`CommRing A`)

| Theorem | Statement | Module |
|---------|-----------|--------|
| `mul_smul` | `a * (r • b) = r • (a * b)` | Mul |

### 2D (`CommRing A`)

| Theorem | Statement | Module |
|---------|-----------|--------|
| `zero_mul_2d`, `mul_zero_2d` | Zero absorption | Mul |
| `add_mul_2d`, `mul_add_2d` | Distributivity | Mul |
| `smul_mul_2d`, `mul_smul_2d` | Scalar compatibility | Mul |

## Theorems -- Differentiation

| Theorem | Statement | Module |
|---------|-----------|--------|
| `deriv_zero` | `(0).deriv i = 0` | Deriv |
| `deriv_add` | `(a + b).deriv i = a.deriv i + b.deriv i` | Deriv |
| `deriv_smul` | `(c • a).deriv i = c • a.deriv i` | Deriv |
| `deriv_deriv_comm` | `(a.deriv i).deriv j = (a.deriv j).deriv i` | Deriv |
| `deriv_deriv_eq_iteratedDeriv` | `(a.deriv i).deriv i = a.iteratedDeriv i 2` | Deriv |
| `iteratedDeriv_add_eq` | `iteratedDeriv (iteratedDeriv a i k) i m = iteratedDeriv a i (k+m)` | Deriv |
| `iteratedDeriv_zero` | `(0).iteratedDeriv i k = 0` | Deriv |
| `iteratedDeriv_add` | Linearity of iterated derivatives | Deriv |
| `iteratedDeriv_smul` | Scalar compatibility of iterated derivatives | Deriv |

## Theorems -- Fourier Analysis

| Theorem | Statement | Module |
|---------|-----------|--------|
| `fourierExpansion_add/smul/zero` | Linearity | Fourier |
| `fourierMode_add/smul/zero` | Linearity | Fourier |
| `residue_add/smul/zero` | Linearity | Fourier |
| `fourierExpansion_linear` | Full linearity | Fourier |
| `fourierMode_linear` | Full linearity | Fourier |
| `residue_linear` | Full linearity | Fourier |
| `fourierExpansion_deriv` | `fe(da, n) = (n+1) * fe(a, n+1)` | Fourier |
| `fourierMode_deriv` | `fm(da, n) = -n * fm(a, n-1)` | Fourier |
| `residue_deriv` | `Res(da) = 0` | Fourier |
| `residue_iteratedDeriv` | `Res(d^k a) = 0` for k >= 1 | Fourier |
| `residue_eq_fourierMode_zero` | `Res(a) = fm(a, 0)` | Fourier |
| `fourierExpansion_eq_fourierMode_neg` | `fe(a, n) = fm(a, -n-1)` | Fourier |

## Theorems -- Extended Binomial Coefficients

| Theorem | Statement | Module |
|---------|-----------|--------|
| `Int.extChoose_zero` | `C(j, 0) = 1` | Binomial |
| `Int.extChoose_succ` | `C(j, n+1) = C(j, n) * (j-n) / (n+1)` | Binomial |
| `Int.extChoose_nonneg` | `C(k, n) = Nat.choose k n` for natural k, n | Binomial |

## Theorems -- Expansion Operators (Proposition 1.2.6)

| Theorem | Statement | Module |
|---------|-----------|--------|
| `deriv_fst_expansion_izw` | `d_z i_{z,w}(z-w)^k = k * i_{z,w}(z-w)^{k-1}` | Expansion |
| `deriv_snd_expansion_izw` | `d_w i_{z,w}(z-w)^k = -k * i_{z,w}(z-w)^{k-1}` | Expansion |
| `deriv_fst_expansion_iwz` | `d_z i_{w,z}(z-w)^k = k * i_{w,z}(z-w)^{k-1}` | Expansion |
| `deriv_snd_expansion_iwz` | `d_w i_{w,z}(z-w)^k = -k * i_{w,z}(z-w)^{k-1}` | Expansion |

### Remark 1.2.4

| Theorem | Statement | Module |
|---------|-----------|--------|
| `expansion_izw_eq_iwz_of_nonneg` | `i_{z,w}(z-w)^k = i_{w,z}(z-w)^k` for `k ≥ 0` | Expansion |

## Theorems -- Formal Delta

### Proposition 1.3.4

| Theorem | Statement | Module |
|---------|-----------|--------|
| `formalDelta_eq_expansion_izw_sub_iwz` | `delta = i_{z,w}(z-w)^{-1} - i_{w,z}(z-w)^{-1}` | Delta |

### Proposition 1.3.5 -- All 7 Properties

| # | Theorem | Statement | Module |
|---|---------|-----------|--------|
| 1 | `mul_z_sub_w_pow_succ_iteratedDeriv_formalDelta_eq_zero` | `(z-w)^{n+1} d_w^n delta = 0` | Delta |
| 2 | `mul_z_sub_w_iteratedDeriv_formalDelta` | `(z-w) d_w^n delta = n * d_w^{n-1} delta` for n >= 1 | Delta |
| 3 | `formalDelta_swap` | `delta(z,w).swap = delta(z,w)` (variable-swap symmetry) | Delta |
| 4 | `deriv_fst_formalDelta_add_deriv_snd_formalDelta` | `d_z delta + d_w delta = 0` | Delta |
| 5 | `embedFst_mulGen_formalDelta_eq_embedSnd` | `a(z) delta = a(w) delta` | Delta |
| 6 | `residueAt_embedFst_mulGen_formalDelta` | `Res_z a(z) delta = a(w)` | Delta |
| 7 | `mul_z_sub_w_pow_iteratedDeriv_formalDelta` | `(z-w)^j d_w^n delta = n_j * d_w^{n-j} delta` | Delta |

Property 7 is the falling factorial identity that generalizes Properties 1 and 2:
- j = n+1 recovers Property 1 (since n\_(n+1) = 0)
- j = 1 recovers Property 2 (since n\_1 = n)

### Proposition 1.3.6 -- Decomposition Theorem

| Theorem | Statement | Module |
|---------|-----------|--------|
| `antidiag_const_of_mul_z_sub_w_zero` | `(z-w)f = 0` implies `f(p,q) = f(-1, p+q+1)` | Decomposition |
| `decomposition_theorem` | `(z-w)^N f = 0` implies `f(p,q) = ∑_{j<N} C(-p-1,j) · c_j(p+q+j+1)` | Decomposition |

The decomposition is formulated at the coefficient level using generalized binomial
coefficients, avoiding division by factorials (no `[Algebra ℚ A]` required).

## Theorems -- Generalized Binomial Coefficients

| Theorem | Statement | Module |
|---------|-----------|--------|
| `intBinomial_zero` | `C(k, 0) = 1` | Binomial |
| `intBinomial_neg_one` | `C(-1, n) = (-1)^n` | Binomial |
| `intBinomial_zero_left` | `C(0, n+1) = 0` | Binomial |
| `intBinomial_pascal` | `C(k+1, n+1) = C(k, n) + C(k, n+1)` | Binomial |
| `intBinomial_mul_sub` | `(k-n) C(k,n) = k C(k-1,n)` | Binomial |
| `intBinomial_succ_mul_eq` | `(n+1) C(k,n+1) = k C(k-1,n)` | Binomial |
| `Int.extChoose_eq_intBinomial` | `extChoose j n = intBinomial j n` (cast to ℚ) | Binomial |

## Theorems -- Hahn Series Bridge

| Theorem | Statement | Module |
|---------|-----------|--------|
| `toHahnSeries_coeff` | `(toHahnSeries a).coeff n = a.coeff (fun _ => n)` | HahnSeries |
| `toHahnSeries_zero` | `toHahnSeries 0 = 0` | HahnSeries |
| `toHahnSeries_one` | `toHahnSeries 1 = 1` | HahnSeries |
| `toHahnSeries_add` | `toHahnSeries (a + b) = toHahnSeries a + toHahnSeries b` | HahnSeries |
| `toHahnSeries_mul` | `toHahnSeries (a * b) = toHahnSeries a * toHahnSeries b` | HahnSeries |
| `toHahnSeries_support_finite` | `(toHahnSeries a).support.Finite` | HahnSeries |
| `toHahnSeries_ofHahnSeries` | `toHahnSeries (ofHahnSeries f hf) = f` | HahnSeries |
| `ofHahnSeries_toHahnSeries` | `ofHahnSeries (toHahnSeries a) _ = a` | HahnSeries |

## Infrastructure

### Embeddings (1D -> 2D, `CommRing A`)

| Name | Description | Module |
|------|-------------|--------|
| `embedFst`, `embedSnd` | Embed 1D distributions into 2D | Mul |
| `mulGen` | Mixed multiplication `FormalDist2 x GenFormalDist2 -> GenFormalDist2` | Mul |
| `residueAt` | Residue in a specific variable of a 2D distribution | Mul |

### (z-w) Multiplication

| Name | Description | Module |
|------|-------------|--------|
| `mul_z_sub_w` | Multiply generalized 2D distribution by (z-w) | Delta |
| `mul_z_sub_w_pow` | Multiply by (z-w)^j | Delta |
| `mul_z_sub_w_smul` | Commutes with scalar multiplication | Delta |

### Iterated Derivative Coefficients

| Name | Description | Module |
|------|-------------|--------|
| `iteratedDeriv_snd_formalDelta_coeff` | Explicit coefficient formula for d_w^n delta | Delta |

## Theorems -- Locality (Section 1.4)

### Infrastructure

| Name | Description | Module |
|------|-------------|--------|
| `externalProduct` | Tensor product `a(z)b(w)` of two 1D distributions | Locality |
| `formalCommutator` | Commutator `[a(z), b(w)] = a(z)b(w) - b(w)a(z)` | Locality |
| `nthProduct` | j-th product `a_{(j)} b = Res_z (z-w)^j [a(z), b(w)]` | Locality |

### Example 1.4.2

| Theorem | Statement | Module |
|---------|-----------|--------|
| `formalDelta_isLocal` | `delta` is local with `N = 1` | Locality |
| `iteratedDeriv_formalDelta_isLocal` | `d^n delta` is local with `N = n + 1` | Locality |

### Derivative Stability

| Theorem | Statement | Module |
|---------|-----------|--------|
| `isLocal_deriv_snd` | If `f` is local of order `N`, then `d_w f` is local of order `N + 1` | Locality |

### CommRing Locality

| Theorem | Statement | Module |
|---------|-----------|--------|
| `formalCommutator_eq_zero` | `[a, b] = 0` when `A` is a `CommRing` | Locality |
| `commRing_mutuallyLocal` | All pairs are mutually local over `CommRing` | Locality |

### Theorem 1.4.3 -- Decomposition for Local Distributions

| Theorem | Statement | Module |
|---------|-----------|--------|
| `local_decomposition` | If `[a,b]` is local of order `N`, then `[a(z),b(w)] = ∑_{j<N} c_j(w) ∂^j_w δ(z,w)` | Locality |
| `mul_z_sub_w_pow_zero_of_ge` | `(z-w)^N f = 0` and `j ≥ N` implies `(z-w)^j f = 0` | Locality |
| `nthProduct_eq_zero_of_local` | `a_{(j)} b = 0` for `j ≥ N` when `[a,b]` is local of order `N` | Locality |

### Leibniz Rule and Integration by Parts

| Theorem | Statement | Module |
|---------|-----------|--------|
| `leibniz_deriv_fst_coeff2` | `Res_z (z-w)^j ∂_z f = -j · Res_z (z-w)^{j-1} f` (Leibniz rule) | Locality |
| `integration_by_parts` | `Res_z (z-w)^{j+1} ∂_z f = -(j+1) · Res_z (z-w)^j f` | Locality |

## Theorems -- Fourier Transform (Section 1.5)

### One-Variable (Definition 1.5.1, Propositions 1.5.2)

| Theorem | Statement | Module |
|---------|-----------|--------|
| `fourierTransformCoeff_deriv_zero` | `F(∂a)_0 = 0` | FourierTransform |
| `fourierTransformCoeff_deriv` | `F(∂a)_n = -F(a)_{n-1}` for `n ≥ 1` (Prop 1.5.2) | FourierTransform |
| `fourierMode_reflect` | `(a(-z))_n = (-1)^{n+1} · a_n` | FourierTransform |
| `fourierTransformCoeff_reflect` | `F(a(-z))_n = (-1)^{n+1} F(a)_n` (Prop 1.5.2(3)) | FourierTransform |

### Two-Variable (Definition 1.5.3, Proposition 1.5.4)

| Theorem | Statement | Module |
|---------|-----------|--------|
| `twoVarFourierCoeff_commutator_eq` | `F_{z,w}^λ([a,b])_j = (1/j!) · a_{(j)} b` (Prop 1.5.4) | FourierTransform |
| `twoVarFourierCoeff_deriv_fst_zero` | `F_{z,w}^λ(∂_z f)_0 = 0` | FourierTransform |
| `twoVarFourierCoeff_deriv_fst` | `F_{z,w}^λ(∂_z f)_{j+1} = -F_{z,w}^λ(f)_j` (Prop 1.5.4(2)) | FourierTransform |
| `twoVarFourierCoeff_eq_zero_of_local` | Lambda-bracket is polynomial for local distributions | FourierTransform |

## Intentional Omissions

Three items from Chapter 1 are intentionally omitted. None of them affect the
completeness of the algebraic theory; all downstream consequences are formalized.

### Proposition 1.2.3 (Expansion Formulas via Analytic Evaluation)

Proposition 1.2.3 states that substituting a complex number into the formal
geometric series `i_{z,w}(z-w)^k` recovers the classical Laurent expansion of
`(z-w)^k` in the region `|z| > |w|` (and similarly for `i_{w,z}` in `|w| > |z|`).

This is **analytic motivation**, not an algebraic result. Formalizing it would
require `Complex`, `HasSum`, geometric series convergence, and analytic
continuation machinery -- a substantial detour into analysis with no payoff for
the algebraic theory. The result is never used in any later proof; its role in
the text is to explain *why* the formal expansion operators are defined the way
they are. All algebraic consequences are already captured:

- Remark 1.2.4 (`expansion_izw_eq_iwz_of_nonneg`): both operators agree for `k ≥ 0`
- Proposition 1.2.6: derivative formulas for expansion operators
- Proposition 1.3.4: `δ(z,w) = i_{z,w}(z-w)^{-1} - i_{w,z}(z-w)^{-1}`

### Remark 1.2.5 (Notational Convention)

The text's "Proposition 1.2.5" is actually **Remark 1.2.5**, a notational
convention explaining how other references (particularly Lepowsky-Li) write
expansion operators using a different variable convention. It has no
mathematical content -- it is a note about notation in other books. There is
nothing to formalize.

### Definition 1.3.3 (Delta via Limits)

Definition 1.3.3 gives an alternative characterization of the formal delta
function as a limit of truncated sums. This definition is bypassed because
Proposition 1.3.4 (`formalDelta_eq_expansion_izw_sub_iwz`) is proved directly
from the coefficient-level definition, and all seven properties of
Proposition 1.3.5 follow without it.

---

All other definitions, propositions, theorems, remarks, and examples from
Sections 1.1--1.5 are formalized.

## Verification

```bash
lake build
# Build completed successfully (1398 jobs).

grep -rn "sorry\|axiom\|admit" FormalDistribution/
# (No output)
```
