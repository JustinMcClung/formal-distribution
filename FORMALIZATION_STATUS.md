# Formalization Status: Nozaradan Chapter 1 -- Formal Calculus

**8 modules** under `FormalDistribution/` | **2950 lines** | **0 errors | 0 sorry | 0 axioms**

Everything below is fully proved and compiles cleanly with `lake build` (1395 jobs).

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

## Type Aliases

| Alias | Expansion | Module |
|-------|-----------|--------|
| `FormalDist1 A` | `FormalDistribution A 1` | Basic |
| `FormalDist2 A` | `FormalDistribution A 2` | Basic |
| `GenFormalDist2 A` | `GeneralizedFormalDistribution A 2` | Basic |

## Algebraic Instances

### `GeneralizedFormalDistribution A n`
- `Zero`, `Add`, `Neg`, `Sub`, `SMul A`

### `FormalDistribution A n`
- `Zero`, `Add`, `SMul A`

### `FormalDist1 A` (`[Ring A]`)
- `Mul` (Cauchy product), `One`

### `FormalDist2 A` (`[CommRing A]`)
- `Mul` (2D Cauchy product)

## Theorems -- Multiplication

### 1D (`Ring A`)

| Theorem | Statement | Module |
|---------|-----------|--------|
| `zero_mul_1d` | `0 * a = 0` | Mul |
| `mul_zero_1d` | `a * 0 = 0` | Mul |
| `add_mul_1d` | `(a + b) * c = a * c + b * c` | Mul |
| `mul_add_1d` | `a * (b + c) = a * b + a * c` | Mul |
| `smul_mul_1d` | `(r • a) * b = r • (a * b)` | Mul |

### 1D (`CommRing A`)

| Theorem | Statement | Module |
|---------|-----------|--------|
| `mul_smul_1d` | `a * (r • b) = r • (a * b)` | Mul |

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
| `deriv_z_expansion_izw` | `d_z i_{z,w}(z-w)^k = k * i_{z,w}(z-w)^{k-1}` | Expansion |
| `deriv_w_expansion_izw` | `d_w i_{z,w}(z-w)^k = -k * i_{z,w}(z-w)^{k-1}` | Expansion |
| `deriv_z_expansion_iwz` | `d_z i_{w,z}(z-w)^k = k * i_{w,z}(z-w)^{k-1}` | Expansion |
| `deriv_w_expansion_iwz` | `d_w i_{w,z}(z-w)^k = -k * i_{w,z}(z-w)^{k-1}` | Expansion |

## Theorems -- Dirac Delta

### Proposition 1.3.4

| Theorem | Statement | Module |
|---------|-----------|--------|
| `formalDelta_eq_expansion_izw_sub_iwz` | `delta = i_{z,w}(z-w)^{-1} - i_{w,z}(z-w)^{-1}` | Delta |

### Proposition 1.3.5 -- All 7 Properties

| # | Theorem | Statement | Module |
|---|---------|-----------|--------|
| 1 | `mul_z_sub_w_pow_succ_iteratedDeriv_formalDelta_eq_zero` | `(z-w)^{n+1} d_w^n delta = 0` | Delta |
| 2 | `mul_z_sub_w_iteratedDeriv_formalDelta` | `(z-w) d_w^n delta = n * d_w^{n-1} delta` for n >= 1 | Delta |
| 3 | `formalDelta_symm` | `delta(z,w) = delta(w,z)` | Delta |
| 4 | `deriv_fst_formalDelta_add_deriv_snd_formalDelta` | `d_z delta + d_w delta = 0` | Delta |
| 5 | `embedFst_mulGen_formalDelta_eq_embedSnd` | `a(z) delta = a(w) delta` | Delta |
| 6 | `residueAt_embedFst_mulGen_formalDelta` | `Res_z a(z) delta = a(w)` | Delta |
| 7 | `mul_z_sub_w_pow_iteratedDeriv_formalDelta` | `(z-w)^j d_w^n delta = n_j * d_w^{n-j} delta` | Delta |

Property 7 is the falling factorial identity that generalizes Properties 1 and 2:
- j = n+1 recovers Property 1 (since n\_(n+1) = 0)
- j = 1 recovers Property 2 (since n\_1 = n)

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

## Not Formalized

Intentionally omitted from Chapter 1:

- **Proposition 1.2.3** (expansion formulas via power series evaluation) -- requires topological/analytic machinery
- **Proposition 1.2.5** (uniqueness of expansion) -- same dependency
- **Definition 1.3.3** (alternative delta via limits) -- not needed; Prop 1.3.4 proved directly
- **Proposition 1.3.6** (decomposition theorem) -- requires formal Laurent series machinery

## Verification

```bash
lake build
# Build completed successfully (1395 jobs).

grep -rn "sorry\|axiom\|admit" FormalDistribution/
# (No output)
```
