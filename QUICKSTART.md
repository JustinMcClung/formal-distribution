# Quick Start

## Prerequisites

- [Lean 4](https://lean-lang.org/) (v4.28.0-rc1 or compatible)
- [elan](https://github.com/leanprover/elan) (Lean version manager)

```bash
# Install elan if needed
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

## Build

```bash
lake exe cache get   # fetch Mathlib oleans (~5 min first time)
lake build           # build the library
```

Expected output: `Build completed successfully (1395 jobs).`

## Explore

Open the project in VS Code with the Lean 4 extension.

### Core types

```lean
import FormalDistribution.Basic

-- Formal distributions with finite support
#check FormalDistribution    -- (A : Type*) -> [Ring A] -> (nvars : N) -> Type
#check FormalDist1           -- one-variable alias
#check FormalDist2           -- two-variable alias

-- Generalized: bounded-finite support (for delta)
#check GeneralizedFormalDistribution
#check GenFormalDist2
```

### Fourier analysis

```lean
import FormalDistribution.Fourier

-- Extract coefficient sequence from a distribution
#check fourierExpansion   -- FormalDist1 A -> (Z -> A)
#check fourierMode        -- FormalDist1 A -> Z -> A
#check residue            -- FormalDist1 A -> A
```

### Multiplication

```lean
import FormalDistribution.Mul

-- 1D distributions form a ring (Mul instance)
example (a b : FormalDist1 C) : FormalDist1 C := a * b

-- Ring axioms are proved
#check FormalDistribution.add_mul_1d
#check FormalDistribution.mul_add_1d
```

### Extended binomial

```lean
import FormalDistribution.Binomial

-- Works for negative integers
#check Int.extChoose      -- Z -> N -> Q
#check Int.extChoose_zero -- Int.extChoose j 0 = 1
```

### Expansion operators

```lean
import FormalDistribution.Expansion

#check expansion_izw   -- Z -> GenFormalDist2 A
#check expansion_iwz   -- Z -> GenFormalDist2 A
```

### Formal delta

```lean
import FormalDistribution.Delta

-- The formal delta distribution
#check formalDelta                   -- GenFormalDist2 A
#check formalDelta_coeff             -- coefficient formula (by rfl)

-- Key properties
#check FormalDelta.mul_z_sub_w_formalDelta   -- (z-w) delta = 0
#check FormalDelta.formalDelta_symm          -- delta(z,w) = delta(w,z)

-- a(z) delta(z,w) = a(w) delta(z,w)
#check FormalDelta.embedFst_mulGen_formalDelta_eq_embedSnd

-- Res_z a(z) delta(z,w) = a(w)
#check FormalDelta.residueAt_embedFst_mulGen_formalDelta
```

### Hahn Series bridge

```lean
import FormalDistribution.HahnSeries

-- Convert between FormalDist1 and Mathlib's HahnSeries
#check FormalDistribution.toHahnSeries   -- FormalDist1 R -> HahnSeries Z R
#check FormalDistribution.ofHahnSeries   -- HahnSeries Z R -> FormalDist1 R

-- Preserves algebraic structure
#check FormalDistribution.toHahnSeries_add
#check FormalDistribution.toHahnSeries_mul
#check FormalDistribution.toHahnSeries_one

-- Round-trip identities
#check FormalDistribution.toHahnSeries_ofHahnSeries
#check FormalDistribution.ofHahnSeries_toHahnSeries
```

## File Guide

| If you want to...                          | Read...              |
|--------------------------------------------|----------------------|
| Understand the core types                  | `Basic.lean`         |
| See how derivatives work                   | `Deriv.lean`         |
| Study multiplication proofs                | `Mul.lean`           |
| Work with Fourier modes / residues         | `Fourier.lean`       |
| Use extended binomial coefficients         | `Binomial.lean`      |
| Understand expansion operators             | `Expansion.lean`     |
| Study the formal delta and its properties  | `Delta.lean`         |
| Connect to Mathlib's HahnSeries           | `HahnSeries.lean`   |

## Troubleshooting

**Build fails with missing oleans:**
```bash
lake exe cache get && lake build
```

**Lean server slow or unresponsive:**
Restart via VS Code command palette: `Lean 4: Restart Server`

**Clean rebuild:**
```bash
lake clean && lake build
```

## References

- Nozaradan, *Introduction to Vertex Algebras*, Section 1
- [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
