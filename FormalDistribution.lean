/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FormalDistribution.Basic
import FormalDistribution.Deriv
import FormalDistribution.Mul
import FormalDistribution.Fourier
import FormalDistribution.Binomial
import FormalDistribution.Expansion
import FormalDistribution.Delta
import FormalDistribution.HahnSeries
import FormalDistribution.Decomposition
import FormalDistribution.Locality
import FormalDistribution.FourierTransform

/-!
# Formal Distributions

This is the root import file for the formal distribution library, which formalizes
Chapter 1 (Formal Calculus) from Nozaradan's "Introduction to Vertex Algebras."

## Contents

* `Basic` - Type definitions, algebraic instances
* `Deriv` - Formal differentiation
* `Mul` - Cauchy product multiplication, embeddings, residues
* `Fourier` - Fourier modes, residues
* `Binomial` - Extended binomial coefficients
* `Expansion` - Expansion operators `i_{z,w}`, `i_{w,z}`
* `Delta` - Formal delta distribution and its seven properties
* `HahnSeries` - Compatibility with Mathlib's HahnSeries
* `Decomposition` - Proposition 1.3.6: decomposition theorem
* `Locality` - Section 1.4: mutual locality, commutator, derivative stability
* `FourierTransform` - Section 1.5: Fourier transform, j-th product, lambda-bracket

## References

* [Nozaradan, *Introduction to Vertex Algebras*], Chapter 1
* [Kac, *Vertex Algebras for Beginners*], Chapter 1
-/
