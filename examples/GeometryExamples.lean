/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveSpace.BasicOpenBasis
import ProjectiveSpace.ProjectiveNullstellensatz
import ProjectiveSpace.HomogeneousDimension
import ProjectiveSpace.Irreducible

/-!
# Geometry recipes for projective spectra

## Positive basic opens and projective vanishing

Let `A : Type u` be a commutative ring, `σ : Type v` have `SetLike σ A`
and `AddSubgroupClass σ A`, and let `𝒜 : ℕ → σ` have `GradedRing 𝒜`.
For `degree : PNat` and `f : 𝒜 (degree : ℕ)`, the set underlying
`AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)` belongs to
`AlgebraicGeometry.Proj.positiveBasicOpens 𝒜`: its defining witness is
`⟨⟨degree, f⟩, rfl⟩`. For the basis property itself, use
`AlgebraicGeometry.Proj.isTopologicalBasis_positiveBasicOpens 𝒜` directly.
The positive degree is part of the indexing here, not a statement about
arbitrary degree-zero basic opens.

For `I : HomogeneousIdeal 𝒜`, `f : A`, `degree : ℕ`,
`hf : f ∈ 𝒜 degree`, and `hdegree : 0 < degree`, apply
`ProjectiveSpectrum.mem_vanishingIdeal_zeroLocus_iff_mem_radical 𝒜 I hf hdegree`.
Its reverse implication, `.2 h`, sends `h : f ∈ I.toIdeal.radical` to
`f ∈ ProjectiveSpectrum.vanishingIdeal (ProjectiveSpectrum.zeroLocus 𝒜 I)`.
This recipe keeps both homogeneity and strict positivity explicit; it does
not supply a degree-zero variant.

## Homogeneous dimension and irreducibility

The dimension calculation uses a separate `R : Type u` with
`CommSemiring R` and `StrongRankCondition R`. For `ι : Type v` with
`Fintype ι` and any `degree : ℕ`, the direct producer
`ProjectiveSpace.finrank_homogeneousSubmodule R ι degree` gives
`Module.finrank R (MvPolynomial.homogeneousSubmodule ι R degree) =
(Fintype.card ι).multichoose degree`.
This is the finite-coordinate finrank formula, including degree zero;
its hypotheses are not a field assumption.

For a separate `S : Type u` with `CommRing S` and `IsDomain S`, and
`ι : Type v` with `Nonempty ι`, use instance inference for
`IrreducibleSpace (AlgebraicGeometry.Proj
  (MvPolynomial.homogeneousSubmodule ι S))`.
The instance route here uses nonempty coordinates, not the `Fintype`
hypothesis used by the dimension formula. These two recipes should not
be conflated into a single set of assumptions.
-/
