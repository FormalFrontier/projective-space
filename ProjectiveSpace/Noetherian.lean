/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.CoefficientRingBase
public import GradedRings.Noetherian
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Noetherian projective spectra

The projective spectrum of a naturally graded Noetherian commutative ring is a
Noetherian scheme. In particular, projective space with finitely many
coordinates over a Noetherian commutative ring is a Noetherian scheme. Mathlib
then supplies Noetherianity of the underlying topological space.

The degree-zero part of a Noetherian graded ring is Noetherian by Mathlib;
Graded Rings supplies finite type over that part. Mathlib's locally-finite-type
and quasicompact structure morphism to its spectrum provides the scheme-level
route. No degree-one generation or nontriviality assumption is needed.

## References

* The Stacks Project, *Noetherian schemes*, Tag 01OU.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, the
  projective-space corollary following Exercise 5.1.C.
* Mathlib, `AlgebraicGeometry.Noetherian` and
  `AlgebraicGeometry.ProjectiveSpectrum.Proper`; Formal Frontier Graded Rings,
  `GradedRings.Noetherian` and `GradedRings.FiniteType`.
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Proj

universe u v

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The projective spectrum of a naturally graded Noetherian commutative ring
is a Noetherian scheme (Stacks Project, Tag 01OU). This includes empty
projective spectra and the zero ring. -/
instance isNoetherian [IsNoetherianRing A] :
    IsNoetherian (Proj 𝒜) := by
  let _ : Algebra.FiniteType (𝒜 0) A :=
    GradedAlgebra.finiteType_of_irrelevant_fg 𝒜
      (GradedAlgebra.irrelevant_fg_of_isNoetherianRing 𝒜)
  have _ : IsLocallyNoetherian (Proj 𝒜) :=
    LocallyOfFiniteType.isLocallyNoetherian (Proj.toSpecZero 𝒜)
  have _ : CompactSpace (Proj 𝒜) :=
    QuasiCompact.compactSpace_of_compactSpace (Proj.toSpecZero 𝒜)
  exact ⟨⟩

end AlgebraicGeometry.Proj

scoped[ProjectiveSpace] attribute [instance] MvPolynomial.gradedAlgebra

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (ι : Type v) [Finite ι]

/-- Polynomial projective space in finitely many coordinates over a Noetherian
commutative ring is a Noetherian scheme. In particular, this gives the
finite-coordinate projective-space corollary following Vakil, Exercise 5.1.C,
without requiring a field or a nonempty coordinate type. -/
theorem isNoetherian_polynomialProj :
    AlgebraicGeometry.IsNoetherian
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule ι R)) := by
  infer_instance

end ProjectiveSpace
