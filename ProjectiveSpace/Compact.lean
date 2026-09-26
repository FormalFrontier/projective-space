/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.StandardChartScheme
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Compactness of polynomial projective space

Polynomial projective space with finitely many coordinates is quasicompact.
This follows from its standard finite affine-coordinate cover.
-/

public section

noncomputable section

open AlgebraicGeometry

scoped[ProjectiveSpace] attribute [instance] MvPolynomial.gradedAlgebra

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R]
variable (ι : Type v)

/-- Polynomial projective space with a finite coordinate type is
quasicompact. -/
instance instCompactSpaceProj [Finite ι] : CompactSpace
    (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule ι R)) := by
  let _ := Fintype.ofFinite ι
  let _ : Finite (standardCoordinateAffineOpenCover R ι).openCover.I₀ := by
    change Finite ι
    infer_instance
  let _ : ∀ i, IsAffine
      ((standardCoordinateAffineOpenCover R ι).openCover.X i) :=
    fun i ↦ AlgebraicGeometry.Scheme.isAffine_affineOpenCover _
      (standardCoordinateAffineOpenCover R ι) i
  exact (standardCoordinateAffineOpenCover R ι).openCover.compactSpace

end ProjectiveSpace
