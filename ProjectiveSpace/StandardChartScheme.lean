/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.StandardChart
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The standard-coordinate affine cover of projective space

This file packages the standard affine cover of projective space over a
commutative ring. Its `i`th component is literally the spectrum of the
polynomial ring in the coordinates other than `i`. The component map is the
usual identification with the degree-zero homogeneous localization at `X i`,
followed by the canonical open immersion into `Proj`.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory

scoped[ProjectiveSpace] attribute [instance] MvPolynomial.gradedAlgebra

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R]
variable (ι : Type v)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

private theorem X_mem_degree_one (i : ι) :
    MvPolynomial.X i ∈ 𝒜 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).2
    (MvPolynomial.isHomogeneous_X R i)

/-- The standard coordinate basic opens cover projective space. -/
theorem iSup_basicOpen_X_eq_top :
    ⨆ i : ι, AlgebraicGeometry.Proj.basicOpen 𝒜
      (MvPolynomial.X i) = ⊤ := by
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top' 𝒜
  · intro i
    exact ⟨1, X_mem_degree_one R ι i⟩
  · exact adjoin_degreeZero_range_X_eq_top R ι

/-- The spectrum of the polynomial coordinates on the `i`th standard chart
is canonically isomorphic to the spectrum of its degree-zero homogeneous
localization. -/
@[expose] noncomputable def standardCoordinateChartIso [Fintype ι] (i : ι) :
  AlgebraicGeometry.Spec
        (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)) ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (StandardChart R ι i)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso
    (standardChartEquiv R ι i).toRingEquiv.toCommRingCatIso.symm.op

/-- The `i`th standard polynomial chart map to projective space. -/
@[expose] noncomputable def standardCoordinateChartMap [Fintype ι] (i : ι) :
    AlgebraicGeometry.Spec
        (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)) ⟶
      AlgebraicGeometry.Proj 𝒜 :=
  (standardCoordinateChartIso R ι i).hom ≫
    AlgebraicGeometry.Proj.awayι 𝒜 (MvPolynomial.X i)
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).2
        (MvPolynomial.isHomogeneous_X R i)) (by simp)

private def standardCoordinateChartMap_privateConstruction [Fintype ι] (i : ι) :
    AlgebraicGeometry.Spec
        (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)) ⟶
      AlgebraicGeometry.Proj 𝒜 :=
  (standardCoordinateChartIso R ι i).hom ≫
    AlgebraicGeometry.Proj.awayι 𝒜 (MvPolynomial.X i)
      (X_mem_degree_one R ι i) (by simp)

private theorem standardCoordinateChartMap_eq_privateConstruction [Fintype ι]
    (i : ι) : standardCoordinateChartMap R ι i =
      standardCoordinateChartMap_privateConstruction R ι i := rfl

instance standardCoordinateChartMap_isOpenImmersion [Fintype ι] (i : ι) :
    AlgebraicGeometry.IsOpenImmersion
      (standardCoordinateChartMap R ι i) := by
  dsimp [standardCoordinateChartMap]
  exact AlgebraicGeometry.IsOpenImmersion.comp _ _

/-- The range of the `i`th standard coordinate chart map is its projective
basic open. -/
theorem standardCoordinateChartMap_opensRange [Fintype ι] (i : ι) :
    (standardCoordinateChartMap R ι i).opensRange =
      AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X i) := by
  unfold standardCoordinateChartMap
  exact (AlgebraicGeometry.Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (AlgebraicGeometry.Proj.opensRange_awayι 𝒜 (MvPolynomial.X i)
      (X_mem_degree_one R ι i) (by simp))

/-- The affine open cover of projective space by its literal polynomial
standard charts. -/
@[expose] noncomputable def standardCoordinateAffineOpenCover [Fintype ι] :
    (AlgebraicGeometry.Proj 𝒜).AffineOpenCover where
  I₀ := ι
  X i := CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)
  f i := standardCoordinateChartMap R ι i
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_X_eq_top R ι).ge (Set.mem_univ x))).choose
  covers x := by
    let i := (TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_basicOpen_X_eq_top R ι).ge (Set.mem_univ x))).choose
    have hx := (TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_basicOpen_X_eq_top R ι).ge (Set.mem_univ x))).choose_spec
    change x ∈ (standardCoordinateChartMap R ι i).opensRange
    rw [standardCoordinateChartMap_opensRange]
    exact hx
  map_prop i := standardCoordinateChartMap_isOpenImmersion R ι i

/-- The component maps of the standard-coordinate affine open cover are the
standard coordinate chart maps. -/
@[simp]
theorem standardCoordinateAffineOpenCover_f [Fintype ι] (i : ι) :
    (standardCoordinateAffineOpenCover R ι).f i =
      standardCoordinateChartMap R ι i := rfl

/-- A universe-lifted copy of the standard-coordinate open cover, suitable
for the single-universe gluing API. -/
@[expose] noncomputable def standardCoordinateGluingOpenCover [Fintype ι] :
    (AlgebraicGeometry.Proj 𝒜).OpenCover.{max u v} :=
  AlgebraicGeometry.Scheme.Cover.copy
    (standardCoordinateAffineOpenCover R ι).openCover
    (ULift.{max u v} ι)
    (fun i ↦ AlgebraicGeometry.Spec
      (CommRingCat.of (MvPolynomial {j : ι // j ≠ i.down} R)))
    (fun i ↦ standardCoordinateChartMap R ι i.down)
    Equiv.ulift
    (fun _ ↦ Iso.refl _)
    (fun _ ↦ rfl)

@[simp]
theorem standardCoordinateGluingOpenCover_f [Fintype ι] (i : ι) :
    (standardCoordinateGluingOpenCover R ι).f (ULift.up i) =
      standardCoordinateChartMap R ι i := rfl

/-- The gluing datum of the literal polynomial standard-chart cover. -/
noncomputable abbrev standardCoordinateGlueData [Fintype ι] :
    AlgebraicGeometry.Scheme.GlueData :=
  (standardCoordinateGluingOpenCover R ι).gluedCover

/-- Gluing the literal polynomial standard charts recovers intrinsic
projective space. -/
noncomputable def standardCoordinateGluedIsoProj [Fintype ι] :
    (standardCoordinateGlueData R ι).glued ≅
      AlgebraicGeometry.Proj 𝒜 :=
  asIso (standardCoordinateGluingOpenCover R ι).fromGlued

/-- Under the canonical gluing isomorphism, each glued chart inclusion is the
corresponding standard coordinate chart map. -/
@[reassoc]
theorem standardCoordinateGlueData_ι_gluedIsoProj_hom [Fintype ι] (i : ι) :
    (standardCoordinateGlueData R ι).ι (ULift.up i) ≫
        (standardCoordinateGluedIsoProj R ι).hom =
      standardCoordinateChartMap R ι i := by
  exact AlgebraicGeometry.Scheme.Cover.ι_fromGlued
    (standardCoordinateGluingOpenCover R ι) (ULift.up i)

end ProjectiveSpace
