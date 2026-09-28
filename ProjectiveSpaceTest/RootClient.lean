/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import ProjectiveSpace

/-!
# Aggregate-import client

Private named checks of the public root interface, including the scoped
polynomial grading, charts, point evaluation, graded transport and geometric
properties.
-/

open scoped ProjectiveSpace

namespace ProjectiveSpaceTest

universe u v uA uB uσ uτ

private noncomputable abbrev chart_algebra (R : Type u) [CommRing R]
    (ι : Type v) (i : ι) : Algebra R (ProjectiveSpace.StandardChart R ι i) :=
  inferInstance

private theorem polynomial_chart_cover (R : Type u) [CommRing R]
    (ι : Type v) :
    (⨆ i : ι, AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)) = ⊤ :=
  ProjectiveSpace.iSup_basicOpen_X_eq_top R ι

private theorem reduced_polynomial_proj (R : Type u)
    [CommRing R] [IsReduced R] (ι : Type v) [Finite ι] :
    AlgebraicGeometry.IsReduced
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule ι R)) :=
  inferInstance

private theorem compact_polynomial_proj (R : Type u)
    [CommRing R] (ι : Type v) [Finite ι] :
    CompactSpace
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule ι R)) :=
  inferInstance

private theorem point_on_chart {k : Type u} [Field k]
    {ι : Type v} (a : ι → k) (ha : a ≠ 0) (i : ι) :
    ProjectiveSpace.homogeneousCoordinatePoint a ha ∈
        ProjectiveSpectrum.basicOpen
          (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) ↔
      a i ≠ 0 :=
  ProjectiveSpace.homogeneousCoordinatePoint_mem_basicOpen_X_iff a ha i

private theorem point_generator {k : Type u} [Field k]
    {ι : Type v} (a : ι → k) (i : ι) :
    ProjectiveSpace.homogeneousCoordinateMap a (MvPolynomial.X i) =
      Polynomial.C (a i) * Polynomial.X := by
  simp

variable {A : Type uA} {B : Type uB}
variable {σ : Type uσ} {τ : Type uτ}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

private theorem transport_irrelevant (f : 𝒜 →+*ᵍ ℬ) :
    (HomogeneousIdeal.irrelevant 𝒜).map f ≤
      HomogeneousIdeal.irrelevant ℬ :=
  ProjectiveSpace.map_irrelevant_le f

private noncomputable def transport_points (f : 𝒜 →+*ᵍ ℬ)
    (g : ℬ →+*ᵍ 𝒜) (hfg : f.comp g = GradedRingHom.id ℬ)
    (hgf : g.comp f = GradedRingHom.id 𝒜) :
    ProjectiveSpectrum ℬ ≃ₜ ProjectiveSpectrum 𝒜 :=
  ProjectiveSpace.projectiveSpectrumHomeomorphOfInverseGradedRingHom
    f g hfg hgf

private noncomputable def veronese_whole_iso {ringType : Type u}
    [CommRing ringType] {componentType : Type v}
    [SetLike componentType ringType] [AddSubgroupClass componentType ringType]
    (grading : ℕ → componentType) [GradedRing grading]
    (degree : ℕ) (positive : 0 < degree) :
    AlgebraicGeometry.Proj grading ≅
      AlgebraicGeometry.Proj (GradedRing.Veronese.component grading degree) :=
  AlgebraicGeometry.Proj.Veronese.schemeIso grading degree positive

end ProjectiveSpaceTest
