/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original example proofs: Worker B Task hive-request-00a7647d0c694c4eaf4654c0548c0ab129c53130
UID be7b6056-8d20-41e1-b1be-2d825db69e8b
Reader selection and header: Worker A Task hive-request-a11cc160eed1b0c777c9d375b66b4c5b41de124b
UID 01de320f-d2fb-47c5-91b1-98d7a4984f70
Imported project mathematics: Atlas and Formal Frontier contributors (AI-assisted)
-/
module

import ProjectiveSpace.BasicOpenBasis
import ProjectiveSpace.ProjectiveNullstellensatz
import ProjectiveSpace.HomogeneousDimension
import ProjectiveSpace.Irreducible

open scoped ProjectiveSpace

namespace ProjectiveSpaceReader.GeometryExamples

universe u v

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem positive_basicOpen_is_in_basis
    (degree : PNat) (f : 𝒜 (degree : ℕ)) :
    (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) :
      Set (AlgebraicGeometry.Proj 𝒜)) ∈
      AlgebraicGeometry.Proj.positiveBasicOpens 𝒜 := by
  exact ⟨⟨degree, f⟩, rfl⟩

private theorem positive_basicOpen_basis :
    TopologicalSpace.IsTopologicalBasis
      (AlgebraicGeometry.Proj.positiveBasicOpens 𝒜) :=
  AlgebraicGeometry.Proj.isTopologicalBasis_positiveBasicOpens 𝒜

private theorem radical_implies_projective_vanishing
    (I : HomogeneousIdeal 𝒜) {f : A} {degree : ℕ}
    (hf : f ∈ 𝒜 degree) (hdegree : 0 < degree)
    (h : f ∈ I.toIdeal.radical) :
    f ∈ ProjectiveSpectrum.vanishingIdeal
      (ProjectiveSpectrum.zeroLocus 𝒜 I) :=
  (ProjectiveSpectrum.mem_vanishingIdeal_zeroLocus_iff_mem_radical
    𝒜 I hf hdegree).2 h

variable {R : Type u} [CommSemiring R] [StrongRankCondition R]

private theorem finrank_for_finite_coordinates
    (ι : Type v) [Fintype ι] (degree : ℕ) :
    Module.finrank R (MvPolynomial.homogeneousSubmodule ι R degree) =
      (Fintype.card ι).multichoose degree :=
  ProjectiveSpace.finrank_homogeneousSubmodule R ι degree

variable {S : Type u} [CommRing S] [IsDomain S]
variable {ι : Type v} [Nonempty ι]

private theorem polynomial_proj_is_irreducible :
    IrreducibleSpace
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule ι S)) := by
  infer_instance

#print axioms positive_basicOpen_is_in_basis
#print axioms positive_basicOpen_basis
#print axioms radical_implies_projective_vanishing
#print axioms finrank_for_finite_coordinates
#print axioms polynomial_proj_is_irreducible

end ProjectiveSpaceReader.GeometryExamples
