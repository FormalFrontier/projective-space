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

import ProjectiveSpace.GradedProjIso

namespace ProjectiveSpaceReader.TransportExamples

universe uA uB uσ uτ

variable {A : Type uA} {B : Type uB}
variable {σ : Type uσ} {τ : Type uτ}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

private theorem transport_point_roundtrip
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ)
    (hgf : g.comp f = GradedRingHom.id 𝒜)
    (p : ProjectiveSpectrum ℬ) :
    (ProjectiveSpace.projectiveSpectrumEquivOfInverseGradedRingHom
      f g hfg hgf).symm
      (ProjectiveSpace.projectiveSpectrumEquivOfInverseGradedRingHom
        f g hfg hgf p) = p :=
  (ProjectiveSpace.projectiveSpectrumEquivOfInverseGradedRingHom
    f g hfg hgf).left_inv p

private theorem transported_closed_point_underlying
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ)
    (hgf : g.comp f = GradedRingHom.id 𝒜)
    (p : closedPoints (AlgebraicGeometry.Proj ℬ)) :
    (ProjectiveSpace.projClosedPointsEquivOfInverseGradedRingHom
      f g hfg hgf p).1 =
      AlgebraicGeometry.ProjectiveSpectrum.comapFun f
        (ProjectiveSpace.irrelevant_le_map_of_comp_eq_id f g hfg) p.1 := by
  simpa only using
    ProjectiveSpace.projClosedPointsEquivOfInverseGradedRingHom_apply_coe
      f g hfg hgf p

#print axioms transport_point_roundtrip
#print axioms transported_closed_point_underlying

end ProjectiveSpaceReader.TransportExamples
