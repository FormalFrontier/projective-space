/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveSpace.UnitScaling

public section

set_option warningAsError true

/-! # Public-import clients for degree-weighted scaling of Proj morphisms -/

namespace ProjectiveSpaceTest.ProjUnitScaling

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory
  HomogeneousLocalization TopologicalSpace

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}}
variable (f g : A →+* Γ(X, ⊤)) (unit : Γ(X, ⊤)ˣ)
variable (hscale : ∀ d (a : A), a ∈ 𝒜 d →
  g a = (unit : Γ(X, ⊤)) ^ d * f a)

include hscale

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
theorem clientSameOpen {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) :
    X.basicOpen (g t) = X.basicOpen (f t) :=
  basicOpen_eq_of_unitScaling 𝒜 f g unit hscale ht

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
theorem clientCover (hcover : IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
    X.basicOpen (f ir.2.1))) :
    IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
      X.basicOpen (g ir.2.1)) :=
  isOpenCover_of_unitScaling 𝒜 f g unit hscale hcover

theorem clientChart {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    toBasicOpenOfGlobalSections 𝒜 f rfl hd ht =
      (X.isoOfEq (clientSameOpen 𝒜 f g unit hscale ht).symm).hom ≫
        toBasicOpenOfGlobalSections 𝒜 g rfl hd ht :=
  toBasicOpenOfGlobalSections_eq_of_unitScaling 𝒜 f g unit hscale hd ht

theorem clientWholeArrow
    (hcoverf : IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
      X.basicOpen (f ir.2.1)))
    (hcoverg : IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
      X.basicOpen (g ir.2.1))) :
    fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf =
      fromOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg :=
  fromOfGlobalSectionsOfIsOpenCover_eq_of_unitScaling 𝒜 f g unit hscale hcoverf hcoverg

theorem clientOneCover
    (hcover : IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
      X.basicOpen (f ir.2.1))) :
    fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcover =
      fromOfGlobalSectionsOfIsOpenCover 𝒜 g
        (clientCover 𝒜 f g unit hscale hcover) :=
  fromOfGlobalSectionsOfIsOpenCover_unitScaling 𝒜 f g unit hscale hcover

end ProjectiveSpaceTest.ProjUnitScaling
