/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original client contribution: Formal Frontier Hive Task hive-request-b988d896159b1606f206dbd80748f923ee680d6f
  (UID 66dd1fe1-34c7-4874-b17b-5400ac0aa165, formalization-worker-a)
-/
module

public import ProjectiveSpace.GlobalSections

public section

set_option warningAsError true

/-! # Public-import clients for geometric global sections of Proj -/

namespace ProjectiveSpaceTest.ProjGlobalSections

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory TopologicalSpace

universe u

variable {σ : Type*} {A : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}}
variable (f : A →+* Γ(X, ⊤))
variable (hcover : IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
  X.basicOpen (f ir.2.1)))

noncomputable def clientArrow : X ⟶ Proj 𝒜 :=
  fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcover

theorem clientPreimage {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    clientArrow 𝒜 f hcover ⁻¹ᵁ basicOpen 𝒜 r = X.basicOpen (f r) :=
  fromOfGlobalSectionsOfIsOpenCover_preimage_basicOpen 𝒜 f hcover hn hr

theorem clientChart {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    (clientArrow 𝒜 f hcover).resLE _ _ (clientPreimage 𝒜 f hcover hn hr).ge =
      toBasicOpenOfGlobalSections 𝒜 f rfl hn hr :=
  fromOfGlobalSectionsOfIsOpenCover_resLE 𝒜 f hcover hn hr

theorem clientMorphismRestrict {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    (clientArrow 𝒜 f hcover) ∣_ (basicOpen 𝒜 r) =
      (Scheme.isoOfEq _ (clientPreimage 𝒜 f hcover hn hr)).hom ≫
        toBasicOpenOfGlobalSections 𝒜 f rfl hn hr :=
  fromOfGlobalSectionsOfIsOpenCover_morphismRestrict 𝒜 f hcover hn hr

theorem clientBase :
    clientArrow 𝒜 f hcover ≫ toSpecZero 𝒜 =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (f.comp (algebraMap _ _))) :=
  fromOfGlobalSectionsOfIsOpenCover_toSpecZero 𝒜 f hcover

theorem clientRecovery
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    clientArrow 𝒜 f hcover = fromOfGlobalSections 𝒜 f hf :=
  fromOfGlobalSectionsOfIsOpenCover_eq_fromOfGlobalSections 𝒜 f hcover hf

theorem clientStrongRecovery
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    ∃ hcover : IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
        X.basicOpen (f ir.2.1)),
      fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcover = fromOfGlobalSections 𝒜 f hf := by
  have cover : IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
      X.basicOpen (f ir.2.1)) := by
    have ranges := (openCoverOfMapIrrelevantEqTop 𝒜 f hf).isOpenCover_opensRange
    change IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
      (X.basicOpen (f ir.2.1)).ι.opensRange) at ranges
    simpa only [Scheme.Opens.opensRange_ι] using ranges
  exact ⟨cover, fromOfGlobalSectionsOfIsOpenCover_eq_fromOfGlobalSections 𝒜 f cover hf⟩

end ProjectiveSpaceTest.ProjGlobalSections
