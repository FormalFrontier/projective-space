/-
SPDX-License-Identifier: Apache-2.0
Authors: Andrew Yang (adapted gluing and chart arguments from Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic),
  Formal Frontier Agents
Copyright (c) 2024 Andrew Yang. All rights reserved.
Adapted material released under Apache 2.0, as in mathlib's LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

@[expose] public section

set_option warningAsError true

/-!
# Proj morphisms from geometrically covering global sections

The map from a graded ring to the global sections of a scheme defines a morphism to `Proj`
whenever the basic opens associated to its positive-degree homogeneous elements cover the
source scheme. Unlike `Proj.fromOfGlobalSections`, no ideal-theoretic equality in the global
sections ring is required.
-/

namespace AlgebraicGeometry.Proj

open CategoryTheory Limits HomogeneousLocalization TopologicalSpace

universe u

variable {σ : Type*} {A : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}}
variable (f : A →+* Γ(X, ⊤))

/-- The geometric cover by positive-degree homogeneous basic opens. -/
def openCoverOfGlobalSectionsOfIsOpenCover
    (hcover : IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
      X.basicOpen (f ir.2.1))) : X.OpenCover :=
  X.openCoverOfIsOpenCover _ hcover

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Construct `X ⟶ Proj 𝒜` from a geometric cover, without an irrelevant-ideal hypothesis. -/
noncomputable def fromOfGlobalSectionsOfIsOpenCover
    (hcover : IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
      X.basicOpen (f ir.2.1))) : X ⟶ Proj 𝒜 := by
  refine (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcover).glueMorphisms
    (fun ri ↦ toBasicOpenOfGlobalSections 𝒜 f rfl ri.2.2.1 ri.2.2.2 ≫ Scheme.Opens.ι _) ?_
  rintro x y
  let e : pullback ((openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcover).f x)
      ((openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcover).f y) ≅
      (X.basicOpen (f (x.snd.fst * y.snd.fst))) :=
    (isPullback_opens_inf _ _).isoPullback.symm ≪≫ X.isoOfEq (by simp)
  rw [← cancel_epi e.inv]
  trans toBasicOpenOfGlobalSections 𝒜 f rfl (Nat.add_pos_left x.2.2.1 y.1)
    (SetLike.mul_mem_graded x.2.2.2 y.2.2.2) ≫ (Scheme.Opens.ι _)
  · simpa [e, openCoverOfGlobalSectionsOfIsOpenCover, Scheme.isoOfEq_inv] using
      homOfLE_toBasicOpenOfGlobalSections_ι _ _ rfl rfl y.2.2.2
  · simpa [e, openCoverOfGlobalSectionsOfIsOpenCover, Scheme.isoOfEq_inv] using
      (homOfLE_toBasicOpenOfGlobalSections_ι _ _ (mul_comm _ _) (add_comm _ _) x.2.2.2).symm

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of a positive-degree homogeneous basic open is its basic open on `X`. -/
lemma fromOfGlobalSectionsOfIsOpenCover_preimage_basicOpen
    (hcover : IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
      X.basicOpen (f ir.2.1))) {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcover ⁻¹ᵁ basicOpen 𝒜 r =
      X.basicOpen (f r) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, x, rfl⟩ := (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcover).exists_eq x
    rw [← SetLike.mem_coe] at hx
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      ← Scheme.Hom.comp_apply, fromOfGlobalSectionsOfIsOpenCover,
      Scheme.Cover.ι_glueMorphisms] at hx
    simp only [openCoverOfGlobalSectionsOfIsOpenCover,
      toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv, Category.assoc,
      basicOpenIsoSpec_inv_ι] at hx
    simp only [Scheme.Hom.comp_base, Scheme.homOfLE_base, homOfLE_leOfHom, TopCat.hom_comp,
      ContinuousMap.comp_assoc, ContinuousMap.comp_apply, morphismRestrict_base,
      TopologicalSpace.Opens.carrier_eq_coe] at hx
    rw [← SetLike.mem_coe, ← Set.mem_preimage, ← TopologicalSpace.Opens.map_coe,
      Proj.awayι_preimage_basicOpen (𝒜 := 𝒜) i.2.2.2 i.2.2.1 hr hn,
      ← Set.mem_preimage, ← TopologicalSpace.Opens.map_coe, ← Function.Injective.mem_set_image
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) _))).isOpenEmbedding.injective,
      ← Scheme.Hom.comp_apply, basicOpenIsoSpecAway,
      IsOpenImmersion.isoOfRangeEq_hom_fac] at hx
    rw [← SetLike.mem_coe, ← Scheme.toSpecΓ_preimage_basicOpen,
      TopologicalSpace.Opens.map_coe, Set.mem_preimage]
    refine Set.mem_of_subset_of_mem (Set.image_subset_iff.mpr ?_) hx
    change PrimeSpectrum.basicOpen _ ≤ PrimeSpectrum.basicOpen _
    simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
      map_pow, PrimeSpectrum.basicOpen_le_basicOpen_iff, IsLocalization.mk'_mem_iff]
    exact Ideal.pow_mem_of_mem _ (Ideal.le_radical (Ideal.mem_span_singleton_self _)) _ i.2.2.1
  · intro x hx
    let I : (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcover).I₀ := ⟨n, r, hn, hr⟩
    obtain ⟨x, rfl⟩ : x ∈ ((openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcover).f I).opensRange := by
      simpa [openCoverOfGlobalSectionsOfIsOpenCover] using hx
    rw [← SetLike.mem_coe]
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, fromOfGlobalSectionsOfIsOpenCover]
    simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction to a target chart agrees with the native chart arrow. -/
lemma fromOfGlobalSectionsOfIsOpenCover_morphismRestrict
    (hcover : IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
      X.basicOpen (f ir.2.1))) {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    (fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcover) ∣_ (basicOpen 𝒜 r) =
      (Scheme.isoOfEq _
        (fromOfGlobalSectionsOfIsOpenCover_preimage_basicOpen 𝒜 f hcover hn hr)).hom ≫
        toBasicOpenOfGlobalSections 𝒜 f rfl hn hr := by
  rw [← Iso.inv_comp_eq, ← cancel_mono (basicOpen 𝒜 r).ι]
  simp only [Scheme.isoOfEq_inv, Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι_assoc, fromOfGlobalSectionsOfIsOpenCover]
  exact (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcover).ι_glueMorphisms _ _ ⟨_, _, hn, hr⟩

/-- The chart morphism as a map between the named basic-open schemes. -/
lemma fromOfGlobalSectionsOfIsOpenCover_resLE
    (hcover : IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
      X.basicOpen (f ir.2.1))) {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    (fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcover).resLE _ _
      (fromOfGlobalSectionsOfIsOpenCover_preimage_basicOpen 𝒜 f hcover hn hr).ge =
      toBasicOpenOfGlobalSections 𝒜 f rfl hn hr := by
  rw [← (Iso.inv_comp_eq _).mpr
    (fromOfGlobalSectionsOfIsOpenCover_morphismRestrict 𝒜 f hcover hn hr),
    ← Scheme.Hom.resLE_eq_morphismRestrict]
  simp [Scheme.isoOfEq_inv]

set_option backward.isDefEq.respectTransparency false in
/-- The geometric-cover morphism commutes with the degree-zero structure maps. -/
@[reassoc]
lemma fromOfGlobalSectionsOfIsOpenCover_toSpecZero
    (hcover : IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
      X.basicOpen (f ir.2.1))) :
    fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcover ≫ toSpecZero 𝒜 =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (f.comp (algebraMap _ _))) := by
  refine (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcover).hom_ext _ _ fun x ↦ ?_
  simp only [fromOfGlobalSectionsOfIsOpenCover, toBasicOpenOfGlobalSections,
    CommRingCat.ofHom_comp, Category.assoc, Scheme.Cover.ι_glueMorphisms_assoc,
    basicOpenIsoSpec_inv_ι_assoc, awayι_toSpecZero, Iso.inv_comp_eq]
  simp only [openCoverOfGlobalSectionsOfIsOpenCover,
    Scheme.openCoverOfIsOpenCover_f, Scheme.isoOfEq_hom_ι_assoc,
    ← morphismRestrict_ι_assoc]
  congr 1
  simp only [basicOpenIsoSpecAway, ← CommRingCat.ofHom_comp, ← Spec.map_comp,
    ← Iso.eq_inv_comp, IsOpenImmersion.isoOfRangeEq_inv_fac_assoc,
    ← HomogeneousLocalization.algebraMap_eq]
  congr 2
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq _ A,
    ← RingHom.comp_assoc, IsLocalization.map_comp, RingHom.comp_assoc]

/-- Under the stronger irrelevant-image-ideal condition this is mathlib's constructor. -/
lemma fromOfGlobalSectionsOfIsOpenCover_eq_fromOfGlobalSections
    (hcover : IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
      X.basicOpen (f ir.2.1)))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcover = fromOfGlobalSections 𝒜 f hf := by
  refine (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcover).hom_ext _ _ fun i ↦ ?_
  simp only [fromOfGlobalSectionsOfIsOpenCover, Scheme.Cover.ι_glueMorphisms]
  let j : (openCoverOfMapIrrelevantEqTop 𝒜 f hf).I₀ := ⟨i.1, i.2.1, i.2.2.1, i.2.2.2⟩
  change _ = (openCoverOfMapIrrelevantEqTop 𝒜 f hf).f j ≫
    fromOfGlobalSections 𝒜 f hf
  rw [fromOfGlobalSections, Scheme.Cover.ι_glueMorphisms]
  rfl

end AlgebraicGeometry.Proj
