/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Contributors: Atlas and Formal Frontier contributors (AI-assisted)
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.Topology.JacobsonSpace

/-!
# Transporting `Proj` across graded ring equivalences

Inverse degree-preserving ring maps induce inverse scheme morphisms on `Proj`.
This file packages that construction, its underlying projective-spectrum point
equivalence, and the resulting equivalence on closed points.

The scheme-level construction follows the current monomorphic universe of
`AlgebraicGeometry.Proj.map`; the two graded rings therefore live in one
universe.
-/

set_option warningAsError true

@[expose] public section

open CategoryTheory HomogeneousIdeal
open AlgebraicGeometry

namespace ProjectiveSpace

universe u uA uB uσ uτ

section UniversePolymorphic

variable {A : Type uA} {B : Type uB} {σ : Type uσ} {τ : Type uτ}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A degree-preserving ring map sends the irrelevant ideal into the irrelevant ideal. -/
theorem map_irrelevant_le (f : 𝒜 →+*ᵍ ℬ) : 𝒜₊.map f ≤ ℬ₊ := by
  rw [HomogeneousIdeal.map_le_iff_le_comap]
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  exact HomogeneousIdeal.mem_irrelevant_of_mem ℬ hi (f.map_mem hx)

/-- One side of an inverse pair gives the irrelevant-ideal hypothesis needed
for contravariant functoriality of `Proj`. -/
theorem irrelevant_le_map_of_comp_eq_id (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ) : ℬ₊ ≤ 𝒜₊.map f := by
  have h := HomogeneousIdeal.map_mono f (map_irrelevant_le g)
  simpa only [← HomogeneousIdeal.map_comp, hfg, HomogeneousIdeal.map_id] using h

/-- Inverse degree-preserving ring maps induce an equivalence of
projective-spectrum points. Unlike the scheme-level construction, this uses
only ideal comaps and permits the two graded rings to live in independent
universes. -/
noncomputable def projectiveSpectrumEquivOfInverseGradedRingHom
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ)
    (hgf : g.comp f = GradedRingHom.id 𝒜) :
    ProjectiveSpectrum ℬ ≃ ProjectiveSpectrum 𝒜 where
  toFun := ProjectiveSpectrum.comapFun f
    (irrelevant_le_map_of_comp_eq_id f g hfg)
  invFun := ProjectiveSpectrum.comapFun g
    (irrelevant_le_map_of_comp_eq_id g f hgf)
  left_inv p := by
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.toIdeal_injective
    change (p.1.toIdeal.comap f.toRingHom).comap g.toRingHom = p.1.toIdeal
    rw [Ideal.comap_comap]
    change p.1.toIdeal.comap (f.comp g).toRingHom = p.1.toIdeal
    rw [hfg]
    exact Ideal.comap_id p.1.toIdeal
  right_inv p := by
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.toIdeal_injective
    change (p.1.toIdeal.comap g.toRingHom).comap f.toRingHom = p.1.toIdeal
    rw [Ideal.comap_comap]
    change p.1.toIdeal.comap (g.comp f).toRingHom = p.1.toIdeal
    rw [hgf]
    exact Ideal.comap_id p.1.toIdeal

@[simp]
theorem projectiveSpectrumEquivOfInverseGradedRingHom_apply
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ)
    (hgf : g.comp f = GradedRingHom.id 𝒜) (p : ProjectiveSpectrum ℬ) :
    projectiveSpectrumEquivOfInverseGradedRingHom f g hfg hgf p =
      ProjectiveSpectrum.comapFun f
        (irrelevant_le_map_of_comp_eq_id f g hfg) p :=
  rfl

/-- Inverse degree-preserving ring maps induce a homeomorphism of
projective-spectrum points, without a common-universe requirement. -/
noncomputable def projectiveSpectrumHomeomorphOfInverseGradedRingHom
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ)
    (hgf : g.comp f = GradedRingHom.id 𝒜) :
    ProjectiveSpectrum ℬ ≃ₜ ProjectiveSpectrum 𝒜 where
  toEquiv := projectiveSpectrumEquivOfInverseGradedRingHom f g hfg hgf
  continuous_toFun :=
    (ProjectiveSpectrum.comap f
      (irrelevant_le_map_of_comp_eq_id f g hfg)).continuous
  continuous_invFun :=
    (ProjectiveSpectrum.comap g
      (irrelevant_le_map_of_comp_eq_id g f hgf)).continuous

/-- Inverse degree-preserving ring maps induce an equivalence on closed points
of `Proj`, even when the two graded rings live in independent universes. -/
noncomputable def projClosedPointsEquivOfInverseGradedRingHom
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ)
    (hgf : g.comp f = GradedRingHom.id 𝒜) :
    closedPoints (AlgebraicGeometry.Proj ℬ) ≃
      closedPoints (AlgebraicGeometry.Proj 𝒜) :=
  (projectiveSpectrumHomeomorphOfInverseGradedRingHom f g hfg hgf).toEquiv.subtypeEquiv
    fun x ↦ by
      change IsClosed ({x} : Set (ProjectiveSpectrum ℬ)) ↔
        IsClosed ({projectiveSpectrumHomeomorphOfInverseGradedRingHom f g hfg hgf x} :
          Set (ProjectiveSpectrum 𝒜))
      simpa only [Set.image_singleton] using
        ((projectiveSpectrumHomeomorphOfInverseGradedRingHom f g hfg hgf).isClosed_image
          (s := {x})).symm

@[simp]
theorem projClosedPointsEquivOfInverseGradedRingHom_apply_coe
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ)
    (hgf : g.comp f = GradedRingHom.id 𝒜)
    (p : closedPoints (AlgebraicGeometry.Proj ℬ)) :
    (projClosedPointsEquivOfInverseGradedRingHom f g hfg hgf p).1 =
      ProjectiveSpectrum.comapFun f
        (irrelevant_le_map_of_comp_eq_id f g hfg) p.1 :=
  rfl

end UniversePolymorphic

section UniverseMonomorphic

variable {A B σ τ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Inverse degree-preserving ring maps induce an isomorphism on `Proj`. -/
noncomputable def projIsoOfInverseGradedRingHom
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ)
    (hgf : g.comp f = GradedRingHom.id 𝒜) :
    AlgebraicGeometry.Proj ℬ ≅ AlgebraicGeometry.Proj 𝒜 where
  hom := AlgebraicGeometry.Proj.map f
    (irrelevant_le_map_of_comp_eq_id f g hfg)
  inv := AlgebraicGeometry.Proj.map g
    (irrelevant_le_map_of_comp_eq_id g f hgf)
  hom_inv_id := by
    rw [← AlgebraicGeometry.Proj.map_comp]
    simpa only [hfg] using (AlgebraicGeometry.Proj.map_id (𝒜 := ℬ))
  inv_hom_id := by
    rw [← AlgebraicGeometry.Proj.map_comp]
    simpa only [hgf] using (AlgebraicGeometry.Proj.map_id (𝒜 := 𝒜))

/-- A scheme isomorphism induces an equivalence on closed points. -/
noncomputable def closedPointsEquivOfIso
    {X Y : Scheme.{u}} (e : X ≅ Y) : closedPoints X ≃ closedPoints Y :=
  (Scheme.homeoOfIso e).toEquiv.subtypeEquiv fun x ↦ by
    rw [mem_closedPoints_iff, mem_closedPoints_iff]
    change IsClosed {x} ↔ IsClosed {(Scheme.homeoOfIso e) x}
    simpa only [Set.image_singleton] using
      ((Scheme.homeoOfIso e).isClosed_image (s := {x})).symm

@[simp]
theorem closedPointsEquivOfIso_apply_coe {X Y : Scheme.{u}} (e : X ≅ Y)
    (x : closedPoints X) :
    ((closedPointsEquivOfIso e x : closedPoints Y) : Y) = e.hom x :=
  rfl

end UniverseMonomorphic


end ProjectiveSpace
