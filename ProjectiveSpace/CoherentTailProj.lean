/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveSpace.GradedProjIso
public import GradedRings.CoherentTailVeronese
public import ProjectiveSpace.Veronese

@[expose] public section

/-!
# Proj of coherently equivalent graded tails

A coherent equivalence of degree zero and all sufficiently high homogeneous
pieces induces an isomorphism of whole projective schemes, compatible with
their maps to the spectra of their degree-zero rings.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GradedRing.Veronese.CoherentTail

open CategoryTheory AlgebraicGeometry GradedRing.Veronese HomogeneousIdeal

universe u v w

variable {R S : Type u} [CommRing R] [CommRing S]
  {σ : Type v} {τ : Type w} [SetLike σ R] [AddSubgroupClass σ R]
  [SetLike τ S] [AddSubgroupClass τ S]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

namespace TailEquiv

variable (E : TailEquiv 𝒜 ℬ N) (n : ℕ) (hNn : N ≤ n) (hn : 0 < n)

/-- Isomorphism of the selected Proj schemes, including their structure sheaves. -/
def selectedProjIso : AlgebraicGeometry.Proj (component 𝒜 n) ≅
    AlgebraicGeometry.Proj (component ℬ n) :=
  ProjectiveSpace.projIsoOfInverseGradedRingHom
    (E.selectedGradedHomSymm n hNn) (E.selectedGradedHom n hNn)
    (E.selectedGradedHomSymm_comp n hNn) (E.selectedGradedHom_comp_symm n hNn)

/-- The entire projective schemes of coherent tails are isomorphic. -/
def projIso : AlgebraicGeometry.Proj 𝒜 ≅ AlgebraicGeometry.Proj ℬ :=
  (AlgebraicGeometry.Proj.Veronese.schemeIso 𝒜 n hn).trans
    ((E.selectedProjIso n hNn).trans
      (AlgebraicGeometry.Proj.Veronese.schemeIso ℬ n hn).symm)

/-- The chosen whole-scheme isomorphism is the composite of published Veronese
arrows and the native Proj map of the inverse selected graded map. -/
theorem projIso_hom : (E.projIso n hNn hn).hom =
    (AlgebraicGeometry.Proj.Veronese.schemeIso 𝒜 n hn).hom ≫
      AlgebraicGeometry.Proj.map (E.selectedGradedHomSymm n hNn)
        (ProjectiveSpace.irrelevant_le_map_of_comp_eq_id
          (E.selectedGradedHomSymm n hNn) (E.selectedGradedHom n hNn)
          (E.selectedGradedHomSymm_comp n hNn)) ≫
        (AlgebraicGeometry.Proj.Veronese.schemeIso ℬ n hn).inv := by
  change (AlgebraicGeometry.Proj.Veronese.schemeIso 𝒜 n hn).hom ≫
    (E.selectedProjIso n hNn).hom ≫
    (AlgebraicGeometry.Proj.Veronese.schemeIso ℬ n hn).inv = _
  rfl

theorem selected_zero_spec :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom E.zero.toRingHom) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (zeroRingEquiv 𝒜 n hn).toRingHom) =
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (zeroRingEquiv ℬ n hn).toRingHom) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (GradedRingHom.gradedZeroRingHom
          (E.selectedGradedHom n hNn))) := by
  simp only [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← E.selected_zero n hNn hn]

theorem projIso_comp_selected_inv :
    (E.projIso n hNn hn).hom ≫
      (AlgebraicGeometry.Proj.Veronese.schemeIso ℬ n hn).hom ≫
      (E.selectedProjIso n hNn).inv =
        (AlgebraicGeometry.Proj.Veronese.schemeIso 𝒜 n hn).hom := by
  rw [E.projIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change (AlgebraicGeometry.Proj.Veronese.schemeIso 𝒜 n hn).hom ≫
    (E.selectedProjIso n hNn).hom ≫ (E.selectedProjIso n hNn).inv = _
  simp only [Iso.hom_inv_id, Category.comp_id]

/-- The tail Proj isomorphism commutes with the actual degree-zero coefficient map. -/
theorem projIso_toSpecZero :
    (E.projIso n hNn hn).hom ≫ AlgebraicGeometry.Proj.toSpecZero ℬ ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom E.zero.toRingHom) =
        AlgebraicGeometry.Proj.toSpecZero 𝒜 := by
  let outerA := AlgebraicGeometry.Proj.Veronese.schemeIso 𝒜 n hn
  let outerB := AlgebraicGeometry.Proj.Veronese.schemeIso ℬ n hn
  let middle := E.selectedProjIso n hNn
  let zeroA := zeroRingEquiv 𝒜 n hn
  let zeroB := zeroRingEquiv ℬ n hn
  let selectedZero := GradedRingHom.gradedZeroRingHom (E.selectedGradedHom n hNn)
  have hA : outerA.hom ≫ AlgebraicGeometry.Proj.toSpecZero (component 𝒜 n) =
      AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom zeroA.toRingHom) :=
    AlgebraicGeometry.Proj.Veronese.forward_toSpecZero 𝒜 n hn
  have hB : outerB.hom ≫ AlgebraicGeometry.Proj.toSpecZero (component ℬ n) =
      AlgebraicGeometry.Proj.toSpecZero ℬ ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom zeroB.toRingHom) :=
    AlgebraicGeometry.Proj.Veronese.forward_toSpecZero ℬ n hn
  have hMiddle : middle.inv ≫ AlgebraicGeometry.Proj.toSpecZero (component 𝒜 n) =
      AlgebraicGeometry.Proj.toSpecZero (component ℬ n) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom selectedZero) :=
    AlgebraicGeometry.Proj.map_toSpecZero
      (E.selectedGradedHom n hNn)
      (ProjectiveSpace.irrelevant_le_map_of_comp_eq_id
        (E.selectedGradedHom n hNn) (E.selectedGradedHomSymm n hNn)
        (E.selectedGradedHom_comp_symm n hNn))
  have hZero : AlgebraicGeometry.Spec.map (CommRingCat.ofHom E.zero.toRingHom) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom zeroA.toRingHom) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom zeroB.toRingHom) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom selectedZero) :=
    E.selected_zero_spec n hNn hn
  have hIso : IsIso (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom zeroA.toRingHom)) := by
    change IsIso (AlgebraicGeometry.Spec.map zeroA.toCommRingCatIso.hom)
    infer_instance
  apply (cancel_mono (AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom zeroA.toRingHom))).mp
  calc
    _ = (E.projIso n hNn hn).hom ≫
        (AlgebraicGeometry.Proj.toSpecZero ℬ ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom zeroB.toRingHom)) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom selectedZero) := by
      simp only [Category.assoc, hZero]
    _ = (E.projIso n hNn hn).hom ≫
        (outerB.hom ≫ AlgebraicGeometry.Proj.toSpecZero (component ℬ n)) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom selectedZero) := by rw [hB]
    _ = (E.projIso n hNn hn).hom ≫ outerB.hom ≫
        (AlgebraicGeometry.Proj.toSpecZero (component ℬ n) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom selectedZero)) := by
      simp only [Category.assoc]
    _ = (E.projIso n hNn hn).hom ≫ outerB.hom ≫
        (middle.inv ≫ AlgebraicGeometry.Proj.toSpecZero (component 𝒜 n)) := by
      rw [hMiddle]
    _ = outerA.hom ≫ AlgebraicGeometry.Proj.toSpecZero (component 𝒜 n) := by
      simpa only [Category.assoc] using
        congrArg (fun φ => φ ≫ AlgebraicGeometry.Proj.toSpecZero (component 𝒜 n))
          (E.projIso_comp_selected_inv n hNn hn)
    _ = AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom zeroA.toRingHom) := hA

/-- The inverse whole-scheme map obeys the companion coefficient triangle. -/
theorem projIso_inv_toSpecZero :
    (E.projIso n hNn hn).inv ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜 =
      AlgebraicGeometry.Proj.toSpecZero ℬ ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom E.zero.toRingHom) := by
  calc
    _ = (E.projIso n hNn hn).inv ≫
        ((E.projIso n hNn hn).hom ≫ AlgebraicGeometry.Proj.toSpecZero ℬ ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom E.zero.toRingHom)) := by
      rw [E.projIso_toSpecZero]
    _ = _ := by simp only [Iso.inv_hom_id_assoc]

end TailEquiv
end GradedRing.Veronese.CoherentTail
