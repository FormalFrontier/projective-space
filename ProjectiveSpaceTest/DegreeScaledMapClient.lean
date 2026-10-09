/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveSpace.DegreeScaledMap

@[expose] public section

set_option warningAsError true

/-! # Public-import client for positive-degree-scaled Proj maps -/

noncomputable section

namespace ProjectiveSpaceTest.DegreeScaledProjMap

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory HomogeneousLocalization

universe u v w

variable {A B : Type u} {σ : Type v} {τ : Type w}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ]
variable (f : A →+* B) (d : ℕ) (hd : 0 < d)
  (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))

example : (degreeScaledDomain 𝒜 ℬ f).toScheme ⟶ Proj 𝒜 :=
  degreeScaledMap 𝒜 ℬ f d hd hdeg

example : (degreeScaledDomain 𝒜 ℬ f : Set (Proj ℬ)) =
    (ProjectiveSpectrum.zeroLocus ℬ (imageIrrelevant 𝒜 f) : Set (Proj ℬ))ᶜ :=
  degreeScaledDomain_eq_zeroLocus_compl 𝒜 ℬ f

/-- Checks that the degree-scaled morphism restricts to the expected map on an
entire homogeneous affine chart. -/
theorem clientWholeChart (i : Σ n : PNat, 𝒜 n) :
    (basicOpenIsoSpec ℬ (f (i.2 : A))
      (hdeg i.1 (i.2 : A) i.2.2) (Nat.mul_pos hd i.1.2)).inv ≫
        (chartCover 𝒜 ℬ f).f i ≫ degreeScaledMap 𝒜 ℬ f d hd hdeg =
      Spec.map (CommRingCat.ofHom (Away.mapDegreeMul 𝒜 ℬ f d hdeg (i.2 : A))) ≫
        awayι 𝒜 (i.2 : A) i.2.2 i.1.2 :=
  degreeScaledMap_chartSpec 𝒜 ℬ f d hd hdeg i

example (i : Σ n : PNat, 𝒜 n) :
    (basicOpenIsoSpec ℬ (f (i.2 : A))
      (hdeg i.1 (i.2 : A) i.2.2) (Nat.mul_pos hd i.1.2)).inv ≫
        (chartCover 𝒜 ℬ f).f i ≫ degreeScaledMap 𝒜 ℬ f d hd hdeg =
      Spec.map (CommRingCat.ofHom (Away.mapDegreeMul 𝒜 ℬ f d hdeg (i.2 : A))) ≫
        awayι 𝒜 (i.2 : A) i.2.2 i.1.2 :=
  clientWholeChart 𝒜 ℬ f d hd hdeg i

example (i : Σ n : PNat, 𝒜 n) (a : A) (ha : a ∈ 𝒜 i.1)
    (k : ℕ) (b : A) (hb : b ∈ 𝒜 (k • i.1)) :
    Away.mapDegreeMul 𝒜 ℬ f d hdeg a (Away.mk 𝒜 ha k b hb) =
      Away.mk ℬ (hdeg i.1 a ha) k (f b)
        (by simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          hdeg (k • i.1) b hb) :=
  Away.mapDegreeMul_mk 𝒜 ℬ f d hdeg a ha k b hb

example {n : ℕ} (r : A) (hr : r ∈ 𝒜 n) (hn : 0 < n) :
    degreeScaledMap 𝒜 ℬ f d hd hdeg ⁻¹ᵁ basicOpen 𝒜 r =
      (degreeScaledDomain 𝒜 ℬ f).ι ⁻¹ᵁ basicOpen ℬ (f r) :=
  degreeScaledMap_preimage_basicOpen 𝒜 ℬ f d hd hdeg r hr hn

example : degreeScaledMap 𝒜 ℬ f d hd hdeg ≫ toSpecZero 𝒜 =
    (degreeScaledDomain 𝒜 ℬ f).ι ≫ toSpecZero ℬ ≫
      Spec.map (CommRingCat.ofHom (degreeZeroRingHom 𝒜 ℬ f d hdeg)) :=
  degreeScaledMap_toSpecZero 𝒜 ℬ f d hd hdeg

example (g : (degreeScaledDomain 𝒜 ℬ f).toScheme ⟶ Proj 𝒜)
    (hg : ∀ i : Σ n : PNat, 𝒜 n,
      (chartCover 𝒜 ℬ f).f i ≫ g = degreeScaledChartMap 𝒜 ℬ f d hd hdeg i) :
    g = degreeScaledMap 𝒜 ℬ f d hd hdeg :=
  degreeScaledMap_unique 𝒜 ℬ f d hd hdeg g hg

end ProjectiveSpaceTest.DegreeScaledProjMap
