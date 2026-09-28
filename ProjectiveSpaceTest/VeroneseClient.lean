/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.Veronese

@[expose] public section

/-! # Ordinary-import client for positive Veronese charts and Proj isomorphisms -/

set_option warningAsError true

noncomputable section

namespace ProjectiveSpaceTest.Veronese

open AlgebraicGeometry AlgebraicGeometry.Proj AlgebraicGeometry.Proj.Veronese GradedRing.Veronese
  HomogeneousLocalization CategoryTheory

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

example (n : ℕ) (hn : 0 < n) (j : ℕ) (f : VeroneseRing 𝒮 n)
    (hf : f ∈ component 𝒮 n j) :
    Away (component 𝒮 n) f ≃+* Away 𝒮 (inclusion 𝒮 n f) :=
  chartEquiv 𝒮 n hn j f hf

example (n : ℕ) (hn : 0 < n) :
    Away (component 𝒮 n) 0 ≃+* Away 𝒮 (inclusion 𝒮 n 0) :=
  chartEquiv 𝒮 n hn 1 0 (by exact zero_mem (component 𝒮 n 1))

example (n : ℕ) (hn : 0 < n) :
    Proj 𝒮 ≅ Proj (component 𝒮 n) := schemeIso 𝒮 n hn

example : Proj 𝒮 ≅ Proj (component 𝒮 1) :=
  schemeIso 𝒮 1 (by decide)

example (n : ℕ) (hn : 0 < n) (p : Proj 𝒮)
    (a : VeroneseRing 𝒮 n) :
    a ∈ ((schemeIso 𝒮 n hn).hom p).asHomogeneousIdeal.toIdeal ↔
      inclusion 𝒮 n a ∈ p.asHomogeneousIdeal.toIdeal := by
  simpa using forward_mem_pointIdeal 𝒮 n hn p a

example (n : ℕ) (hn : 0 < n) (j : ℕ) (hj : 0 < j)
    (f : VeroneseRing 𝒮 n) (hf : f ∈ component 𝒮 n j) :
    (schemeIso 𝒮 n hn).hom ⁻¹ᵁ basicOpen (component 𝒮 n) f =
      basicOpen 𝒮 (inclusion 𝒮 n f) := by
  simpa using forward_preimage_basicOpen 𝒮 n hn j hj f hf

example (n : ℕ) (hn : 0 < n) :
    (schemeIso 𝒮 n hn).hom ≫ toSpecZero (component 𝒮 n) =
      toSpecZero 𝒮 ≫
        Spec.map (CommRingCat.ofHom (zeroRingEquiv 𝒮 n hn).toRingHom) :=
  forward_toSpecZero 𝒮 n hn

end ProjectiveSpaceTest.Veronese
