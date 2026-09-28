/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Hive Task hive-request-2ca332a8ced6485f6ca92c839afc566e562ec00c
  (UID 12e28acb-0999-4a80-b88f-3a412dbf506b, worker-a)
-/
module

public import ProjectiveSpace.DegreeScaledMapPoint

@[expose] public section

set_option warningAsError true

/-! # Public-import client for ordinary primes of degree-scaled Proj maps -/

noncomputable section

namespace ProjectiveSpaceTest.DegreeScaledProjMapPoint

open AlgebraicGeometry AlgebraicGeometry.Proj

universe u v w

variable {A B : Type u} {σ : Type v} {τ : Type w}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ]
variable (f : A →+* B) (d : ℕ) (hd : 0 < d)
  (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))

example (p : (degreeScaledDomain 𝒜 ℬ f).toScheme) :
    ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal =
      Ideal.comap f (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal) :=
  degreeScaledMap_pointIdeal 𝒜 ℬ f d hd hdeg p

example (p : (degreeScaledDomain 𝒜 ℬ f).toScheme) (a : A) :
    a ∈ ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal ↔
      f a ∈ (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal) :=
  degreeScaledMap_mem_pointIdeal 𝒜 ℬ f d hd hdeg p a

example (p : (degreeScaledDomain 𝒜 ℬ f).toScheme) (a : 𝒜 0) :
    (a : A) ∈ ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal ↔
      f (a : A) ∈ (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal) :=
  degreeScaledMap_mem_pointIdeal 𝒜 ℬ f d hd hdeg p (a : A)

end ProjectiveSpaceTest.DegreeScaledProjMapPoint
