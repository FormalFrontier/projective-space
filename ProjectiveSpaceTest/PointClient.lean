/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveSpace.HomogeneousCoordinatePoint
public import ProjectiveSpace.GradedProjIso

/-!
# Ordinary-import point and transport client

Checks the public cone-line evaluation map, its definitional kernel, and the
universe-polymorphic graded transport theorem without private implementation imports.
-/

namespace ProjectiveSpaceTest

universe u v

variable {k : Type u} [Field k] {ι : Type v}

private theorem coneLine_on_coordinate (a : ι → k) (i : ι) :
    ProjectiveSpace.homogeneousCoordinateMap a (MvPolynomial.X i) =
      Polynomial.C (a i) * Polynomial.X := by
  simp

private theorem coneLine_kernel_reduces (a : ι → k) :
    ProjectiveSpace.homogeneousCoordinateIdeal a =
      RingHom.ker (ProjectiveSpace.homogeneousCoordinateMap a).toRingHom := by
  rfl

private noncomputable def storedConeLineMap (a : ι → k) :
    MvPolynomial ι k →ₐ[k] Polynomial k :=
  ProjectiveSpace.homogeneousCoordinateMap a

variable {A : Type u} {B : Type v} {σ : Type*} {τ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

private theorem graded_map_irrelevant (f : 𝒜 →+*ᵍ ℬ) :
    (HomogeneousIdeal.irrelevant 𝒜).map f ≤ HomogeneousIdeal.irrelevant ℬ :=
  ProjectiveSpace.map_irrelevant_le f

end ProjectiveSpaceTest
