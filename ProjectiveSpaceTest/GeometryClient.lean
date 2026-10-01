/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveSpace.BasicOpenBasis
public import ProjectiveSpace.ProjectiveNullstellensatz
public import ProjectiveSpace.Irreducible
public import ProjectiveSpace.HomogeneousDimension

/-!
# Ordinary-import basic-open, radical, and dimension client

Exercises independent coefficient/index universes, positive degree, and the
semiring strong-rank-condition boundary of the public library.
-/

open scoped ProjectiveSpace

namespace ProjectiveSpaceTest

universe u v

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem basicOpen_basis :
    TopologicalSpace.IsTopologicalBasis (AlgebraicGeometry.Proj.positiveBasicOpens 𝒜) :=
  AlgebraicGeometry.Proj.isTopologicalBasis_positiveBasicOpens 𝒜

private theorem positive_degree_radical (I : HomogeneousIdeal 𝒜)
    {f : A} {n : ℕ} (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    f ∈ ProjectiveSpectrum.vanishingIdeal (ProjectiveSpectrum.zeroLocus 𝒜 I) ↔
      f ∈ I.toIdeal.radical :=
  ProjectiveSpectrum.mem_vanishingIdeal_zeroLocus_iff_mem_radical 𝒜 I hf hn

variable {R : Type u} [CommSemiring R] [StrongRankCondition R]

private theorem fin_dimension (n d : ℕ) :
    Module.finrank R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) =
      (n + d).choose d :=
  ProjectiveSpace.finrank_homogeneousSubmodule_fin R n d

variable {S : Type u} [CommRing S] [IsDomain S] {ι : Type v} [Nonempty ι]

private theorem irreducible_polynomial_proj :
    IrreducibleSpace
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule ι S)) := by
  infer_instance

end ProjectiveSpaceTest
