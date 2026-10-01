/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Irreducibility of polynomial projective space

Polynomial projective space over an integral domain is irreducible when its
coordinate type is nonempty. The homogeneous zero ideal is a relevant prime
and its closure is the entire projective spectrum.
-/

@[expose] public section

noncomputable section

scoped[ProjectiveSpace] attribute [instance] MvPolynomial.gradedAlgebra

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R] [IsDomain R]
variable (ι : Type v) [Nonempty ι]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

private noncomputable def polynomialProjGenericPoint :
    ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := by
    simpa only [HomogeneousIdeal.toIdeal_bot] using
      (Ideal.isPrime_bot : (⊥ : Ideal (MvPolynomial ι R)).IsPrime)
  not_irrelevant_le := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hX : MvPolynomial.X i ∈ HomogeneousIdeal.irrelevant 𝒜 :=
      HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 Nat.zero_lt_one
        (MvPolynomial.isHomogeneous_X R i)
    have : MvPolynomial.X i ∈ (⊥ : HomogeneousIdeal 𝒜) := h hX
    simpa using (MvPolynomial.X_ne_zero (R := R) i this)

/-- Polynomial projective space over an integral domain, with at least one
homogeneous coordinate, is irreducible. -/
instance polynomialProj_irreducibleSpace :
    IrreducibleSpace (AlgebraicGeometry.Proj 𝒜) := by
  apply (irreducibleSpace_def _).2
  have hclosure : closure ({polynomialProjGenericPoint R ι} :
      Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [← ProjectiveSpectrum.le_iff_mem_closure]
    change (⊥ : HomogeneousIdeal 𝒜) ≤ x.asHomogeneousIdeal
    exact bot_le
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
  rw [← hclosure]
  exact isIrreducible_singleton.closure

end ProjectiveSpace
