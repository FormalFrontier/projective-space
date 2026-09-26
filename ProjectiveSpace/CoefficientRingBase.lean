/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.StandardChart
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The coefficient-ring base of polynomial projective space

This file identifies the degree-zero part of the total-degree grading on a
multivariable polynomial ring with its coefficient ring. It then packages the
structure morphism from polynomial `Proj` to the coefficient spectrum.

The direct structure morphism allows the coordinate type to live in a universe
absorbed by the coefficient-ring universe; in particular, it applies directly
to `Fin n` coordinates over an arbitrary-universe coefficient ring. A universe-
lifted version preserves fully independent universes. For a finite coordinate
type, both morphisms are locally of finite type and quasicompact.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory

scoped[ProjectiveSpace] attribute [instance] MvPolynomial.gradedAlgebra

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R]
variable (ι : Type v)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

/-- The coefficient ring is canonically isomorphic, as an algebra over itself,
to the degree-zero part of its multivariable polynomial ring. -/
@[expose] def mvPolynomialDegreeZeroEquiv : R ≃ₐ[R] 𝒜 0 where
  toFun r := ⟨MvPolynomial.C r,
    (MvPolynomial.mem_homogeneousSubmodule 0 _).2
      (MvPolynomial.isHomogeneous_C ι r)⟩
  invFun f := f.1.coeff 0
  left_inv r := by simp
  right_inv f := by
    apply Subtype.ext
    exact (zeroDegree_eq_C R ι f).symm
  map_mul' r s := by ext; simp
  map_add' r s := by ext; simp
  commutes' r := rfl

@[simp]
theorem coe_mvPolynomialDegreeZeroEquiv_apply (r : R) :
    ((mvPolynomialDegreeZeroEquiv R ι r : 𝒜 0) : MvPolynomial ι R) =
      MvPolynomial.C r := rfl

@[simp]
theorem mvPolynomialDegreeZeroEquiv_symm_apply (f : 𝒜 0) :
    (mvPolynomialDegreeZeroEquiv R ι).symm f = f.1.coeff 0 := rfl

/-- A multivariable polynomial ring in finitely many variables is of finite
type over its degree-zero homogeneous component. -/
instance instFiniteTypeDegreeZeroMvPolynomial [Finite ι] :
    Algebra.FiniteType (𝒜 0) (MvPolynomial ι R) := by
  classical
  let _ := Fintype.ofFinite ι
  refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact adjoin_degreeZero_range_X_eq_top R ι

/-- The structure morphism from polynomial projective space to a
universe-lifted copy of the coefficient spectrum. This version permits the
coefficient and coordinate types to live in independent universes. -/
def polynomialProjToSpecULift :
    Proj 𝒜 ⟶ Spec (CommRingCat.of (ULift.{v} R)) :=
  Proj.toSpecZero 𝒜 ≫
    Spec.map ((ULift.ringEquiv.trans
      (mvPolynomialDegreeZeroEquiv R ι).toRingEquiv).toCommRingCatIso.hom)

instance instLocallyOfFiniteTypePolynomialProjToSpecULift [Finite ι] :
    LocallyOfFiniteType (polynomialProjToSpecULift R ι) := by
  unfold polynomialProjToSpecULift
  infer_instance

instance instQuasiCompactPolynomialProjToSpecULift [Finite ι] :
    QuasiCompact (polynomialProjToSpecULift R ι) := by
  unfold polynomialProjToSpecULift
  infer_instance

section DirectCoefficientBase

variable (S : Type (max u v)) [CommRing S]
variable (κ : Type v)

local notation "ℬ" => MvPolynomial.homogeneousSubmodule κ S

/-- The structure morphism from polynomial projective space directly to its
coefficient spectrum. -/
def polynomialProjToSpec : Proj ℬ ⟶ Spec (CommRingCat.of S) :=
  Proj.toSpecZero ℬ ≫
    Spec.map (mvPolynomialDegreeZeroEquiv S κ).toRingEquiv.toCommRingCatIso.hom

instance instLocallyOfFiniteTypePolynomialProjToSpec [Finite κ] :
    LocallyOfFiniteType (polynomialProjToSpec S κ) := by
  unfold polynomialProjToSpec
  infer_instance

instance instQuasiCompactPolynomialProjToSpec [Finite κ] :
    QuasiCompact (polynomialProjToSpec S κ) := by
  unfold polynomialProjToSpec
  infer_instance

end DirectCoefficientBase

end ProjectiveSpace
