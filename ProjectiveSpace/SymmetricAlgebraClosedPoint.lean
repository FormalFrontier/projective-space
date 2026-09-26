/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.HomogeneousCoordinateClosedPoint
public import ProjectiveSpace.SymmetricAlgebraProj
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Closed points of `Proj` of a symmetric algebra

For a finite-dimensional vector space `V` over an algebraically closed field,
the closed points of `Proj (SymmetricAlgebra k (Module.Dual k V))` are the
one-dimensional subspaces of `V`. A finite basis proves this by transporting
the homogeneous-coordinate classification for a polynomial ring.

The transported homogeneous-coordinate ideal is intrinsically the kernel of
the map sending a linear form `φ` to `(φ v) X`. Consequently the resulting
point and the equivalence on closed points are independent of the basis.
The coefficient field, vector space, basis index, and comparison vector space
may live in independent universes.
-/

set_option warningAsError true

public section

noncomputable section

open AlgebraicGeometry
open scoped LinearAlgebra.Projectivization ProjectiveSpace

namespace ProjectiveSpace

universe u v w x

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} {V : Type v} {I : Type w} [Field k]
variable [AddCommGroup V] [Module k V]

/-- Local decidable equality for finite-coordinate proof construction; it is not a public
assumption of the homogeneous-coordinate API. -/
local instance instDecidableEqSymmetricAlgebraClosedPoint : DecidableEq I :=
  Classical.decEq I

/-- Evaluation at a vector, followed by the degree-one polynomial embedding. -/
@[expose] noncomputable def dualConeLineMap (v : V) :
    Module.Dual k V →ₗ[k] Polynomial k where
  toFun φ := Polynomial.C (φ v) * Polynomial.X
  map_add' φ ψ := by simp [add_mul]
  map_smul' c φ := by
    change Polynomial.C (c * φ v) * Polynomial.X =
      c • (Polynomial.C (φ v) * Polynomial.X)
    rw [map_mul, Polynomial.smul_eq_C_mul, mul_assoc]

/-- The basis-free cone-line map from the symmetric algebra on the dual. -/
@[expose] noncomputable def symmetricAlgebraHomogeneousCoordinateMap (v : V) :
    SymmetricAlgebra k (Module.Dual k V) →ₐ[k] Polynomial k :=
  SymmetricAlgebra.lift (dualConeLineMap v)

@[simp]
theorem symmetricAlgebraHomogeneousCoordinateMap_ι (v : V)
    (φ : Module.Dual k V) :
    symmetricAlgebraHomogeneousCoordinateMap v
      (SymmetricAlgebra.ι k (Module.Dual k V) φ) =
        Polynomial.C (φ v) * Polynomial.X := by
  simp [symmetricAlgebraHomogeneousCoordinateMap, dualConeLineMap]

/-- The dual-basis polynomial presentation identifies the coordinate and
basis-free cone-line evaluation maps. A finite index suffices without an
enumerated `Fintype` assumption. -/
theorem homogeneousCoordinateMap_comp_equivMvPolynomial
    [Finite I]
    (b : Module.Basis I k V) (v : V) :
    (homogeneousCoordinateMap (b.equivFun v)).comp
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toAlgHom =
        symmetricAlgebraHomogeneousCoordinateMap v := by
  classical
  apply SymmetricAlgebra.algHom_ext
  apply b.dualBasis.ext
  intro i
  change homogeneousCoordinateMap (b.equivFun v)
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis
        (SymmetricAlgebra.ι k (Module.Dual k V) (b.dualBasis i))) =
    symmetricAlgebraHomogeneousCoordinateMap v
      (SymmetricAlgebra.ι k (Module.Dual k V) (b.dualBasis i))
  rw [SymmetricAlgebra.equivMvPolynomial_ι_apply,
    homogeneousCoordinateMap_X,
    symmetricAlgebraHomogeneousCoordinateMap_ι,
    Module.Basis.dualBasis_apply, Module.Basis.equivFun_apply]

variable [Fintype I]

/-- The basis-free homogeneous ideal defined by cone-line evaluation. -/
@[expose] noncomputable def symmetricAlgebraHomogeneousCoordinateIdeal (v : V) :
    Ideal (SymmetricAlgebra k (Module.Dual k V)) :=
  RingHom.ker (symmetricAlgebraHomogeneousCoordinateMap v).toRingHom

/-- Transport a polynomial homogeneous-coordinate point to symmetric-algebra
`Proj` using a basis. -/
@[expose] noncomputable def symmetricAlgebraHomogeneousCoordinatePointOfBasis
    (b : Module.Basis I k V) (v : V) (hv : v ≠ 0) :
    ProjectiveSpectrum
      (SymmetricAlgebra.homogeneousSubmodule
        (R := k) (M := Module.Dual k V)) :=
  ProjectiveSpectrum.comapFun
    (SymmetricAlgebra.equivMvPolynomialGradedHom b.dualBasis).toGradedRingHom
    (irrelevant_le_map_of_comp_eq_id
      (SymmetricAlgebra.equivMvPolynomialGradedHom b.dualBasis).toGradedRingHom
      (SymmetricAlgebra.equivMvPolynomialSymmGradedHom b.dualBasis).toGradedRingHom
      (symmetricAlgebraGradedHom_comp_mvPolynomialGradedHom b.dualBasis))
    (homogeneousCoordinatePoint (b.equivFun v)
      (b.equivFun.map_ne_zero_iff.mpr hv))

/-- The transported point has the basis-free cone-line evaluation kernel. -/
theorem symmetricAlgebraHomogeneousCoordinatePointOfBasis_toIdeal
    (b : Module.Basis I k V) (v : V) (hv : v ≠ 0) :
    (symmetricAlgebraHomogeneousCoordinatePointOfBasis b v hv).1.toIdeal =
      symmetricAlgebraHomogeneousCoordinateIdeal v := by
  change (homogeneousCoordinateIdeal (b.equivFun v)).comap
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toAlgHom.toRingHom =
    RingHom.ker (symmetricAlgebraHomogeneousCoordinateMap v).toRingHom
  rw [homogeneousCoordinateIdeal, RingHom.comap_ker]
  congr 1
  exact congrArg AlgHom.toRingHom
    (homogeneousCoordinateMap_comp_equivMvPolynomial b v)

/-- The transported symmetric-algebra point is independent of the chosen
basis. -/
theorem symmetricAlgebraHomogeneousCoordinatePointOfBasis_eq
    {J : Type x} [Fintype J]
    (b : Module.Basis I k V) (c : Module.Basis J k V) (v : V) (hv : v ≠ 0) :
    symmetricAlgebraHomogeneousCoordinatePointOfBasis b v hv =
      symmetricAlgebraHomogeneousCoordinatePointOfBasis c v hv := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [symmetricAlgebraHomogeneousCoordinatePointOfBasis_toIdeal,
    symmetricAlgebraHomogeneousCoordinatePointOfBasis_toIdeal]

/-- The homogeneous-coordinate point of symmetric-algebra `Proj`, defined
without choosing a public basis. -/
@[expose] noncomputable def symmetricAlgebraHomogeneousCoordinatePoint
    [FiniteDimensional k V] (v : V) (hv : v ≠ 0) :
    ProjectiveSpectrum
      (SymmetricAlgebra.homogeneousSubmodule
        (R := k) (M := Module.Dual k V)) :=
  symmetricAlgebraHomogeneousCoordinatePointOfBasis
    ((Module.finBasis k V).reindex (Equiv.ulift.{v}.symm)) v hv

/-- The basis-free point has the cone-line evaluation kernel. -/
@[simp]
theorem symmetricAlgebraHomogeneousCoordinatePoint_toIdeal
    [FiniteDimensional k V] (v : V) (hv : v ≠ 0) :
    (symmetricAlgebraHomogeneousCoordinatePoint v hv).1.toIdeal =
      symmetricAlgebraHomogeneousCoordinateIdeal (k := k) v :=
  symmetricAlgebraHomogeneousCoordinatePointOfBasis_toIdeal
    ((Module.finBasis k V).reindex (Equiv.ulift.{v}.symm)) v hv

/-- Any finite basis computes the basis-free homogeneous-coordinate point. -/
theorem symmetricAlgebraHomogeneousCoordinatePoint_eq_ofBasis
    [FiniteDimensional k V] (b : Module.Basis I k V) (v : V) (hv : v ≠ 0) :
    symmetricAlgebraHomogeneousCoordinatePoint v hv =
      symmetricAlgebraHomogeneousCoordinatePointOfBasis b v hv :=
  symmetricAlgebraHomogeneousCoordinatePointOfBasis_eq
    ((Module.finBasis k V).reindex (Equiv.ulift.{v}.symm)) b v hv

/-- The contravariant `Proj` equivalence induced by pullback of linear forms
sends the point of a line to the point of its image under the original linear
equivalence. -/
theorem symmetricAlgebraHomogeneousCoordinatePoint_map
    {W : Type w} [AddCommGroup W] [Module k W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    (e : V ≃ₗ[k] W) (v : V) (hv : v ≠ 0) :
    symmetricAlgebraProjectiveSpectrumEquivOfLinearEquiv e.dualMap
        (symmetricAlgebraHomogeneousCoordinatePoint v hv) =
      symmetricAlgebraHomogeneousCoordinatePoint (e v)
        (e.map_ne_zero_iff.mpr hv) := by
  rw [symmetricAlgebraProjectiveSpectrumEquivOfLinearEquiv_apply]
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  change ((symmetricAlgebraHomogeneousCoordinatePoint v hv).1.toIdeal).comap
      (SymmetricAlgebra.map e.dualMap.toLinearMap).toRingHom =
    (symmetricAlgebraHomogeneousCoordinatePoint (e v)
      (e.map_ne_zero_iff.mpr hv)).1.toIdeal
  rw [symmetricAlgebraHomogeneousCoordinatePoint_toIdeal,
    symmetricAlgebraHomogeneousCoordinatePoint_toIdeal]
  rw [symmetricAlgebraHomogeneousCoordinateIdeal,
    symmetricAlgebraHomogeneousCoordinateIdeal, RingHom.comap_ker]
  congr 1
  apply congrArg AlgHom.toRingHom
    (show (symmetricAlgebraHomogeneousCoordinateMap v).comp
        (SymmetricAlgebra.map e.dualMap.toLinearMap) =
      symmetricAlgebraHomogeneousCoordinateMap (e v) by
        apply SymmetricAlgebra.algHom_ext
        ext φ
        simp [symmetricAlgebraHomogeneousCoordinateMap, dualConeLineMap])

/-- A basis identifies projectivization of a vector space with
projectivization of its coordinate functions. -/
@[expose] noncomputable def projectivizationEquivCoordinates (b : Module.Basis I k V) :
    Projectivization k V ≃ Projectivization k (I → k) :=
  Equiv.ofBijective
    (Projectivization.map b.equivFun.toLinearMap b.equivFun.injective)
    ⟨Projectivization.map_injective b.equivFun.toLinearMap b.equivFun.injective,
      fun x ↦ by
        induction x using Projectivization.ind with
        | h a ha =>
          let a' := b.equivFun.symm a
          have ha' : a' ≠ 0 := b.equivFun.symm.map_ne_zero_iff.mpr ha
          refine ⟨Projectivization.mk k a' ha', ?_⟩
          rw [Projectivization.map_mk]
          rw [Projectivization.mk_eq_mk_iff']
          refine ⟨1, ?_⟩
          rw [one_smul]
          change a = b.equivFun a'
          exact (b.equivFun.apply_symm_apply a).symm⟩

@[simp]
theorem projectivizationEquivCoordinates_mk
    (b : Module.Basis I k V) (v : V) (hv : v ≠ 0) :
    projectivizationEquivCoordinates b (Projectivization.mk k v hv) =
      Projectivization.mk k (b.equivFun v)
        (b.equivFun.map_ne_zero_iff.mpr hv) := by
  exact Projectivization.map_mk b.equivFun.toLinearMap
    b.equivFun.injective v hv

/-- A basis gives the closed-point equivalence for `Proj` of the symmetric
algebra on the dual. -/
@[expose] noncomputable def projectivizationEquivSymmetricAlgebraClosedPointsOfBasis
    [IsAlgClosed k] (b : Module.Basis I k V) :
    Projectivization k V ≃
      closedPoints
        (Proj (SymmetricAlgebra.homogeneousSubmodule
          (R := k) (M := Module.Dual k V))) :=
  (projectivizationEquivCoordinates b).trans
    (projectivizationEquivClosedPoints (k := k) (ι := I)) |>.trans
      (mvPolynomialProjClosedPointsEquivSymmetricAlgebra b.dualBasis)

@[simp]
theorem projectivizationEquivSymmetricAlgebraClosedPointsOfBasis_mk
    [IsAlgClosed k] (b : Module.Basis I k V) (v : V) (hv : v ≠ 0) :
    (projectivizationEquivSymmetricAlgebraClosedPointsOfBasis b
      (Projectivization.mk k v hv)).1 =
        symmetricAlgebraHomogeneousCoordinatePointOfBasis b v hv := by
  rfl

/-- The projectivization-to-closed-points equivalence does not depend on the
chosen finite basis. -/
theorem projectivizationEquivSymmetricAlgebraClosedPointsOfBasis_eq
    [IsAlgClosed k] {J : Type x} [Fintype J]
    (b : Module.Basis I k V) (c : Module.Basis J k V) :
    projectivizationEquivSymmetricAlgebraClosedPointsOfBasis b =
      projectivizationEquivSymmetricAlgebraClosedPointsOfBasis c := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  induction x using Projectivization.ind with
  | h v hv =>
    rw [projectivizationEquivSymmetricAlgebraClosedPointsOfBasis_mk,
      projectivizationEquivSymmetricAlgebraClosedPointsOfBasis_mk]
    exact symmetricAlgebraHomogeneousCoordinatePointOfBasis_eq b c v hv

/-- Vector-space projectivization is canonically equivalent to the closed
points of `Proj` of the symmetric algebra on its dual. -/
@[expose] noncomputable def projectivizationEquivSymmetricAlgebraClosedPoints
    [FiniteDimensional k V] [IsAlgClosed k] :
    Projectivization k V ≃
      closedPoints
        (Proj (SymmetricAlgebra.homogeneousSubmodule
          (R := k) (M := Module.Dual k V))) :=
  projectivizationEquivSymmetricAlgebraClosedPointsOfBasis
    ((Module.finBasis k V).reindex (Equiv.ulift.{v}.symm))

@[simp]
theorem projectivizationEquivSymmetricAlgebraClosedPoints_mk
    [FiniteDimensional k V] [IsAlgClosed k] (v : V) (hv : v ≠ 0) :
    (projectivizationEquivSymmetricAlgebraClosedPoints
      (Projectivization.mk k v hv)).1 =
        symmetricAlgebraHomogeneousCoordinatePoint v hv := by
  rfl

/-- The equivalence computed using any finite basis is the canonical
basis-free equivalence. -/
theorem projectivizationEquivSymmetricAlgebraClosedPointsOfBasis_eq_canonical
    [FiniteDimensional k V] [IsAlgClosed k] (b : Module.Basis I k V) :
    projectivizationEquivSymmetricAlgebraClosedPointsOfBasis b =
      projectivizationEquivSymmetricAlgebraClosedPoints :=
  projectivizationEquivSymmetricAlgebraClosedPointsOfBasis_eq
    b ((Module.finBasis k V).reindex (Equiv.ulift.{v}.symm))

/-- The canonical closed-point equivalence is natural under linear
equivalences: projectivizing the original map agrees with contravariant `Proj`
transport along pullback of linear forms. -/
theorem projectivizationEquivSymmetricAlgebraClosedPoints_naturality
    {W : Type w} [AddCommGroup W] [Module k W]
    [FiniteDimensional k V] [FiniteDimensional k W] [IsAlgClosed k]
    (e : V ≃ₗ[k] W) (x : Projectivization k V) :
    symmetricAlgebraProjClosedPointsEquivOfLinearEquiv e.dualMap
        (projectivizationEquivSymmetricAlgebraClosedPoints x) =
      projectivizationEquivSymmetricAlgebraClosedPoints
        (Projectivization.map e.toLinearMap e.injective x) := by
  induction x using Projectivization.ind with
  | h v hv =>
    apply Subtype.ext
    rw [symmetricAlgebraProjClosedPointsEquivOfLinearEquiv_apply_coe,
      projectivizationEquivSymmetricAlgebraClosedPoints_mk,
      Projectivization.map_mk,
      projectivizationEquivSymmetricAlgebraClosedPoints_mk]
    exact symmetricAlgebraHomogeneousCoordinatePoint_map e v hv

/-- One-dimensional subspaces of a finite-dimensional vector space are
canonically equivalent to the closed points of `Proj` of the symmetric algebra
on its dual. -/
noncomputable def oneDimensionalSubspacesEquivSymmetricAlgebraClosedPoints
    [FiniteDimensional k V] [IsAlgClosed k] :
    {H : Submodule k V // Module.finrank k H = 1} ≃
      closedPoints
        (Proj (SymmetricAlgebra.homogeneousSubmodule
          (R := k) (M := Module.Dual k V))) :=
  (Projectivization.equivSubmodule k V).symm.trans
    projectivizationEquivSymmetricAlgebraClosedPoints


end ProjectiveSpace
