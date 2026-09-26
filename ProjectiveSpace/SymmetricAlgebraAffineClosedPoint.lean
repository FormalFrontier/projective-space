/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.SymmetricAlgebraClosedPoint
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Nullstellensatz

/-!
# Closed points of affine space from a symmetric algebra

For a finite-dimensional vector space `V` over an algebraically closed field,
the closed points of `Spec (SymmetricAlgebra k (Module.Dual k V))` are
canonically the vectors of `V`. The point attached to `v : V` is the kernel of
evaluation of linear forms at `v`.

This is the affine counterpart of the projective symmetric-algebra closed-point
classification. Evaluation at a scalar multiple `c • v` is also the
specialization at `c` of the homogeneous cone-line map attached to `v`.
The native module directly imports dual reflexivity and the polynomial
Nullstellensatz used by the finite-dimensional classification.
-/

set_option warningAsError true

public section

noncomputable section

open AlgebraicGeometry

namespace ProjectiveSpace

universe u v w

variable {k : Type u} {V : Type v} {I : Type w} [Field k]
variable [AddCommGroup V] [Module k V]

/-- Local decidable equality for coordinate proof construction; it is not a public
assumption of the affine evaluation API. -/
local instance instDecidableEqSymmetricAlgebraAffineClosedPoint : DecidableEq I :=
  Classical.decEq I

/-- Evaluation at a vector, extended from the dual to its symmetric algebra. -/
@[expose] noncomputable def symmetricAlgebraAffineCoordinateMap (v : V) :
    SymmetricAlgebra k (Module.Dual k V) →ₐ[k] k :=
  SymmetricAlgebra.lift (Module.Dual.eval k V v)

@[simp]
theorem symmetricAlgebraAffineCoordinateMap_ι (v : V)
    (φ : Module.Dual k V) :
    symmetricAlgebraAffineCoordinateMap v
      (SymmetricAlgebra.ι k (Module.Dual k V) φ) = φ v := by
  simp [symmetricAlgebraAffineCoordinateMap]

/-- The affine evaluation ideal attached to a vector. -/
@[expose] noncomputable def symmetricAlgebraAffineCoordinateIdeal (v : V) :
    Ideal (SymmetricAlgebra k (Module.Dual k V)) :=
  RingHom.ker (symmetricAlgebraAffineCoordinateMap v).toRingHom

/-- The affine evaluation ideal is maximal. -/
theorem symmetricAlgebraAffineCoordinateIdeal_isMaximal (v : V) :
    (symmetricAlgebraAffineCoordinateIdeal (k := k) v).IsMaximal := by
  exact RingHom.ker_isMaximal_of_surjective
    (symmetricAlgebraAffineCoordinateMap (k := k) v).toRingHom
    (fun c ↦
      ⟨algebraMap k (SymmetricAlgebra k (Module.Dual k V)) c, by simp⟩)

/-- The prime-spectrum point defined by evaluation at a vector. -/
@[expose] noncomputable def symmetricAlgebraAffineCoordinatePoint (v : V) :
    PrimeSpectrum (SymmetricAlgebra k (Module.Dual k V)) :=
  ⟨symmetricAlgebraAffineCoordinateIdeal v,
    (symmetricAlgebraAffineCoordinateIdeal_isMaximal (k := k) v).isPrime⟩

@[simp]
theorem symmetricAlgebraAffineCoordinatePoint_asIdeal (v : V) :
    (symmetricAlgebraAffineCoordinatePoint v).asIdeal =
      symmetricAlgebraAffineCoordinateIdeal (k := k) v :=
  rfl

/-- Evaluation points of the symmetric algebra are closed. -/
theorem symmetricAlgebraAffineCoordinatePoint_isClosed (v : V) :
    IsClosed ({symmetricAlgebraAffineCoordinatePoint v} :
      Set (PrimeSpectrum (SymmetricAlgebra k (Module.Dual k V)))) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
    (symmetricAlgebraAffineCoordinateIdeal_isMaximal (k := k) v)

/-- A vector as a closed point of the affine spectrum of the symmetric algebra
on its dual. -/
@[expose] noncomputable def symmetricAlgebraAffineClosedPoint (v : V) :
    closedPoints (PrimeSpectrum (SymmetricAlgebra k (Module.Dual k V))) :=
  ⟨symmetricAlgebraAffineCoordinatePoint v,
    symmetricAlgebraAffineCoordinatePoint_isClosed v⟩

/-- The affine-space point associated to a tuple of polynomial coordinates. -/
@[expose] noncomputable def mvPolynomialAffineCoordinatePoint (a : I → k) :
    PrimeSpectrum (MvPolynomial I k) :=
  MvPolynomial.pointToPoint a

@[simp]
theorem mvPolynomialAffineCoordinatePoint_asIdeal (a : I → k) :
    (mvPolynomialAffineCoordinatePoint a).asIdeal =
      RingHom.ker (MvPolynomial.aeval a).toRingHom := by
  ext F
  exact MvPolynomial.mem_vanishingIdeal_singleton_iff a F

/-- Polynomial affine-coordinate points are closed. -/
theorem mvPolynomialAffineCoordinatePoint_isClosed (a : I → k) :
    IsClosed ({mvPolynomialAffineCoordinatePoint a} :
      Set (PrimeSpectrum (MvPolynomial I k))) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 <| by
    rw [mvPolynomialAffineCoordinatePoint_asIdeal]
    exact RingHom.ker_isMaximal_of_surjective
      (MvPolynomial.aeval a).toRingHom
      (fun c ↦ ⟨MvPolynomial.C c, by simp⟩)

/-- A tuple as a closed point of polynomial affine space. -/
@[expose] noncomputable def mvPolynomialAffineClosedPoint (a : I → k) :
    closedPoints (PrimeSpectrum (MvPolynomial I k)) :=
  ⟨mvPolynomialAffineCoordinatePoint a,
    mvPolynomialAffineCoordinatePoint_isClosed a⟩

/-- Polynomial affine-coordinate points remember their coordinates. -/
theorem mvPolynomialAffineClosedPoint_injective :
    Function.Injective
      (mvPolynomialAffineClosedPoint (k := k) (I := I)) := by
  intro a b hab
  funext i
  have hi : MvPolynomial.X i - MvPolynomial.C (a i) ∈
      (mvPolynomialAffineCoordinatePoint a).asIdeal := by
    rw [mvPolynomialAffineCoordinatePoint_asIdeal]
    change MvPolynomial.aeval a
      (MvPolynomial.X i - MvPolynomial.C (a i)) = 0
    simp
  have hp : mvPolynomialAffineCoordinatePoint a =
      mvPolynomialAffineCoordinatePoint b := congrArg Subtype.val hab
  rw [hp, mvPolynomialAffineCoordinatePoint_asIdeal] at hi
  change MvPolynomial.aeval b
    (MvPolynomial.X i - MvPolynomial.C (a i)) = 0 at hi
  have hba : b i - a i = 0 := by simpa using hi
  exact (sub_eq_zero.mp hba).symm

/-- Over an algebraically closed field, every closed point of finite-dimensional
polynomial affine space is an evaluation point. -/
theorem mvPolynomialAffineClosedPoint_surjective
    [Finite I] [IsAlgClosed k] :
    Function.Surjective
      (mvPolynomialAffineClosedPoint (k := k) (I := I)) := by
  intro p
  have hpMax : p.1.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p.1).mp p.2
  obtain ⟨a, ha⟩ :=
    MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hpMax
  refine ⟨a, Subtype.ext ?_⟩
  apply PrimeSpectrum.ext
  exact ha.symm

/-- Affine coordinates classify the closed points of finite-dimensional
polynomial affine space over an algebraically closed field. -/
@[expose] noncomputable def mvPolynomialAffineClosedPointsEquiv
    [Finite I] [IsAlgClosed k] :
    (I → k) ≃ closedPoints (PrimeSpectrum (MvPolynomial I k)) :=
  Equiv.ofBijective mvPolynomialAffineClosedPoint
    ⟨mvPolynomialAffineClosedPoint_injective,
      mvPolynomialAffineClosedPoint_surjective⟩

@[simp]
theorem mvPolynomialAffineClosedPointsEquiv_apply
    [Finite I] [IsAlgClosed k] (a : I → k) :
    mvPolynomialAffineClosedPointsEquiv a =
      mvPolynomialAffineClosedPoint a :=
  rfl

/-- A ring equivalence induces the contravariant equivalence between the closed
points of the corresponding prime spectra. -/
@[expose] noncomputable def primeSpectrumClosedPointsEquivOfRingEquiv
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    closedPoints (PrimeSpectrum R) ≃ closedPoints (PrimeSpectrum S) where
  toFun p :=
    ⟨PrimeSpectrum.comapEquiv e p.1,
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 <| by
        change (p.1.asIdeal.comap e.symm.toRingHom).IsMaximal
        exact ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p.1).mp p.2).comap_bijective
          e.symm.toRingHom e.symm.bijective⟩
  invFun p :=
    ⟨PrimeSpectrum.comapEquiv e.symm p.1,
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 <| by
        change (p.1.asIdeal.comap e.toRingHom).IsMaximal
        exact ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p.1).mp p.2).comap_bijective
          e.toRingHom e.bijective⟩
  left_inv p := Subtype.ext <| (PrimeSpectrum.comapEquiv e).symm_apply_apply p.1
  right_inv p := Subtype.ext <| (PrimeSpectrum.comapEquiv e).apply_symm_apply p.1

@[simp]
theorem primeSpectrumClosedPointsEquivOfRingEquiv_apply_coe
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (e : R ≃+* S) (p : closedPoints (PrimeSpectrum R)) :
    (primeSpectrumClosedPointsEquivOfRingEquiv e p).1 =
      PrimeSpectrum.comap e.symm.toRingHom p.1 :=
  rfl

/-- A dual basis identifies intrinsic affine evaluation with polynomial
evaluation at the corresponding coordinates. -/
theorem affineCoordinateMap_comp_equivMvPolynomial
    [Finite I] (b : Module.Basis I k V) (v : V) :
    (MvPolynomial.aeval (b.equivFun v)).comp
        (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toAlgHom =
      symmetricAlgebraAffineCoordinateMap v := by
  classical
  apply SymmetricAlgebra.algHom_ext
  apply b.dualBasis.ext
  intro i
  change MvPolynomial.aeval (b.equivFun v)
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis
        (SymmetricAlgebra.ι k (Module.Dual k V) (b.dualBasis i))) =
    symmetricAlgebraAffineCoordinateMap v
      (SymmetricAlgebra.ι k (Module.Dual k V) (b.dualBasis i))
  rw [SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.aeval_X,
    symmetricAlgebraAffineCoordinateMap_ι, Module.Basis.dualBasis_apply,
    Module.Basis.equivFun_apply]

/-- Pulling a polynomial affine-coordinate point back through any dual-basis
presentation gives the intrinsic affine evaluation point. -/
theorem mvPolynomialAffineCoordinatePoint_comap_equivMvPolynomial
    [Finite I] (b : Module.Basis I k V) (v : V) :
    PrimeSpectrum.comap
        (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toRingEquiv.toRingHom
        (mvPolynomialAffineCoordinatePoint (b.equivFun v)) =
      symmetricAlgebraAffineCoordinatePoint v := by
  apply PrimeSpectrum.ext
  change ((mvPolynomialAffineCoordinatePoint (b.equivFun v)).asIdeal).comap
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toAlgHom.toRingHom =
    (symmetricAlgebraAffineCoordinatePoint v).asIdeal
  rw [mvPolynomialAffineCoordinatePoint_asIdeal]
  change (RingHom.ker (MvPolynomial.aeval (b.equivFun v)).toRingHom).comap
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toAlgHom.toRingHom =
    RingHom.ker (symmetricAlgebraAffineCoordinateMap v).toRingHom
  rw [RingHom.comap_ker]
  congr 1
  exact congrArg AlgHom.toRingHom
    (affineCoordinateMap_comp_equivMvPolynomial b v)

/-- The affine closed point computed through a chosen finite dual basis. Its
public type does not expose coordinate decidability. -/
@[expose] noncomputable def symmetricAlgebraAffineClosedPointOfBasis
    [Finite I] (b : Module.Basis I k V) (v : V) :
    closedPoints
      (PrimeSpectrum (SymmetricAlgebra k (Module.Dual k V))) :=
  ⟨PrimeSpectrum.comap
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toRingEquiv.toRingHom
      (mvPolynomialAffineCoordinatePoint (b.equivFun v)), by
    rw [mvPolynomialAffineCoordinatePoint_comap_equivMvPolynomial]
    exact symmetricAlgebraAffineCoordinatePoint_isClosed v⟩

/-- Computing an affine closed point through any finite dual basis gives the
basis-free evaluation point. -/
theorem symmetricAlgebraAffineClosedPointOfBasis_eq
    [Finite I] (b : Module.Basis I k V) (v : V) :
    symmetricAlgebraAffineClosedPointOfBasis b v =
      symmetricAlgebraAffineClosedPoint v := by
  apply Subtype.ext
  exact mvPolynomialAffineCoordinatePoint_comap_equivMvPolynomial b v

/-- For a reflexive module, distinct vectors define distinct affine evaluation
points. In particular, this applies to every finite-dimensional vector space. -/
theorem symmetricAlgebraAffineClosedPoint_injective
    [Module.IsReflexive k V] :
    Function.Injective
      (symmetricAlgebraAffineClosedPoint (k := k) (V := V)) := by
  intro v w hvw
  apply (Module.evalEquiv k V).injective
  ext φ
  simp only [Module.evalEquiv_apply, Module.Dual.eval_apply]
  have hp : symmetricAlgebraAffineCoordinatePoint v =
      symmetricAlgebraAffineCoordinatePoint w := congrArg Subtype.val hvw
  have hI := congrArg PrimeSpectrum.asIdeal hp
  let F := SymmetricAlgebra.ι k (Module.Dual k V) φ -
    algebraMap k (SymmetricAlgebra k (Module.Dual k V)) (φ v)
  have hF : F ∈ (symmetricAlgebraAffineCoordinatePoint v).asIdeal := by
    change symmetricAlgebraAffineCoordinateMap v F = 0
    simp [F]
  rw [hI] at hF
  change symmetricAlgebraAffineCoordinateMap w F = 0 at hF
  have hwv : φ w - φ v = 0 := by simpa [F] using hF
  exact (sub_eq_zero.mp hwv).symm

/-- A finite basis and the affine Nullstellensatz show that every closed point
of the symmetric algebra on the dual is an evaluation point. -/
theorem symmetricAlgebraAffineClosedPoint_surjective_of_basis
    [Finite I] [IsAlgClosed k] (b : Module.Basis I k V) :
    Function.Surjective
      (symmetricAlgebraAffineClosedPoint (k := k) (V := V)) := by
  intro p
  let q : PrimeSpectrum (MvPolynomial I k) :=
    PrimeSpectrum.comap
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm.toRingEquiv.toRingHom
      p.1
  have hpMax : p.1.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p.1).mp p.2
  have hqMax : q.asIdeal.IsMaximal := by
    dsimp only [q]
    rw [PrimeSpectrum.comap_asIdeal]
    exact hpMax.comap_bijective
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm.toRingEquiv.toRingHom
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm.bijective
  obtain ⟨a, ha⟩ :=
    MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hqMax
  have hqa : q = mvPolynomialAffineCoordinatePoint a := by
    apply PrimeSpectrum.ext
    change q.asIdeal = MvPolynomial.vanishingIdeal k {a}
    exact ha
  have hback := congrArg
    (PrimeSpectrum.comapEquiv
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toRingEquiv).symm hqa
  have hqApply : q =
      (PrimeSpectrum.comapEquiv
        (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toRingEquiv) p.1 := rfl
  rw [hqApply, OrderIso.symm_apply_apply] at hback
  change p.1 = PrimeSpectrum.comap
    (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toRingEquiv.toRingHom
      (mvPolynomialAffineCoordinatePoint a) at hback
  let v := b.equivFun.symm a
  have hv : b.equivFun v = a := by
    dsimp only [v]
    exact b.equivFun.apply_symm_apply a
  refine ⟨v, Subtype.ext ?_⟩
  change symmetricAlgebraAffineCoordinatePoint v = p.1
  calc
    symmetricAlgebraAffineCoordinatePoint v =
        PrimeSpectrum.comap
          (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toRingEquiv.toRingHom
          (mvPolynomialAffineCoordinatePoint (b.equivFun v)) :=
      (mvPolynomialAffineCoordinatePoint_comap_equivMvPolynomial b v).symm
    _ = PrimeSpectrum.comap
          (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toRingEquiv.toRingHom
          (mvPolynomialAffineCoordinatePoint a) := by
      rw [hv]
    _ = p.1 := hback.symm

/-- Over an algebraically closed field, every closed point of the symmetric
algebra on the dual of a finite-dimensional vector space is an evaluation
point. -/
theorem symmetricAlgebraAffineClosedPoint_surjective
    [FiniteDimensional k V] [IsAlgClosed k] :
    Function.Surjective
      (symmetricAlgebraAffineClosedPoint (k := k) (V := V)) :=
  symmetricAlgebraAffineClosedPoint_surjective_of_basis
    (Module.finBasis k V)

/-- A finite-dimensional vector space over an algebraically closed field is
canonically equivalent to the closed points of the affine spectrum of the
symmetric algebra on its dual. -/
@[expose] noncomputable def symmetricAlgebraAffineClosedPointsEquiv
    [FiniteDimensional k V] [IsAlgClosed k] :
    V ≃ closedPoints
      (PrimeSpectrum (SymmetricAlgebra k (Module.Dual k V))) :=
  Equiv.ofBijective
    (symmetricAlgebraAffineClosedPoint (k := k) (V := V))
    ⟨symmetricAlgebraAffineClosedPoint_injective,
      symmetricAlgebraAffineClosedPoint_surjective⟩

@[simp]
theorem symmetricAlgebraAffineClosedPointsEquiv_apply
    [FiniteDimensional k V] [IsAlgClosed k] (v : V) :
    symmetricAlgebraAffineClosedPointsEquiv (k := k) v =
      symmetricAlgebraAffineClosedPoint (k := k) v :=
  rfl

/-- Every finite dual-basis polynomial presentation computes the canonical
affine closed point. -/
theorem symmetricAlgebraAffineClosedPointsEquiv_apply_eq_comap_ofBasis
    [Finite I] [FiniteDimensional k V] [IsAlgClosed k]
    (b : Module.Basis I k V) (v : V) :
    (symmetricAlgebraAffineClosedPointsEquiv (k := k) v).1 =
      PrimeSpectrum.comap
        (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toRingEquiv.toRingHom
        (mvPolynomialAffineClosedPointsEquiv (b.equivFun v)).1 := by
  rw [symmetricAlgebraAffineClosedPointsEquiv_apply,
    mvPolynomialAffineClosedPointsEquiv_apply]
  exact (mvPolynomialAffineCoordinatePoint_comap_equivMvPolynomial b v).symm

/-- Every finite basis computes the value of the canonical affine
closed-point equivalence. -/
theorem symmetricAlgebraAffineClosedPointsEquiv_apply_eq_ofBasis
    [Finite I] [FiniteDimensional k V] [IsAlgClosed k]
    (b : Module.Basis I k V) (v : V) :
    symmetricAlgebraAffineClosedPointsEquiv (k := k) v =
      symmetricAlgebraAffineClosedPointOfBasis b v := by
  rw [symmetricAlgebraAffineClosedPointsEquiv_apply,
    symmetricAlgebraAffineClosedPointOfBasis_eq]

/-- A linear equivalence induces the contravariant equivalence on affine
closed points of the symmetric algebras on the dual spaces. -/
@[expose] noncomputable def symmetricAlgebraAffineClosedPointsEquivOfLinearEquiv
    {W : Type w} [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] W) :
    closedPoints
        (PrimeSpectrum (SymmetricAlgebra k (Module.Dual k V))) ≃
      closedPoints
        (PrimeSpectrum (SymmetricAlgebra k (Module.Dual k W))) :=
  primeSpectrumClosedPointsEquivOfRingEquiv
    (SymmetricAlgebra.congr e.dualMap).symm.toRingEquiv

@[simp]
theorem symmetricAlgebraAffineClosedPointsEquivOfLinearEquiv_apply_coe
    {W : Type w} [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] W)
    (p : closedPoints
      (PrimeSpectrum (SymmetricAlgebra k (Module.Dual k V)))) :
    (symmetricAlgebraAffineClosedPointsEquivOfLinearEquiv e p).1 =
      PrimeSpectrum.comap
        (SymmetricAlgebra.map e.dualMap.toLinearMap).toRingHom p.1 :=
  rfl

/-- Pullback of linear forms carries the affine evaluation point of `v` to the
affine evaluation point of its image under a linear equivalence. -/
theorem symmetricAlgebraAffineCoordinatePoint_map
    {W : Type w} [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] W) (v : V) :
    PrimeSpectrum.comap
        (SymmetricAlgebra.map e.dualMap.toLinearMap).toRingHom
        (symmetricAlgebraAffineCoordinatePoint v) =
      symmetricAlgebraAffineCoordinatePoint (e v) := by
  apply PrimeSpectrum.ext
  change (symmetricAlgebraAffineCoordinateIdeal v).comap
      (SymmetricAlgebra.map e.dualMap.toLinearMap).toRingHom =
    symmetricAlgebraAffineCoordinateIdeal (e v)
  rw [symmetricAlgebraAffineCoordinateIdeal,
    symmetricAlgebraAffineCoordinateIdeal, RingHom.comap_ker]
  congr 1
  apply congrArg AlgHom.toRingHom
    (show (symmetricAlgebraAffineCoordinateMap v).comp
        (SymmetricAlgebra.map e.dualMap.toLinearMap) =
      symmetricAlgebraAffineCoordinateMap (e v) by
        apply SymmetricAlgebra.algHom_ext
        ext φ
        simp [symmetricAlgebraAffineCoordinateMap])

/-- The closed evaluation point construction is natural under linear
equivalences. -/
theorem symmetricAlgebraAffineClosedPoint_naturality
    {W : Type w} [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] W) (v : V) :
    symmetricAlgebraAffineClosedPointsEquivOfLinearEquiv e
        (symmetricAlgebraAffineClosedPoint v) =
      symmetricAlgebraAffineClosedPoint (e v) := by
  apply Subtype.ext
  rw [symmetricAlgebraAffineClosedPointsEquivOfLinearEquiv_apply_coe]
  exact symmetricAlgebraAffineCoordinatePoint_map e v

/-- The canonical affine closed-point equivalence commutes with linear
equivalences. -/
theorem symmetricAlgebraAffineClosedPointsEquiv_naturality
    {W : Type w} [AddCommGroup W] [Module k W]
    [FiniteDimensional k V] [FiniteDimensional k W] [IsAlgClosed k]
    (e : V ≃ₗ[k] W) (v : V) :
    symmetricAlgebraAffineClosedPointsEquivOfLinearEquiv e
        (symmetricAlgebraAffineClosedPointsEquiv v) =
      symmetricAlgebraAffineClosedPointsEquiv (e v) := by
  rw [symmetricAlgebraAffineClosedPointsEquiv_apply,
    symmetricAlgebraAffineClosedPointsEquiv_apply]
  exact symmetricAlgebraAffineClosedPoint_naturality e v

/-- Specializing the cone-line map of `v` at `c` gives affine evaluation at
`c • v`. -/
theorem polynomialEval_comp_symmetricAlgebraHomogeneousCoordinateMap
    (c : k) (v : V) :
    (Polynomial.aeval c : Polynomial k →ₐ[k] k).comp
        (symmetricAlgebraHomogeneousCoordinateMap v) =
      symmetricAlgebraAffineCoordinateMap (c • v) := by
  apply SymmetricAlgebra.algHom_ext
  ext φ
  simp only [LinearMap.coe_comp, LinearMap.coe_ofClass, AlgHom.coe_comp,
    Polynomial.coe_aeval_eq_eval, Function.comp_apply,
    symmetricAlgebraHomogeneousCoordinateMap_ι, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, symmetricAlgebraAffineCoordinateMap_ι,
    map_smul, smul_eq_mul]
  exact mul_comm _ _


end ProjectiveSpace
