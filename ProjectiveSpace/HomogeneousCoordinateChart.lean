/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.HomogeneousCoordinatePoint
public import ProjectiveSpace.StandardChartScheme

/-!
# Homogeneous-coordinate points in standard affine charts

This file identifies the literal affine-chart coordinates of a point of
polynomial projective space constructed from homogeneous coordinates. A
nonzero vector `a : ι → k` belongs to the standard chart indexed by `i`
exactly when `a i ≠ 0`; on that chart, the corresponding prime of the
polynomial coordinate ring is evaluation at `a j / a i`.

The result only needs a field, not algebraic closure. The index and
coefficient types may live in independent universes.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable {k : Type u} [Field k] {ι : Type v}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The affine coordinates obtained by normalizing the `i`th homogeneous
coordinate to one. -/
@[expose] def normalizedCoordinates (a : ι → k) (i : ι) : {j : ι // j ≠ i} → k :=
  fun j ↦ a j.1 / a i

/-- The point of the literal `i`th polynomial chart obtained by evaluating at
the normalized homogeneous coordinates `a j / a i`. -/
@[expose] def affineCoordinatePoint (a : ι → k) (i : ι) :
    PrimeSpectrum (MvPolynomial {j : ι // j ≠ i} k) :=
  ⟨RingHom.ker (MvPolynomial.aeval (normalizedCoordinates a i)).toRingHom,
    RingHom.ker_isPrime
      (MvPolynomial.aeval (normalizedCoordinates a i)).toRingHom⟩

/-- A homogeneous-coordinate point belongs to `D₊(X i)` exactly when its
`i`th coordinate is nonzero. -/
theorem homogeneousCoordinatePoint_mem_basicOpen_X_iff
    (a : ι → k) (ha : a ≠ 0) (i : ι) :
    homogeneousCoordinatePoint a ha ∈
        ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule ι k)
          (MvPolynomial.X i) ↔
      a i ≠ 0 := by
  rw [ProjectiveSpectrum.mem_basicOpen]
  constructor
  · intro hmem hai
    apply hmem
    change MvPolynomial.X i ∈ homogeneousCoordinateIdeal a
    rw [homogeneousCoordinateIdeal, RingHom.mem_ker]
    simp [homogeneousCoordinateMap, hai]
  · exact X_not_mem_homogeneousCoordinateIdeal a i

/-- Nonmembership of `X i` in the homogeneous-coordinate prime is equivalent
to nonvanishing of the `i`th coordinate, in simp-normal form. -/
@[simp]
theorem homogeneousCoordinatePoint_X_not_mem_asHomogeneousIdeal_iff
    (a : ι → k) (ha : a ≠ 0) (i : ι) :
    MvPolynomial.X i ∉ (homogeneousCoordinatePoint a ha).asHomogeneousIdeal ↔
      a i ≠ 0 := by
  simpa only [ProjectiveSpectrum.mem_basicOpen] using
    homogeneousCoordinatePoint_mem_basicOpen_X_iff a ha i

private def localizationEvaluation (a : ι → k) (i : ι) (hi : a i ≠ 0) :
    Localization.Away (MvPolynomial.X i : MvPolynomial ι k) →+* k :=
  IsLocalization.Away.lift
    (R := MvPolynomial ι k)
    (S := Localization.Away (MvPolynomial.X i : MvPolynomial ι k))
    (P := k) (MvPolynomial.X i) (g := MvPolynomial.eval a) (by simp [hi])

private def chartEvaluation (a : ι → k) (i : ι) (hi : a i ≠ 0) :
    StandardChart k ι i →+* k :=
  (localizationEvaluation a i hi).comp
    (algebraMap (StandardChart k ι i)
      (Localization.Away (MvPolynomial.X i : MvPolynomial ι k)))

@[simp]
private theorem chartEvaluation_coordinateRatio (a : ι → k) (i : ι)
    (hi : a i ≠ 0) (j : {j : ι // j ≠ i}) :
    chartEvaluation a i hi (coordinateRatio k ι i j) = a j.1 / a i := by
  rw [chartEvaluation, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, coordinateRatio_val]
  rw [Localization.mk_eq_mk', localizationEvaluation,
    IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [MvPolynomial.eval_X, pow_one]
  field_simp

private def chartEvaluationAlgHom (a : ι → k) (i : ι) (hi : a i ≠ 0) :
    StandardChart k ι i →ₐ[k] k where
  __ := chartEvaluation a i hi
  commutes' r := by
    change localizationEvaluation a i hi
      (algebraMap (MvPolynomial ι k)
        (Localization.Away (MvPolynomial.X i : MvPolynomial ι k))
        (MvPolynomial.C r)) = r
    simp [localizationEvaluation]

private theorem chartEvaluationAlgHom_comp_standardChartEquiv [Fintype ι]
    (a : ι → k) (i : ι) (hi : a i ≠ 0) :
    (chartEvaluationAlgHom a i hi).comp (standardChartEquiv k ι i).toAlgHom =
      MvPolynomial.aeval (normalizedCoordinates a i) := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
  change chartEvaluation a i hi
      (standardChartEquiv k ι i (MvPolynomial.X j)) =
    normalizedCoordinates a i j
  rw [standardChartEquiv_X, chartEvaluation_coordinateRatio]
  rfl

private theorem standardCoordinateChartIso_affineCoordinatePoint_asIdeal
    [Fintype ι] (a : ι → k) (i : ι) (hi : a i ≠ 0) :
    (((standardCoordinateChartIso k ι i).hom.base
      (affineCoordinatePoint a i)).asIdeal) =
        RingHom.ker (chartEvaluation a i hi) := by
  change (PrimeSpectrum.comap
      (standardChartEquiv k ι i).symm.toRingEquiv.toRingHom
      (affineCoordinatePoint a i)).asIdeal = _
  ext z
  change MvPolynomial.aeval (normalizedCoordinates a i)
      ((standardChartEquiv k ι i).symm z) = 0 ↔
    chartEvaluation a i hi z = 0
  have h := DFunLike.congr_fun
    (chartEvaluationAlgHom_comp_standardChartEquiv a i hi)
    ((standardChartEquiv k ι i).symm z)
  rw [AlgHom.comp_apply] at h
  change chartEvaluation a i hi
      (standardChartEquiv k ι i ((standardChartEquiv k ι i).symm z)) = _ at h
  rw [AlgEquiv.apply_symm_apply] at h
  rw [h]

private def homogeneousCoordinatePointOnChart (a : ι → k) (ha : a ≠ 0)
    (i : ι) (hi : a i ≠ 0) :
    AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) :=
  ⟨homogeneousCoordinatePoint a ha,
    (homogeneousCoordinatePoint_mem_basicOpen_X_iff a ha i).2 hi⟩

set_option backward.isDefEq.respectTransparency.types false in
private theorem toSpec_homogeneousCoordinatePoint_asIdeal
    (a : ι → k) (ha : a ≠ 0) (i : ι) (hi : a i ≠ 0) :
    (AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec
      (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
      (homogeneousCoordinatePointOnChart a ha i hi)).asIdeal =
        RingHom.ker (chartEvaluation a i hi) := by
  ext z
  obtain ⟨w, rfl⟩ := HomogeneousLocalization.mk_surjective z
  have hcarrier :
      (AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec
        (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
        (homogeneousCoordinatePointOnChart a ha i hi)).asIdeal =
      AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.carrier
        (homogeneousCoordinatePointOnChart a ha i hi) := rfl
  rw [hcarrier,
    AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier,
    RingHom.mem_ker]
  change w.num.1 ∈ homogeneousCoordinateIdeal a ↔ _
  rw [mem_homogeneousCoordinateIdeal_iff_eval_eq_zero a
    ((MvPolynomial.mem_homogeneousSubmodule w.deg w.num.1).1 w.num.2)]
  change MvPolynomial.eval a w.num.1 = 0 ↔
    chartEvaluation a i hi (HomogeneousLocalization.mk w) = 0
  obtain ⟨d, hd⟩ := w.den_mem
  rw [chartEvaluation, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk]
  rw [Localization.mk_eq_mk', localizationEvaluation,
    IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [← hd, map_pow, MvPolynomial.eval_X]
  field_simp
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Under the literal `i`th polynomial chart map, evaluation at the normalized
coordinates `a j / a i` is the intrinsic homogeneous-coordinate point
represented by `a`. -/
theorem standardCoordinateChartMap_affineCoordinatePoint [Fintype ι]
    (a : ι → k) (ha : a ≠ 0) (i : ι) (hi : a i ≠ 0) :
    (standardCoordinateChartMap k ι i).base (affineCoordinatePoint a i) =
      homogeneousCoordinatePoint a ha := by
  let p := homogeneousCoordinatePointOnChart a ha i hi
  let q := (standardCoordinateChartIso k ι i).hom.base
    (affineCoordinatePoint a i)
  let e := AlgebraicGeometry.Proj.basicOpenIsoSpec
    (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
    (by simpa using MvPolynomial.isHomogeneous_X k i) (by norm_num)
  let einv := e.inv
  have hq : e.hom.base p = q := by
    have htop : AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec
        (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) p = q := by
      apply PrimeSpectrum.ext
      exact (toSpec_homogeneousCoordinatePoint_asIdeal a ha i hi).trans
        (standardCoordinateChartIso_affineCoordinatePoint_asIdeal a i hi).symm
    have hscheme :=
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq
        (MvPolynomial.homogeneousSubmodule ι k) p).trans htop
    rw [show e.hom = AlgebraicGeometry.Proj.basicOpenToSpec
        (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) from
      AlgebraicGeometry.Proj.basicOpenIsoSpec_hom _ _ _ _]
    exact hscheme
  have hinv : einv.base q = p := by
    dsimp [einv]
    rw [← hq]
    change ((e.hom ≫ e.inv).base) p = p
    rw [e.hom_inv_id]
    rfl
  let incl := (AlgebraicGeometry.Proj.basicOpen
    (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)).ι
  let c := (einv ≫ incl)
  change c.base q = _
  change incl.base (einv.base q) = _
  rw [hinv]
  rfl

end ProjectiveSpace
