/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Polynomial coordinates on standard projective charts

For a finite family of homogeneous coordinates and a chosen coordinate `i`,
this file identifies the degree-zero homogeneous localization at `X i` with
the polynomial ring in the remaining ratios `X j / X i`. It also packages
pairwise overlap localizations and coordinate transitions; the homogeneous
overlap maps and identities themselves do not require a finite index type.

The result is valid over an arbitrary commutative ring, including the zero
ring. It is stated algebraically, independently of any particular construction
of projective space as a scheme.
-/

public section

noncomputable section

open HomogeneousLocalization

scoped[ProjectiveSpace] attribute [instance] MvPolynomial.gradedAlgebra

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R]
variable (ι : Type v) (i : ι)

/-- Classical decidable equality on coordinate indices, scoped to this chart module. -/
local instance instDecidableEqCoordinates : DecidableEq ι := Classical.decEq ι

local notation "Others" => {j : ι // j ≠ i}
local notation "Poly" => MvPolynomial ι R
local notation "Q" => MvPolynomial Others R
local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R
local notation "Xi" => (MvPolynomial.X i : MvPolynomial ι R)

/-- The coordinate ring of the standard chart indexed by `i`, presented as a
degree-zero homogeneous localization. -/
abbrev StandardChart := Away 𝒜 Xi

local notation "Chart" => StandardChart R ι i

private def dehomogenizePolynomial : Poly →ₐ[R] Q :=
  MvPolynomial.aeval fun j ↦ if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

@[simp]
private lemma dehomogenizePolynomial_X_self :
    dehomogenizePolynomial R ι i Xi = 1 := by
  simp [dehomogenizePolynomial]

@[simp]
private lemma dehomogenizePolynomial_X_other (j : Others) :
    dehomogenizePolynomial R ι i (MvPolynomial.X j.1) = MvPolynomial.X j := by
  simp [dehomogenizePolynomial, j.2]

private def coefficientHom : R →+* Chart :=
  (fromZeroRingHom 𝒜 (Submonoid.powers Xi)).comp
    { toFun := fun r ↦ ⟨MvPolynomial.C r,
        (MvPolynomial.mem_homogeneousSubmodule 0 _).2
          (MvPolynomial.isHomogeneous_C ι r)⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }

/-- The coefficient algebra structure on a standard chart. -/
instance standardChartAlgebra : Algebra R Chart :=
  ((fromZeroRingHom 𝒜 (Submonoid.powers Xi)).comp
    { toFun := fun r ↦ ⟨MvPolynomial.C r,
        (MvPolynomial.mem_homogeneousSubmodule 0 _).2
          (MvPolynomial.isHomogeneous_C ι r)⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }).toAlgebra

private theorem standardChartAlgebra_eq_privateConstruction :
    standardChartAlgebra R ι i = (coefficientHom R ι i).toAlgebra := by
  rfl

/-- The homogeneous coordinates generate the polynomial ring as an algebra
over its degree-zero homogeneous component. -/
theorem adjoin_degreeZero_range_X_eq_top :
    Algebra.adjoin (𝒜 0)
      (Set.range (MvPolynomial.X : ι → MvPolynomial ι R)) = ⊤ := by
  rw [eq_top_iff]
  intro p hpTop
  clear hpTop
  induction p using MvPolynomial.induction_on with
  | C r =>
      let cr : 𝒜 0 := ⟨MvPolynomial.C r,
        (MvPolynomial.mem_homogeneousSubmodule 0 _).2
          (MvPolynomial.isHomogeneous_C ι r)⟩
      exact algebraMap_mem (Algebra.adjoin (𝒜 0)
        (Set.range (MvPolynomial.X : ι → MvPolynomial ι R))) cr
  | add p q hp hq => exact add_mem hp hq
  | mul_X p j hp =>
      exact mul_mem hp (Algebra.subset_adjoin ⟨j, rfl⟩)

private lemma sum_eq_self_add_others [Fintype ι] (ai : ι → ℕ) :
    ∑ j, ai j = ai i + ∑ j : Others, ai j.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j ↦ j = i) ai]
  simp
  exact congrArg ai ((default : {j : ι // j = i}).property)

private lemma prod_eq_self_mul_others [Fintype ι] {M : Type*} [CommMonoid M]
    (f : ι → M) :
    ∏ j, f j = f i * ∏ j : Others, f j.1 := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j ↦ j = i) f]
  simp
  rw [congrArg f ((default : {j : ι // j = i}).property)]

/-- The affine coordinate `X j / X i` in the degree-zero homogeneous
localization at `X i`. -/
@[expose] def coordinateRatio (j : Others) : Chart :=
  Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R i) 1 (MvPolynomial.X j.1) (by
    simpa using MvPolynomial.isHomogeneous_X R j.1)

@[simp]
theorem coordinateRatio_val (j : Others) :
    (coordinateRatio R ι i j).val =
      Localization.mk (MvPolynomial.X j.1)
        ⟨Xi ^ 1, (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩ := by
  rfl

/-- A homogeneous polynomial of degree `d`, viewed as the degree-zero fraction
`F / X i ^ d` on the `i`th standard chart. -/
@[expose] def homogeneousPolynomialOnChart {d : ℕ} (F : Poly) (hF : F ∈ 𝒜 d) : Chart :=
  Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R i) d F (by simpa using hF)

/-- A homogeneous polynomial of fixed degree is determined by its fraction
`F / X i ^ d` on the `i`th standard chart. -/
theorem homogeneousPolynomialOnChart_injective {d : ℕ} {F G : Poly}
    (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d)
    (h : homogeneousPolynomialOnChart R ι i F hF =
      homogeneousPolynomialOnChart R ι i G hG) :
    F = G := by
  change Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R i) d F _ =
    Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R i) d G _ at h
  have hv := congrArg HomogeneousLocalization.val h
  change Localization.mk F _ = Localization.mk G _ at hv
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hv
  obtain ⟨⟨_, n, rfl⟩, hv⟩ := hv
  apply (MvPolynomial.isRegular_X_pow (R := R) (n := i) (n + d)).left
  simpa [pow_add, mul_assoc] using hv

private def chartMap : Q →ₐ[R] Chart :=
  MvPolynomial.aeval (coordinateRatio R ι i)

private def localizationDehomogenize : Localization.Away Xi →+* Q :=
  IsLocalization.Away.lift (R := Poly) (S := Localization.Away Xi) (P := Q) Xi
    (g := (dehomogenizePolynomial R ι i).toRingHom)
    (by simp)

private def dehomogenize : Chart →+* Q :=
  (localizationDehomogenize R ι i).comp
    (algebraMap Chart (Localization.Away Xi))

@[simp]
private lemma dehomogenize_coordinateRatio (j : Others) :
    dehomogenize R ι i (coordinateRatio R ι i j) = MvPolynomial.X j := by
  rw [dehomogenize, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    coordinateRatio_val]
  rw [Localization.mk_eq_mk', localizationDehomogenize, IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec]
  simp

@[simp]
private lemma dehomogenize_coefficient (r : R) :
    dehomogenize R ι i (algebraMap R Chart r) = MvPolynomial.C r := by
  change dehomogenize R ι i (coefficientHom R ι i r) = _
  rw [dehomogenize, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  change localizationDehomogenize R ι i
    (algebraMap Poly (Localization.Away Xi) (MvPolynomial.C r)) = _
  simp [localizationDehomogenize]

private lemma dehomogenize_chartMap (f : Q) :
    dehomogenize R ι i (chartMap R ι i f) = f := by
  let d : Chart →ₐ[R] Q :=
    { __ := dehomogenize R ι i
      commutes' := dehomogenize_coefficient R ι i }
  change d (chartMap R ι i f) = f
  have h : d.comp (chartMap R ι i) = AlgHom.id R Q := by
    apply MvPolynomial.algHom_ext
    intro j
    change dehomogenize R ι i (chartMap R ι i (MvPolynomial.X j)) =
      MvPolynomial.X j
    rw [chartMap, MvPolynomial.aeval_X, dehomogenize_coordinateRatio]
  exact DFunLike.congr_fun h f

private lemma val_mk_prod [Fintype ι] (a : ℕ) (ai : ι → ℕ)
    (ha : (∏ j, (MvPolynomial.X j : Poly) ^ ai j) ∈ 𝒜 (a • 1)) :
    (Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R i) a
      (∏ j, (MvPolynomial.X j : Poly) ^ ai j) ha).val =
        Localization.mk (∏ j, (MvPolynomial.X j : Poly) ^ ai j)
          ⟨Xi ^ a, (Submonoid.mem_powers_iff _ _).mpr ⟨a, rfl⟩⟩ := by
  rfl

private lemma prod_X_mem [Fintype ι] (ai : ι → ℕ) :
    (∏ j, (MvPolynomial.X j : Poly) ^ ai j) ∈ 𝒜 (∑ j, ai j) := by
  simpa using SetLike.prod_pow_mem_graded 𝒜 (fun _ : ι ↦ 1)
    (MvPolynomial.X : ι → Poly) ai
    (F := Finset.univ) (fun j _ ↦ MvPolynomial.isHomogeneous_X R j)

private def monomialFraction [Fintype ι] (ai : ι → ℕ) : Chart :=
  Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R i) (∑ j, ai j)
    (∏ j, (MvPolynomial.X j : Poly) ^ ai j) (by
      simpa using prod_X_mem R ι ai)

private lemma chartMap_prod_eq_mk [Fintype ι] (a : ℕ) (ai : ι → ℕ)
    (hai : ∑ j, ai j = a)
    (ha : (∏ j, (MvPolynomial.X j : Poly) ^ ai j) ∈ 𝒜 a) :
    chartMap R ι i (∏ j : Others, MvPolynomial.X j ^ ai j.1) =
      Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R i) a
        (∏ j, (MvPolynomial.X j : Poly) ^ ai j) (by simpa using ha) := by
  apply HomogeneousLocalization.val_injective
  change (algebraMap Chart (Localization.Away Xi))
      (chartMap R ι i (∏ j : Others, MvPolynomial.X j ^ ai j.1)) =
    (Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R i) a
      (∏ j, (MvPolynomial.X j : Poly) ^ ai j) _).val
  rw [map_prod]
  simp only [map_pow, chartMap, MvPolynomial.aeval_X,
    HomogeneousLocalization.algebraMap_apply, val_mk_prod]
  change (algebraMap Chart (Localization.Away Xi))
    (∏ x, coordinateRatio R ι i x ^ ai x.1) = _
  rw [map_prod]
  simp only [map_pow, HomogeneousLocalization.algebraMap_apply,
    coordinateRatio_val]
  simp only [Localization.mk_pow, Localization.mk_prod]
  rw [Localization.mk_eq_mk_iff]
  rw [Localization.r_iff_of_le_nonZeroDivisors (R := Poly) (by
    rintro _ ⟨n, rfl⟩
    exact (MvPolynomial.isRegular_X (R := R) (σ := ι) (n := i)).pow n
      |>.mem_nonZeroDivisors)]
  simp only [Submonoid.coe_finsetProd, SubmonoidClass.coe_pow, pow_one]
  have hsum : a = ai i + ∑ j : Others, ai j.1 := by
    rw [← hai, sum_eq_self_add_others]
  have hden : (∏ j : Others, Xi ^ ai j.1) =
      Xi ^ (∑ j : Others, ai j.1) := by
    simpa using Finset.prod_pow_eq_pow_sum Finset.univ
      (fun j : Others ↦ ai j.1) Xi
  rw [hsum, pow_add, hden, prod_eq_self_mul_others ι i]
  ring

private lemma chartMap_prod_eq_monomialFraction [Fintype ι] (ai : ι → ℕ) :
    chartMap R ι i (∏ j : Others, MvPolynomial.X j ^ ai j.1) =
      monomialFraction R ι i ai := by
  apply chartMap_prod_eq_mk R ι i (∑ j, ai j) ai rfl
  exact prod_X_mem R ι ai

private lemma adjoin_monomialFraction_eq_top [Fintype ι] :
    Algebra.adjoin (𝒜 0) (Set.range (monomialFraction R ι i)) = ⊤ := by
  have hgen := Away.adjoin_mk_prod_pow_eq_top
    (f := Xi) (d := 1)
    (MvPolynomial.isHomogeneous_X R i) ι
    (MvPolynomial.X : ι → Poly) (adjoin_degreeZero_range_X_eq_top R ι)
    (fun _ : ι ↦ 1) (fun j ↦ MvPolynomial.isHomogeneous_X R j)
  apply top_unique
  rw [← hgen]
  apply Algebra.adjoin_mono
  rintro x ⟨a, ai, hai, hle, rfl⟩
  refine ⟨ai, ?_⟩
  have hs : ∑ j, ai j = a := by simpa using hai
  subst a
  rfl

/-- A total-degree-zero multivariable polynomial is the constant polynomial
given by its constant coefficient. -/
theorem zeroDegree_eq_C (r : 𝒜 0) :
    r.1 = MvPolynomial.C (r.1.coeff 0) := by
  apply (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := r.1)).1
  apply (MvPolynomial.totalDegree_zero_iff_isHomogeneous ι).2
  exact (MvPolynomial.mem_homogeneousSubmodule 0 r.1).1 r.2

private lemma zeroDegree_algebraMap_eq (r : 𝒜 0) :
    algebraMap (𝒜 0) Chart r =
      algebraMap R Chart (r.1.coeff 0) := by
  change fromZeroRingHom 𝒜 (Submonoid.powers Xi) r =
    coefficientHom R ι i (r.1.coeff 0)
  rw [coefficientHom]
  apply congrArg (fromZeroRingHom 𝒜 (Submonoid.powers Xi))
  apply Subtype.ext
  exact zeroDegree_eq_C R ι r

private lemma chartMap_surjective [Fintype ι] :
    Function.Surjective (chartMap R ι i) := by
  rw [← AlgHom.range_eq_top]
  apply top_unique
  intro x hxTop
  have hx : x ∈ Algebra.adjoin (𝒜 0)
      (Set.range (monomialFraction R ι i)) := by
    rw [adjoin_monomialFraction_eq_top]
    trivial
  clear hxTop
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨ai, rfl⟩ := hx
      refine ⟨∏ j : Others, MvPolynomial.X j ^ ai j.1, ?_⟩
      exact chartMap_prod_eq_monomialFraction R ι i ai
  | algebraMap r =>
      refine ⟨MvPolynomial.C (r.1.coeff 0), ?_⟩
      change chartMap R ι i (MvPolynomial.C (r.1.coeff 0)) =
        algebraMap (𝒜 0) Chart r
      rw [chartMap, MvPolynomial.aeval_C]
      exact (zeroDegree_algebraMap_eq R ι i r).symm
  | add x y hx hy hx' hy' => exact add_mem hx' hy'
  | mul x y hx hy hx' hy' => exact mul_mem hx' hy'

private lemma chartMap_injective : Function.Injective (chartMap R ι i) :=
  Function.LeftInverse.injective (dehomogenize_chartMap R ι i)

/-- The degree-zero homogeneous localization at `X i` is the polynomial ring
in the affine coordinates `X j / X i`, for `j ≠ i`. -/
@[expose] def standardChartEquiv [Fintype ι] : Q ≃ₐ[R] Chart :=
  AlgEquiv.ofBijective (MvPolynomial.aeval (coordinateRatio R ι i))
    ⟨by exact chartMap_injective R ι i, by exact chartMap_surjective R ι i⟩

private theorem standardChartEquiv_eq_privateConstruction [Fintype ι] :
    standardChartEquiv R ι i =
      AlgEquiv.ofBijective (chartMap R ι i)
        ⟨chartMap_injective R ι i, chartMap_surjective R ι i⟩ := by
  rfl

@[simp]
theorem standardChartEquiv_X [Fintype ι] (j : Others) :
    standardChartEquiv R ι i (MvPolynomial.X j) =
      coordinateRatio R ι i j := by
  change chartMap R ι i (MvPolynomial.X j) = coordinateRatio R ι i j
  rw [chartMap, MvPolynomial.aeval_X]

@[simp]
theorem standardChartEquiv_symm_coordinateRatio [Fintype ι] (j : Others) :
    (standardChartEquiv R ι i).symm (coordinateRatio R ι i j) =
      MvPolynomial.X j := by
  rw [← standardChartEquiv_X, AlgEquiv.symm_apply_apply]

/-- The affine dehomogenization of a homogeneous polynomial on the `i`th
standard chart, characterized by the fraction `F / X i ^ d`. -/
@[expose] def dehomogenizedPolynomial [Fintype ι] {d : ℕ} (F : Poly) (hF : F ∈ 𝒜 d) : Q :=
  (standardChartEquiv R ι i).symm
    (homogeneousPolynomialOnChart R ι i F hF)

@[simp]
theorem standardChartEquiv_dehomogenizedPolynomial [Fintype ι] {d : ℕ}
    (F : Poly) (hF : F ∈ 𝒜 d) :
    standardChartEquiv R ι i (dehomogenizedPolynomial R ι i F hF) =
      homogeneousPolynomialOnChart R ι i F hF := by
  exact (standardChartEquiv R ι i).apply_symm_apply _

/-- A homogeneous polynomial of fixed degree is determined by its affine
dehomogenization on any standard chart. -/
theorem dehomogenizedPolynomial_injective [Fintype ι] {d : ℕ} {F G : Poly}
    (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d)
    (h : dehomogenizedPolynomial R ι i F hF =
      dehomogenizedPolynomial R ι i G hG) :
    F = G := by
  apply homogeneousPolynomialOnChart_injective R ι i hF hG
  have := congrArg (standardChartEquiv R ι i) h
  simpa only [standardChartEquiv_dehomogenizedPolynomial] using this

/-- The coordinate ring of the overlap of the standard charts indexed by
`i` and `j`, presented as the degree-zero localization at `X i * X j`. -/
abbrev StandardChartOverlap (j : Others) :=
  Away 𝒜 (Xi * MvPolynomial.X j.1)

/-- Restriction from the `i`th standard chart to its overlap with the `j`th
standard chart. -/
@[expose] def standardChartOverlapMap (j : Others) :
    StandardChart R ι i →+* StandardChartOverlap R ι i j :=
  HomogeneousLocalization.awayMap 𝒜
    (f := Xi) (x := Xi * MvPolynomial.X j.1)
    (MvPolynomial.isHomogeneous_X R j.1) rfl

/-- The algebra structure on a chart overlap induced by restriction from the
`i`th chart. -/
instance standardChartOverlapAlgebra (j : Others) :
    Algebra (StandardChart R ι i) (StandardChartOverlap R ι i j) :=
  (standardChartOverlapMap R ι i j).toAlgebra

/-- The base-ring algebra structure on a chart overlap, induced through the
`i`th chart. -/
instance standardChartOverlapBaseAlgebra (j : Others) :
    Algebra R (StandardChartOverlap R ι i j) :=
  ((standardChartOverlapMap R ι i j).comp
    (algebraMap R (StandardChart R ι i))).toAlgebra

/-- Restriction to a chart overlap is compatible with the coefficient-ring
algebra structures. -/
instance standardChartOverlapIsScalarTower (j : Others) :
    IsScalarTower R (StandardChart R ι i)
      (StandardChartOverlap R ι i j) := by
  have h_chart (r : R) (x : StandardChart R ι i) :
      r • x = algebraMap R (StandardChart R ι i) r * x := by
    refine Quotient.ind' (fun q ↦ ?_) x
    change r • HomogeneousLocalization.mk q =
      coefficientHom R ι i r * HomogeneousLocalization.mk q
    apply HomogeneousLocalization.val_injective
    have hc : (coefficientHom R ι i r).val =
        Localization.mk (MvPolynomial.C r)
          (1 : Submonoid.powers (MvPolynomial.X i : MvPolynomial ι R)) := rfl
    rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_mk, hc, Localization.smul_mk,
      Localization.mk_mul]
    rw [MvPolynomial.smul_eq_C_mul]
    simp only [one_mul]
  have h_overlap (r : R) (z : StandardChartOverlap R ι i j) :
      r • z = algebraMap R (StandardChartOverlap R ι i j) r * z := by
    refine Quotient.ind' (fun q ↦ ?_) z
    change r • HomogeneousLocalization.mk q =
      algebraMap R (StandardChartOverlap R ι i j) r *
        HomogeneousLocalization.mk q
    apply HomogeneousLocalization.val_injective
    have hc :
        (algebraMap R (StandardChartOverlap R ι i j) r).val =
          Localization.mk (MvPolynomial.C r)
            (1 : Submonoid.powers
              ((MvPolynomial.X i : MvPolynomial ι R) * MvPolynomial.X j.1)) := by
      let a : 𝒜 0 :=
        ⟨MvPolynomial.C r,
          (MvPolynomial.mem_homogeneousSubmodule 0 _).2
            (MvPolynomial.isHomogeneous_C ι r)⟩
      have hj : (MvPolynomial.X j.1 : MvPolynomial ι R) ∈ 𝒜 1 :=
        (MvPolynomial.mem_homogeneousSubmodule 1 _).2
          (MvPolynomial.isHomogeneous_X R j.1)
      have h := HomogeneousLocalization.awayMap_fromZeroRingHom
        (f := (MvPolynomial.X i : MvPolynomial ι R)) 𝒜 hj rfl a
      change (standardChartOverlapMap R ι i j
        (coefficientHom R ι i r)).val = _
      change (standardChartOverlapMap R ι i j
        (HomogeneousLocalization.fromZeroRingHom 𝒜
          (Submonoid.powers (MvPolynomial.X i : MvPolynomial ι R)) a)).val = _
      have h' : standardChartOverlapMap R ι i j
          (HomogeneousLocalization.fromZeroRingHom 𝒜
            (Submonoid.powers (MvPolynomial.X i : MvPolynomial ι R)) a) =
          HomogeneousLocalization.fromZeroRingHom 𝒜
            (Submonoid.powers
              ((MvPolynomial.X i : MvPolynomial ι R) * MvPolynomial.X j.1)) a := by
        change HomogeneousLocalization.awayMap 𝒜 _ _
          (HomogeneousLocalization.fromZeroRingHom 𝒜
            (Submonoid.powers (MvPolynomial.X i : MvPolynomial ι R)) a) = _
        convert h using 1
      rw [h']
      rfl
    rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_mk, hc, Localization.smul_mk,
      Localization.mk_mul]
    rw [MvPolynomial.smul_eq_C_mul]
    simp only [one_mul]
  constructor
  intro r x y
  rw [h_chart, h_overlap, Algebra.smul_def, map_mul, Algebra.smul_def,
    mul_assoc]
  rw [show algebraMap R (StandardChartOverlap R ι i j) r =
      standardChartOverlapMap R ι i j
        (algebraMap R (StandardChart R ι i) r) from rfl]
  rw [show algebraMap (StandardChart R ι i)
      (StandardChartOverlap R ι i j) = standardChartOverlapMap R ι i j from rfl]

/-- The overlap with the `j`th standard chart is obtained from the `i`th
chart by inverting the affine coordinate `X j / X i`. -/
theorem isLocalization_standardChartOverlap (j : Others) :
    IsLocalization.Away (coordinateRatio R ι i j)
      (StandardChartOverlap R ι i j) := by
  have hr : coordinateRatio R ι i j =
      Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R i)
        (MvPolynomial.isHomogeneous_X R j.1) := by
    apply HomogeneousLocalization.val_injective
    simp [coordinateRatio, Away.isLocalizationElem]
  rw [hr]
  exact Away.isLocalization_mul (MvPolynomial.isHomogeneous_X R i)
    (MvPolynomial.isHomogeneous_X R j.1) rfl (by norm_num)

attribute [instance] isLocalization_standardChartOverlap

/-- The polynomial presentation of the overlap of the `i`th and `j`th
standard charts, obtained by inverting the variable representing `X j / X i`. -/
abbrev StandardChartPolynomialOverlap (j : Others) :=
  Localization.Away (MvPolynomial.X j : Q)

private theorem standardChartEquiv_map_powers [Fintype ι] (j : Others) :
    Submonoid.map (standardChartEquiv R ι i).toRingEquiv.toMonoidHom
        (Submonoid.powers (MvPolynomial.X j : Q)) =
      Submonoid.powers (coordinateRatio R ι i j) := by
  rw [Submonoid.map_powers]
  congr 1
  exact standardChartEquiv_X R ι i j

/-- The polynomial chart presentation localized at `X j / X i` agrees with
the degree-zero homogeneous localization at `X i * X j`. -/
@[expose] noncomputable def standardChartPolynomialOverlapEquiv [Fintype ι] (j : Others) :
    StandardChartPolynomialOverlap R ι i j ≃ₐ[R]
      StandardChartOverlap R ι i j where
  __ := IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (MvPolynomial.X j : Q))
    (T := Submonoid.powers (coordinateRatio R ι i j))
    (StandardChartPolynomialOverlap R ι i j)
    (StandardChartOverlap R ι i j)
    (standardChartEquiv R ι i).toRingEquiv
    (by
      rw [Submonoid.map_powers]
      congr 1
      exact standardChartEquiv_X R ι i j)
  commutes' r := by
    change IsLocalization.ringEquivOfRingEquiv
        (M := Submonoid.powers (MvPolynomial.X j : Q))
        (T := Submonoid.powers (coordinateRatio R ι i j))
        (StandardChartPolynomialOverlap R ι i j)
        (StandardChartOverlap R ι i j)
        (standardChartEquiv R ι i).toRingEquiv
        (standardChartEquiv_map_powers R ι i j)
        (algebraMap Q (StandardChartPolynomialOverlap R ι i j)
          (MvPolynomial.C r)) =
      standardChartOverlapMap R ι i j
        (algebraMap R (StandardChart R ι i) r)
    rw [IsLocalization.ringEquivOfRingEquiv_eq]
    congr 1
    exact (standardChartEquiv R ι i).commutes r

private theorem standardChartPolynomialOverlapEquiv_eq_privateConstruction
    [Fintype ι] (j : Others) :
    (standardChartPolynomialOverlapEquiv R ι i j).toRingEquiv =
      IsLocalization.ringEquivOfRingEquiv
        (M := Submonoid.powers (MvPolynomial.X j : Q))
        (T := Submonoid.powers (coordinateRatio R ι i j))
        (StandardChartPolynomialOverlap R ι i j)
        (StandardChartOverlap R ι i j)
        (standardChartEquiv R ι i).toRingEquiv
        (standardChartEquiv_map_powers R ι i j) := by
  rfl

/-- The polynomial-overlap equivalence intertwines the polynomial
localization map with restriction from the homogeneous standard chart. -/
theorem standardChartPolynomialOverlapEquiv_algebraMap [Fintype ι]
    (j : Others) (f : Q) :
    standardChartPolynomialOverlapEquiv R ι i j
        (algebraMap Q (StandardChartPolynomialOverlap R ι i j) f) =
      standardChartOverlapMap R ι i j (standardChartEquiv R ι i f) := by
  change IsLocalization.ringEquivOfRingEquiv
      (M := Submonoid.powers (MvPolynomial.X j : Q))
      (T := Submonoid.powers (coordinateRatio R ι i j))
      (StandardChartPolynomialOverlap R ι i j)
      (StandardChartOverlap R ι i j)
      (standardChartEquiv R ι i).toRingEquiv
      (standardChartEquiv_map_powers R ι i j)
      (algebraMap Q (StandardChartPolynomialOverlap R ι i j) f) =
    algebraMap (StandardChart R ι i) (StandardChartOverlap R ι i j)
      (standardChartEquiv R ι i f)
  apply IsLocalization.ringEquivOfRingEquiv_eq

@[simp]
theorem standardChartPolynomialOverlapEquiv_X [Fintype ι]
    (j k : Others) :
    standardChartPolynomialOverlapEquiv R ι i j
        (algebraMap Q (StandardChartPolynomialOverlap R ι i j)
          (MvPolynomial.X k)) =
      standardChartOverlapMap R ι i j (coordinateRatio R ι i k) := by
  rw [standardChartPolynomialOverlapEquiv_algebraMap,
    standardChartEquiv_X]

/-- Restriction from the `j`th standard chart to the overlap with the `i`th
chart, using the same ordered presentation `X i * X j` as
`standardChartOverlapMap`. -/
@[expose] def standardChartOverlapMapRight (j : Others) :
    StandardChart R ι j.1 →+* StandardChartOverlap R ι i j :=
  HomogeneousLocalization.awayMap 𝒜
    (f := MvPolynomial.X j.1) (x := Xi * MvPolynomial.X j.1)
    (MvPolynomial.isHomogeneous_X R i) (by rw [mul_comm])

/-- The algebra structure on a chart overlap induced by restriction from the
`j`th chart. -/
instance standardChartOverlapAlgebraRight (j : Others) :
    Algebra (StandardChart R ι j.1) (StandardChartOverlap R ι i j) :=
  (standardChartOverlapMapRight R ι i j).toAlgebra

/-- Viewed from the `j`th chart, the overlap is obtained by inverting
`X i / X j`. -/
theorem isLocalization_standardChartOverlap_right (j : Others) :
    IsLocalization.Away
      (coordinateRatio R ι j.1 ⟨i, Ne.symm j.2⟩)
      (StandardChartOverlap R ι i j) := by
  have hr : coordinateRatio R ι j.1 ⟨i, Ne.symm j.2⟩ =
      Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R j.1)
        (MvPolynomial.isHomogeneous_X R i) := by
    apply HomogeneousLocalization.val_injective
    simp [coordinateRatio, Away.isLocalizationElem]
  rw [hr]
  exact Away.isLocalization_mul (MvPolynomial.isHomogeneous_X R j.1)
    (MvPolynomial.isHomogeneous_X R i) (by rw [mul_comm]) (by norm_num)

attribute [instance] isLocalization_standardChartOverlap_right

/-- Restriction from the right chart sends coefficients to the same elements
of the common overlap as restriction from the left chart. -/
theorem standardChartOverlapMapRight_algebraMap (j : Others) (r : R) :
    standardChartOverlapMapRight R ι i j
        (algebraMap R (StandardChart R ι j.1) r) =
      algebraMap R (StandardChartOverlap R ι i j) r := by
  let a : 𝒜 0 :=
    ⟨MvPolynomial.C r,
      (MvPolynomial.mem_homogeneousSubmodule 0 _).2
        (MvPolynomial.isHomogeneous_C ι r)⟩
  have hi : Xi ∈ 𝒜 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 _).2
      (MvPolynomial.isHomogeneous_X R i)
  have hj : (MvPolynomial.X j.1 : Poly) ∈ 𝒜 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 _).2
      (MvPolynomial.isHomogeneous_X R j.1)
  change HomogeneousLocalization.awayMap 𝒜 hi (by rw [mul_comm])
        (HomogeneousLocalization.fromZeroRingHom 𝒜
          (Submonoid.powers (MvPolynomial.X j.1 : Poly)) a) =
    HomogeneousLocalization.awayMap 𝒜 hj rfl
        (HomogeneousLocalization.fromZeroRingHom 𝒜
          (Submonoid.powers Xi) a)
  rw [HomogeneousLocalization.awayMap_fromZeroRingHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom]

/-- The polynomial presentation of the same overlap, viewed from the `j`th
chart by inverting the variable representing `X i / X j`. -/
abbrev StandardChartPolynomialOverlapRight (j : Others) :=
  Localization.Away
    (MvPolynomial.X (⟨i, Ne.symm j.2⟩ : {k : ι // k ≠ j.1}) :
      MvPolynomial {k : ι // k ≠ j.1} R)

private theorem standardChartEquiv_map_powers_right [Fintype ι]
    (j : Others) :
    Submonoid.map (standardChartEquiv R ι j.1).toRingEquiv.toMonoidHom
        (Submonoid.powers
          (MvPolynomial.X (⟨i, Ne.symm j.2⟩ : {k : ι // k ≠ j.1}) :
            MvPolynomial {k : ι // k ≠ j.1} R)) =
      Submonoid.powers
        (coordinateRatio R ι j.1 ⟨i, Ne.symm j.2⟩) := by
  rw [Submonoid.map_powers]
  congr 1
  exact standardChartEquiv_X R ι j.1 ⟨i, Ne.symm j.2⟩

/-- The polynomial chart presentation from the `j`th side of an overlap agrees
with the common degree-zero homogeneous localization at `X i * X j`. -/
private noncomputable def standardChartPolynomialOverlapRingEquivRight [Fintype ι]
    (j : Others) :
    StandardChartPolynomialOverlapRight R ι i j ≃+*
      StandardChartOverlap R ι i j :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers
      (MvPolynomial.X (⟨i, Ne.symm j.2⟩ : {k : ι // k ≠ j.1}) :
        MvPolynomial {k : ι // k ≠ j.1} R))
    (T := Submonoid.powers
      (coordinateRatio R ι j.1 ⟨i, Ne.symm j.2⟩))
    (StandardChartPolynomialOverlapRight R ι i j)
    (StandardChartOverlap R ι i j)
    (standardChartEquiv R ι j.1).toRingEquiv
    (standardChartEquiv_map_powers_right R ι i j)

/-- The right polynomial-overlap presentation intertwines its localization map
with restriction from the `j`th homogeneous standard chart. -/
private theorem standardChartPolynomialOverlapRingEquivRight_algebraMap [Fintype ι]
    (j : Others) (f : MvPolynomial {k : ι // k ≠ j.1} R) :
    standardChartPolynomialOverlapRingEquivRight R ι i j
        (algebraMap (MvPolynomial {k : ι // k ≠ j.1} R)
          (StandardChartPolynomialOverlapRight R ι i j) f) =
      standardChartOverlapMapRight R ι i j
        (standardChartEquiv R ι j.1 f) := by
  change IsLocalization.ringEquivOfRingEquiv
      (M := Submonoid.powers
        (MvPolynomial.X (⟨i, Ne.symm j.2⟩ : {k : ι // k ≠ j.1}) :
          MvPolynomial {k : ι // k ≠ j.1} R))
      (T := Submonoid.powers
        (coordinateRatio R ι j.1 ⟨i, Ne.symm j.2⟩))
      (StandardChartPolynomialOverlapRight R ι i j)
      (StandardChartOverlap R ι i j)
      (standardChartEquiv R ι j.1).toRingEquiv
      (standardChartEquiv_map_powers_right R ι i j)
      (algebraMap (MvPolynomial {k : ι // k ≠ j.1} R)
        (StandardChartPolynomialOverlapRight R ι i j) f) =
    algebraMap (StandardChart R ι j.1) (StandardChartOverlap R ι i j)
      (standardChartEquiv R ι j.1 f)
  apply IsLocalization.ringEquivOfRingEquiv_eq

/-- The polynomial presentation from the `j`th side of an overlap is an
equivalence of algebras over the coefficient ring. -/
@[expose] noncomputable def standardChartPolynomialOverlapEquivRight [Fintype ι]
    (j : Others) :
    StandardChartPolynomialOverlapRight R ι i j ≃ₐ[R]
      StandardChartOverlap R ι i j where
  __ := IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers
      (MvPolynomial.X (⟨i, Ne.symm j.2⟩ : {k : ι // k ≠ j.1}) :
        MvPolynomial {k : ι // k ≠ j.1} R))
    (T := Submonoid.powers
      (coordinateRatio R ι j.1 ⟨i, Ne.symm j.2⟩))
    (StandardChartPolynomialOverlapRight R ι i j)
    (StandardChartOverlap R ι i j)
    (standardChartEquiv R ι j.1).toRingEquiv
    (by
      rw [Submonoid.map_powers]
      congr 1
      exact standardChartEquiv_X R ι j.1 ⟨i, Ne.symm j.2⟩)
  commutes' r := by
    change standardChartPolynomialOverlapRingEquivRight R ι i j
        (algebraMap (MvPolynomial {k : ι // k ≠ j.1} R)
          (StandardChartPolynomialOverlapRight R ι i j)
          (MvPolynomial.C r)) = _
    rw [standardChartPolynomialOverlapRingEquivRight_algebraMap]
    change standardChartOverlapMapRight R ι i j
        (standardChartEquiv R ι j.1
          (algebraMap R (MvPolynomial {k : ι // k ≠ j.1} R) r)) = _
    rw [(standardChartEquiv R ι j.1).commutes]
    exact standardChartOverlapMapRight_algebraMap R ι i j r

private theorem standardChartPolynomialOverlapEquivRight_eq_privateConstruction
    [Fintype ι] (j : Others) :
    (standardChartPolynomialOverlapEquivRight R ι i j).toRingEquiv =
      standardChartPolynomialOverlapRingEquivRight R ι i j := by
  rfl

/-- The right polynomial-overlap equivalence intertwines its localization map
with restriction from the `j`th homogeneous standard chart. -/
theorem standardChartPolynomialOverlapEquivRight_algebraMap [Fintype ι]
    (j : Others) (f : MvPolynomial {k : ι // k ≠ j.1} R) :
    standardChartPolynomialOverlapEquivRight R ι i j
        (algebraMap (MvPolynomial {k : ι // k ≠ j.1} R)
          (StandardChartPolynomialOverlapRight R ι i j) f) =
      standardChartOverlapMapRight R ι i j
        (standardChartEquiv R ι j.1 f) := by
  exact standardChartPolynomialOverlapRingEquivRight_algebraMap R ι i j f

@[simp]
theorem standardChartPolynomialOverlapEquivRight_X [Fintype ι]
    (j : Others) (k : {k : ι // k ≠ j.1}) :
    standardChartPolynomialOverlapEquivRight R ι i j
        (algebraMap (MvPolynomial {k : ι // k ≠ j.1} R)
          (StandardChartPolynomialOverlapRight R ι i j)
          (MvPolynomial.X k)) =
      standardChartOverlapMapRight R ι i j
        (coordinateRatio R ι j.1 k) := by
  rw [standardChartPolynomialOverlapEquivRight_algebraMap,
    standardChartEquiv_X]

/-- The two polynomial presentations of a standard-chart overlap are
canonically equivalent through their common homogeneous localization. -/
@[expose] noncomputable def standardChartPolynomialTransition [Fintype ι] (j : Others) :
    StandardChartPolynomialOverlap R ι i j ≃ₐ[R]
      StandardChartPolynomialOverlapRight R ι i j :=
  (standardChartPolynomialOverlapEquiv R ι i j).trans
    (standardChartPolynomialOverlapEquivRight R ι i j).symm

/-- After identifying the target polynomial overlap with the common
homogeneous localization, the transition is restriction from the `i`th chart. -/
theorem standardChartPolynomialOverlapEquivRight_transition_algebraMap
    [Fintype ι] (j : Others) (f : Q) :
    standardChartPolynomialOverlapEquivRight R ι i j
        (standardChartPolynomialTransition R ι i j
          (algebraMap Q (StandardChartPolynomialOverlap R ι i j) f)) =
      standardChartOverlapMap R ι i j (standardChartEquiv R ι i f) := by
  simp only [standardChartPolynomialTransition, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply]
  exact standardChartPolynomialOverlapEquiv_algebraMap R ι i j f

@[simp]
theorem standardChartPolynomialOverlapEquivRight_transition_X [Fintype ι]
    (j k : Others) :
    standardChartPolynomialOverlapEquivRight R ι i j
        (standardChartPolynomialTransition R ι i j
          (algebraMap Q (StandardChartPolynomialOverlap R ι i j)
            (MvPolynomial.X k))) =
      standardChartOverlapMap R ι i j (coordinateRatio R ι i k) := by
  rw [standardChartPolynomialOverlapEquivRight_transition_algebraMap,
    standardChartEquiv_X]

/-- In the right polynomial presentation of an overlap, the unit corresponding
to the left transition coordinate `X j / X i`. -/
@[expose] def standardChartPolynomialTransitionUnit [Fintype ι] (j : Others) :
    StandardChartPolynomialOverlapRight R ι i j :=
  (standardChartPolynomialOverlapEquivRight R ι i j).symm
    (standardChartOverlapMap R ι i j (coordinateRatio R ι i j))

@[simp]
theorem standardChartPolynomialOverlapEquivRight_transitionUnit [Fintype ι]
    (j : Others) :
    standardChartPolynomialOverlapEquivRight R ι i j
        (standardChartPolynomialTransitionUnit R ι i j) =
      standardChartOverlapMap R ι i j (coordinateRatio R ι i j) := by
  exact (standardChartPolynomialOverlapEquivRight R ι i j).apply_symm_apply _

/-- On the overlap of the `i`th and `j`th standard charts, the coordinate
ratios `X j / X i` and `X i / X j` are inverse. -/
theorem standardChartTransition_inverse (j : Others) :
    standardChartOverlapMap R ι i j (coordinateRatio R ι i j) *
      standardChartOverlapMapRight R ι i j
        (coordinateRatio R ι j.1 ⟨i, Ne.symm j.2⟩) = 1 := by
  rw [show standardChartOverlapMap R ι i j
      (coordinateRatio R ι i j) = _ from by
    simpa [standardChartOverlapMap, coordinateRatio] using
      (HomogeneousLocalization.awayMap_mk 𝒜
        (MvPolynomial.isHomogeneous_X R j.1) rfl 1
        (MvPolynomial.isHomogeneous_X R i) (MvPolynomial.X j.1)
        (by simpa using MvPolynomial.isHomogeneous_X R j.1))]
  rw [show standardChartOverlapMapRight R ι i j
      (coordinateRatio R ι j.1 ⟨i, Ne.symm j.2⟩) = _ from by
    simpa [coordinateRatio, standardChartOverlapMapRight] using
      (HomogeneousLocalization.awayMap_mk 𝒜
        (MvPolynomial.isHomogeneous_X R i) (by rw [mul_comm]) 1
        (MvPolynomial.isHomogeneous_X R j.1) Xi
        (by simpa using MvPolynomial.isHomogeneous_X R i))]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- The right-presentation element corresponding to `X j / X i` is a unit. -/
theorem isUnit_standardChartPolynomialTransitionUnit [Fintype ι]
    (j : Others) :
    IsUnit (standardChartPolynomialTransitionUnit R ι i j) := by
  have h : IsUnit
      (standardChartOverlapMap R ι i j (coordinateRatio R ι i j)) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨standardChartOverlapMapRight R ι i j
      (coordinateRatio R ι j.1 ⟨i, Ne.symm j.2⟩), ?_⟩
    exact standardChartTransition_inverse R ι i j
  exact h.map
    (standardChartPolynomialOverlapEquivRight R ι i j).symm.toAlgHom

/-- The coordinate-change identity `X k / X j · X j / X i = X k / X i`
on the overlap of the `i`th and `j`th standard charts. -/
theorem standardChartTransition_other (j : Others) (k : ι)
    (hki : k ≠ i) (hkj : k ≠ j.1) :
    standardChartOverlapMapRight R ι i j
        (coordinateRatio R ι j.1 ⟨k, hkj⟩) *
      standardChartOverlapMap R ι i j (coordinateRatio R ι i j) =
      standardChartOverlapMap R ι i j
        (coordinateRatio R ι i ⟨k, hki⟩) := by
  rw [show standardChartOverlapMapRight R ι i j
      (coordinateRatio R ι j.1 ⟨k, hkj⟩) = _ from by
    simpa [coordinateRatio, standardChartOverlapMapRight] using
      (HomogeneousLocalization.awayMap_mk 𝒜
        (MvPolynomial.isHomogeneous_X R i) (by rw [mul_comm]) 1
        (MvPolynomial.isHomogeneous_X R j.1) (MvPolynomial.X k)
        (by simpa using MvPolynomial.isHomogeneous_X R k))]
  rw [show standardChartOverlapMap R ι i j
      (coordinateRatio R ι i j) = _ from by
    simpa [standardChartOverlapMap, coordinateRatio] using
      (HomogeneousLocalization.awayMap_mk 𝒜
        (MvPolynomial.isHomogeneous_X R j.1) rfl 1
        (MvPolynomial.isHomogeneous_X R i) (MvPolynomial.X j.1)
        (by simpa using MvPolynomial.isHomogeneous_X R j.1))]
  rw [show standardChartOverlapMap R ι i j
      (coordinateRatio R ι i ⟨k, hki⟩) = _ from by
    simpa [standardChartOverlapMap, coordinateRatio] using
      (HomogeneousLocalization.awayMap_mk 𝒜
        (MvPolynomial.isHomogeneous_X R j.1) rfl 1
        (MvPolynomial.isHomogeneous_X R i) (MvPolynomial.X k)
        (by simpa using MvPolynomial.isHomogeneous_X R k))]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- The transition between two polynomial chart presentations sends the
coordinate pointing at the target chart to the distinguished transition
unit. -/
theorem standardChartPolynomialTransition_self [Fintype ι] (j : Others) :
    standardChartPolynomialTransition R ι i j
        (algebraMap Q (StandardChartPolynomialOverlap R ι i j)
          (MvPolynomial.X j)) =
      standardChartPolynomialTransitionUnit R ι i j := by
  let _ : Algebra R (StandardChartOverlap R ι i j) :=
    standardChartOverlapBaseAlgebra R ι i j
  apply (standardChartPolynomialOverlapEquivRight R ι i j).injective
  rw [standardChartPolynomialOverlapEquivRight_transition_X,
    standardChartPolynomialOverlapEquivRight_transitionUnit]

/-- The transition unit is inverse to the variable inverted in the target
polynomial chart presentation. -/
theorem standardChartPolynomialTransitionUnit_mul_variable [Fintype ι]
    (j : Others) :
    standardChartPolynomialTransitionUnit R ι i j *
        algebraMap (MvPolynomial {k : ι // k ≠ j.1} R)
          (StandardChartPolynomialOverlapRight R ι i j)
          (MvPolynomial.X ⟨i, Ne.symm j.2⟩) = 1 := by
  let _ : Algebra R (StandardChartOverlap R ι i j) :=
    standardChartOverlapBaseAlgebra R ι i j
  apply (standardChartPolynomialOverlapEquivRight R ι i j).injective
  rw [map_mul, map_one,
    standardChartPolynomialOverlapEquivRight_transitionUnit,
    standardChartPolynomialOverlapEquivRight_X]
  exact standardChartTransition_inverse R ι i j

/-- In polynomial coordinates, transition carries `X k / X i` to
`(X k / X j) * (X j / X i)`. -/
theorem standardChartPolynomialTransition_other [Fintype ι] (j : Others)
    (k : ι) (hki : k ≠ i) (hkj : k ≠ j.1) :
    standardChartPolynomialTransition R ι i j
        (algebraMap Q (StandardChartPolynomialOverlap R ι i j)
          (MvPolynomial.X ⟨k, hki⟩)) =
      algebraMap (MvPolynomial {l : ι // l ≠ j.1} R)
          (StandardChartPolynomialOverlapRight R ι i j)
          (MvPolynomial.X ⟨k, hkj⟩) *
        standardChartPolynomialTransitionUnit R ι i j := by
  let _ : Algebra R (StandardChartOverlap R ι i j) :=
    standardChartOverlapBaseAlgebra R ι i j
  apply (standardChartPolynomialOverlapEquivRight R ι i j).injective
  rw [map_mul, standardChartPolynomialOverlapEquivRight_transition_X,
    standardChartPolynomialOverlapEquivRight_X,
    standardChartPolynomialOverlapEquivRight_transitionUnit]
  exact (standardChartTransition_other R ι i j k hki hkj).symm

end ProjectiveSpace
