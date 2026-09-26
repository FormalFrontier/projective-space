/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Contributors: Atlas and Formal Frontier contributors (AI-assisted)
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous-coordinate points of polynomial projective space

For a nonzero vector `a : ι → k` over a field, this file packages the kernel
of the map `X i ↦ a i * t` as a relevant homogeneous prime of the polynomial
ring. It therefore defines a point of polynomial `Proj`. The construction is
unchanged by nonzero scalar multiplication and descends to the vector-space
projectivization.

No finiteness or decidable-equality hypothesis on `ι` is needed.
-/

@[expose] public section

noncomputable section

namespace ProjectiveSpace

universe u v

variable {k : Type u} [Field k] {ι : Type v}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The graded cone-line evaluation map attached to a homogeneous-coordinate
vector: it sends `X i` to `a i * t`. -/
noncomputable def homogeneousCoordinateMap (a : ι → k) :
    MvPolynomial ι k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval (fun i ↦ Polynomial.C (a i) * Polynomial.X)

@[simp]
theorem homogeneousCoordinateMap_X (a : ι → k) (i : ι) :
    homogeneousCoordinateMap a (MvPolynomial.X i) =
      Polynomial.C (a i) * Polynomial.X := by
  simp [homogeneousCoordinateMap]

/-- The homogeneous-coordinate ideal represented by `a`. It is the kernel of
the cone-line evaluation map `X i ↦ a i * t`. -/
noncomputable def homogeneousCoordinateIdeal (a : ι → k) :
    Ideal (MvPolynomial ι k) :=
  RingHom.ker (homogeneousCoordinateMap a).toRingHom

/-- A homogeneous-coordinate ideal over a field is prime. -/
theorem homogeneousCoordinateIdeal_isPrime (a : ι → k) :
    (homogeneousCoordinateIdeal a).IsPrime := by
  exact RingHom.ker_isPrime (homogeneousCoordinateMap a).toRingHom

/-- A coordinate whose value is nonzero does not belong to the corresponding
homogeneous-coordinate ideal. -/
theorem X_not_mem_homogeneousCoordinateIdeal (a : ι → k) (i : ι)
    (hi : a i ≠ 0) :
    MvPolynomial.X i ∉ homogeneousCoordinateIdeal a := by
  rw [homogeneousCoordinateIdeal, RingHom.mem_ker]
  simp [homogeneousCoordinateMap, hi]

private theorem homogeneousCoordinateMap_monomial (a : ι → k)
    (s : ι →₀ ℕ) (r : k) :
    homogeneousCoordinateMap a (MvPolynomial.monomial s r) =
      Polynomial.C (r * s.prod fun i e ↦ a i ^ e) *
        Polynomial.X ^ s.degree := by
  rw [homogeneousCoordinateMap, MvPolynomial.aeval_monomial]
  simp only [map_mul, mul_pow]
  rw [Finsupp.prod, Finset.prod_mul_distrib]
  have hc : (∏ x ∈ s.support, Polynomial.C (a x) ^ s x) =
      Polynomial.C (∏ x ∈ s.support, a x ^ s x) := by
    symm
    simpa only [map_pow] using
      (map_prod (Polynomial.C : k →+* Polynomial k)
        (fun x ↦ a x ^ s x) s.support)
  rw [hc, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply, mul_assoc]
  simp [Finsupp.prod]

/-- On a homogeneous polynomial of degree `d`, cone-line evaluation is
ordinary evaluation times `t^d`. -/
theorem homogeneousCoordinateMap_of_isHomogeneous (a : ι → k)
    {F : MvPolynomial ι k} {d : ℕ} (hF : F.IsHomogeneous d) :
    homogeneousCoordinateMap a F =
      Polynomial.C (MvPolynomial.eval a F) * Polynomial.X ^ d := by
  have degree_eq {s : ι →₀ ℕ} (hs : s ∈ F.support) : s.degree = d := by
    by_contra hsd
    exact (Finsupp.mem_support_iff.mp hs) (hF.coeff_eq_zero hsd)
  calc
    homogeneousCoordinateMap a F =
        ∑ s ∈ F.support,
          homogeneousCoordinateMap a (MvPolynomial.monomial s (F.coeff s)) := by
      rw [← map_sum]
      exact congrArg (homogeneousCoordinateMap a) F.as_sum
    _ = ∑ s ∈ F.support,
        Polynomial.C (F.coeff s * s.prod fun i e ↦ a i ^ e) *
          Polynomial.X ^ d := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [homogeneousCoordinateMap_monomial, degree_eq hs]
    _ = Polynomial.C
          (∑ s ∈ F.support, F.coeff s * s.prod fun i e ↦ a i ^ e) *
        Polynomial.X ^ d := by
      rw [map_sum, Finset.sum_mul]
    _ = Polynomial.C (MvPolynomial.eval a F) * Polynomial.X ^ d := by
      congr 2

/-- A homogeneous polynomial belongs to the homogeneous-coordinate ideal
exactly when it vanishes at the representing vector. -/
theorem mem_homogeneousCoordinateIdeal_iff_eval_eq_zero (a : ι → k)
    {F : MvPolynomial ι k} {d : ℕ} (hF : F.IsHomogeneous d) :
    F ∈ homogeneousCoordinateIdeal a ↔ MvPolynomial.eval a F = 0 := by
  rw [homogeneousCoordinateIdeal, RingHom.mem_ker]
  change homogeneousCoordinateMap a F = 0 ↔ MvPolynomial.eval a F = 0
  rw [homogeneousCoordinateMap_of_isHomogeneous a hF]
  simp

private theorem coeff_homogeneousCoordinateMap (a : ι → k)
    (F : MvPolynomial ι k) (d : ℕ) :
    (homogeneousCoordinateMap a F).coeff d =
      MvPolynomial.eval a (MvPolynomial.homogeneousComponent d F) := by
  rw [MvPolynomial.homogeneousComponent_apply, map_sum]
  have hmap : homogeneousCoordinateMap a F =
      ∑ s ∈ F.support,
        homogeneousCoordinateMap a (MvPolynomial.monomial s (F.coeff s)) := by
    rw [← map_sum]
    exact congrArg (homogeneousCoordinateMap a) F.as_sum
  rw [hmap]
  simp only [MvPolynomial.eval_monomial]
  rw [Finset.sum_filter, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro s hs
  rw [homogeneousCoordinateMap_monomial, Polynomial.coeff_C_mul_X_pow]
  by_cases hsd : s.degree = d
  · simp [hsd]
  · have hds : d ≠ s.degree := Ne.symm hsd
    simp [hsd, hds]

/-- The homogeneous-coordinate ideal is homogeneous for the total-degree
grading. -/
theorem homogeneousCoordinateIdeal_isHomogeneous (a : ι → k) :
    Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι k)
      (homogeneousCoordinateIdeal a) := by
  intro d F hF
  rw [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply]
  have hmap : homogeneousCoordinateMap a F = 0 := by
    change (homogeneousCoordinateMap a).toRingHom F = 0
    exact hF
  apply (mem_homogeneousCoordinateIdeal_iff_eval_eq_zero
    (F := MvPolynomial.homogeneousComponent d F) (d := d) a
    (MvPolynomial.homogeneousComponent_isHomogeneous d F)).2
  rw [← coeff_homogeneousCoordinateMap a F d, hmap]
  simp

/-- The homogeneous-coordinate ideal bundled as a homogeneous ideal. -/
noncomputable def homogeneousCoordinateHomogeneousIdeal (a : ι → k) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule ι k) :=
  ⟨homogeneousCoordinateIdeal a, homogeneousCoordinateIdeal_isHomogeneous a⟩

/-- A nonzero coordinate vector defines a relevant homogeneous ideal. -/
theorem irrelevant_not_le_homogeneousCoordinateHomogeneousIdeal
    (a : ι → k) (ha : a ≠ 0) :
    ¬HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι k) ≤
      homogeneousCoordinateHomogeneousIdeal a := by
  intro hle
  have hex : ∃ i, a i ≠ 0 := by
    by_contra h
    apply ha
    funext i
    simp only [not_exists, not_not] at h
    exact h i
  obtain ⟨i, hi⟩ := hex
  exact X_not_mem_homogeneousCoordinateIdeal a i hi <| hle <|
    HomogeneousIdeal.mem_irrelevant_of_mem
      (MvPolynomial.homogeneousSubmodule ι k) Nat.zero_lt_one
      (MvPolynomial.isHomogeneous_X (R := k) i)

/-- The point of polynomial projective spectrum represented by nonzero
homogeneous coordinates. -/
noncomputable def homogeneousCoordinatePoint (a : ι → k) (ha : a ≠ 0) :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ι k) where
  asHomogeneousIdeal := homogeneousCoordinateHomogeneousIdeal a
  isPrime := homogeneousCoordinateIdeal_isPrime a
  not_irrelevant_le :=
    irrelevant_not_le_homogeneousCoordinateHomogeneousIdeal a ha

/-- Scaling all coordinates acts on the cone-line parameter by composition. -/
theorem homogeneousCoordinateMap_smul (a : ι → k) (c : k)
    (F : MvPolynomial ι k) :
    homogeneousCoordinateMap (c • a) F =
      (homogeneousCoordinateMap a F).comp
        (Polynomial.C c * Polynomial.X) := by
  have h : homogeneousCoordinateMap (c • a) =
      (Polynomial.aeval (Polynomial.C c * Polynomial.X)).comp
        (homogeneousCoordinateMap a) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [homogeneousCoordinateMap, mul_assoc]
    ac_rfl
  simpa [Polynomial.comp_eq_aeval] using DFunLike.congr_fun h F

/-- Multiplying all coordinates by a nonzero scalar does not change their
homogeneous-coordinate ideal. -/
theorem homogeneousCoordinateIdeal_smul (a : ι → k) (c : k) (hc : c ≠ 0) :
    homogeneousCoordinateIdeal (c • a) = homogeneousCoordinateIdeal a := by
  ext F
  simp only [homogeneousCoordinateIdeal, RingHom.mem_ker]
  change homogeneousCoordinateMap (c • a) F = 0 ↔
    homogeneousCoordinateMap a F = 0
  rw [homogeneousCoordinateMap_smul]
  exact Polynomial.comp_C_mul_X_eq_zero_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr hc)

/-- Two nonzero vectors related by scalar multiplication define the same
point of polynomial projective spectrum. -/
theorem homogeneousCoordinatePoint_eq_of_eq_smul
    (a b : ι → k) (ha : a ≠ 0) (hb : b ≠ 0) (c : k)
    (hab : a = c • b) :
    homogeneousCoordinatePoint a ha = homogeneousCoordinatePoint b hb := by
  have hc : c ≠ 0 := by
    intro hc
    apply ha
    rw [hab, hc, zero_smul]
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  change homogeneousCoordinateIdeal a = homogeneousCoordinateIdeal b
  rw [hab]
  exact homogeneousCoordinateIdeal_smul b c hc

/-- Map vector-space projectivization into polynomial projective spectrum by
the homogeneous-coordinate ideal. -/
noncomputable def projectivizationToProj :
    Projectivization k (ι → k) →
      ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ι k) :=
  Projectivization.lift
    (fun a ↦ homogeneousCoordinatePoint a.1 a.2)
    (fun a b c hab ↦
      homogeneousCoordinatePoint_eq_of_eq_smul a.1 b.1 a.2 b.2 c hab)

@[simp]
theorem projectivizationToProj_mk (a : ι → k) (ha : a ≠ 0) :
    projectivizationToProj (Projectivization.mk k a ha) =
      homogeneousCoordinatePoint a ha :=
  rfl

end ProjectiveSpace
