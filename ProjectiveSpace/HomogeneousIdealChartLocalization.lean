/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.HomogeneousIdealChart
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Localizing homogeneous-equation chart quotients

This file identifies the quotient presentation of a projective-chart overlap
with the localization of the corresponding chart quotient.
-/

public section

noncomputable section

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v w

variable (R : Type u) [CommRing R]
variable (ι : Type v) (i : ι)

/-- Classical coordinate equality, scoped to homogeneous-ideal localization. -/
local instance instDecidableEqHomogeneousIdealLocalizationCoordinates : DecidableEq ι := Classical.decEq ι

local notation "Others" => {j : ι // j ≠ i}
local notation "Q" => MvPolynomial Others R
local notation "Poly" => MvPolynomial ι R
local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

/-- The canonical map from a chart quotient to its overlap quotient. -/
@[expose] noncomputable def standardChartHomogeneousIdealOverlapMap [Fintype ι]
    (j : Others) (κ : Type w) (d : κ → ℕ) (F : κ → Poly)
    (hF : ∀ a, F a ∈ 𝒜 (d a)) :
    StandardChartHomogeneousIdeal R ι i κ d F hF →+*
      (StandardChartPolynomialOverlap R ι i j ⧸
        localizedDehomogenizedIdeal R ι i j κ d F hF) :=
  Ideal.quotientMap _
    (algebraMap Q (StandardChartPolynomialOverlap R ι i j))
    (Ideal.le_comap_of_map_le
      (map_dehomogenizedIdeal R ι i j κ d F hF).le)

@[simp]
theorem standardChartHomogeneousIdealOverlapMap_mk [Fintype ι]
    (j : Others) (κ : Type w) (d : κ → ℕ) (F : κ → Poly)
    (hF : ∀ a, F a ∈ 𝒜 (d a)) (x : Q) :
    standardChartHomogeneousIdealOverlapMap R ι i j κ d F hF
        (Ideal.Quotient.mk (dehomogenizedIdeal R ι i κ d F hF) x) =
      Ideal.Quotient.mk (localizedDehomogenizedIdeal R ι i j κ d F hF)
        (algebraMap Q (StandardChartPolynomialOverlap R ι i j) x) := by
  simp [standardChartHomogeneousIdealOverlapMap]

/-- The overlap quotient is the localization of the chart quotient at the
class of the transition coordinate. -/
theorem isLocalization_standardChartHomogeneousIdealOverlap [Fintype ι]
    (j : Others) (κ : Type w) (d : κ → ℕ) (F : κ → Poly)
    (hF : ∀ a, F a ∈ 𝒜 (d a)) :
    letI :=
      (standardChartHomogeneousIdealOverlapMap R ι i j κ d F hF).toAlgebra
    IsLocalization.Away
      (Ideal.Quotient.mk (dehomogenizedIdeal R ι i κ d F hF)
        (MvPolynomial.X j))
      (StandardChartPolynomialOverlap R ι i j ⧸
        localizedDehomogenizedIdeal R ι i j κ d F hF) := by
  let _ :=
    (standardChartHomogeneousIdealOverlapMap R ι i j κ d F hF).toAlgebra
  simp only [IsLocalization.Away]
  rw [← Submonoid.map_powers]
  refine IsLocalization.of_surjective _ _
    (Ideal.Quotient.mk (dehomogenizedIdeal R ι i κ d F hF))
    Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk
      (localizedDehomogenizedIdeal R ι i j κ d F hF))
    Ideal.Quotient.mk_surjective ?_ ?_
  · simp [RingHom.algebraMap_toAlgebra,
      standardChartHomogeneousIdealOverlapMap,
      Ideal.quotientMap_comp_mk]
  · simpa only [Ideal.mk_ker] using
      (map_dehomogenizedIdeal R ι i j κ d F hF).ge

/-- The explicit localization of a chart quotient agrees with its polynomial
overlap quotient presentation. -/
noncomputable def standardChartHomogeneousIdealLocalizationEquiv [Fintype ι]
    (j : Others) (κ : Type w) (d : κ → ℕ) (F : κ → Poly)
    (hF : ∀ a, F a ∈ 𝒜 (d a)) :
    letI :=
      (standardChartHomogeneousIdealOverlapMap R ι i j κ d F hF).toAlgebra
    Localization.Away
        (Ideal.Quotient.mk (dehomogenizedIdeal R ι i κ d F hF)
          (MvPolynomial.X j)) ≃ₐ[
      StandardChartHomogeneousIdeal R ι i κ d F hF]
      (StandardChartPolynomialOverlap R ι i j ⧸
        localizedDehomogenizedIdeal R ι i j κ d F hF) := by
  letI :=
    (standardChartHomogeneousIdealOverlapMap R ι i j κ d F hF).toAlgebra
  letI :=
    isLocalization_standardChartHomogeneousIdealOverlap R ι i j κ d F hF
  exact IsLocalization.algEquiv
    (Submonoid.powers
      (Ideal.Quotient.mk (dehomogenizedIdeal R ι i κ d F hF)
        (MvPolynomial.X j))) _ _

end ProjectiveSpace
