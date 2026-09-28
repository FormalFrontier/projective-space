module

public import ProjectiveSpace.CoherentTailProj
public import CoherentTailVeronese

@[expose] public section

/-! Concrete clients of whole-scheme coherent-tail isomorphisms. -/

noncomputable section

namespace CoherentTailProjTest

open CategoryTheory AlgebraicGeometry GradedRing.Veronese.CoherentTail
  GradedRingsTest.CoherentTailVeronese

universe u

variable {C : Type u} [CommRing C]

local instance : GradedRing (polynomialGrade C) := MvPolynomial.gradedAlgebra

/-- The integer polynomial ring and its inherited no-linear subring have isomorphic Proj. -/
def missingLinearProjIso : Proj integerPolynomialGrade ≅ Proj integerNoLinearGrade :=
  missingLinearTail.projIso 2 (by decide) (by decide)

theorem missingLinearProjIso_hom_inv_id :
    missingLinearProjIso.hom ≫ missingLinearProjIso.inv =
      𝟙 (Proj integerPolynomialGrade) :=
  missingLinearProjIso.hom_inv_id

/-- The existing no-extension witness and the geometric isomorphism coexist. -/
theorem missingLinearProjIso_inv_hom_id :
    missingLinearProjIso.inv ≫ missingLinearProjIso.hom =
      𝟙 (Proj integerNoLinearGrade) :=
  missingLinearProjIso.inv_hom_id

private theorem missingLinear_no_global_extension
    (f : integerPolynomialGrade →+*ᵍ integerNoLinearGrade)
    (hhigh : ∀ d, 2 ≤ d → ∀ x : integerPolynomialGrade d,
      ((f (x : MvPolynomial Unit ℤ) : integerNoLinear) : MvPolynomial Unit ℤ) = x) :
    False :=
  missingLinear_no_extension f hhigh

/-- The degree-zero swap on a ring with nilpotents is the actual coefficient map. -/
def swapProjIso : Proj (polynomialGrade (ZMod 4 × ZMod 4)) ≅
    Proj (polynomialGrade (ZMod 4 × ZMod 4)) :=
  swapTail.projIso 2 (by decide) (by decide)

private theorem swapProjIso_zero_nonidentity :
    swapTail.zero
      (⟨MvPolynomial.C ((1 : ZMod 4), 0),
        MvPolynomial.isHomogeneous_C _ _⟩ : polynomialGrade (ZMod 4 × ZMod 4) 0) ≠
      (⟨MvPolynomial.C ((1 : ZMod 4), 0),
        MvPolynomial.isHomogeneous_C _ _⟩ : polynomialGrade (ZMod 4 × ZMod 4) 0) :=
  swap_zero_nonidentity

theorem swapProjIso_toSpecZero :
    swapProjIso.hom ≫ Proj.toSpecZero (polynomialGrade (ZMod 4 × ZMod 4)) ≫
      Spec.map (CommRingCat.ofHom swapTail.zero.toRingHom) =
        Proj.toSpecZero (polynomialGrade (ZMod 4 × ZMod 4)) :=
  swapTail.projIso_toSpecZero 2 (by decide) (by decide)

theorem swapProjIso_hom_inv_id :
    swapProjIso.hom ≫ swapProjIso.inv =
      𝟙 (Proj (polynomialGrade (ZMod 4 × ZMod 4))) :=
  swapProjIso.hom_inv_id

theorem swapProjIso_inv_hom_id :
    swapProjIso.inv ≫ swapProjIso.hom =
      𝟙 (Proj (polynomialGrade (ZMod 4 × ZMod 4))) :=
  swapProjIso.inv_hom_id

/-- The zero coefficient ring also supports the entire construction. -/
def zeroProjIso : Proj (polynomialGrade (ZMod 1)) ≅
    Proj (polynomialGrade (ZMod 1)) :=
  zeroTail.projIso 2 (by decide) (by decide)

theorem zeroProjIso_inv_hom_id :
    zeroProjIso.inv ≫ zeroProjIso.hom =
      𝟙 (Proj (polynomialGrade (ZMod 1))) :=
  zeroProjIso.inv_hom_id

end CoherentTailProjTest
