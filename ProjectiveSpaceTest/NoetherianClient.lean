/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.Noetherian
public import ProjectiveSpace.HomogeneousCoordinatePoint

/-!
# Noetherian projective-spectrum client

Independent coefficient and coordinate witnesses, followed by applications of
the Noetherian projective-spectrum API to projective space and its topology.
-/

open scoped ProjectiveSpace
open TopologicalSpace

namespace ProjectiveSpaceTest

universe u v

private theorem integer_polynomial_noetherian (ι : Type v) [Finite ι] :
    IsNoetherianRing (MvPolynomial ι ℤ) := by
  infer_instance

private theorem field_polynomial_noetherian (k : Type u) [Field k] (n : ℕ) :
    IsNoetherianRing (MvPolynomial (Fin (n + 1)) k) := by
  infer_instance

private theorem empty_coordinate_polynomial_noetherian :
    IsNoetherianRing (MvPolynomial Empty ℤ) := by
  infer_instance

private theorem zero_ring_polynomial_noetherian :
    IsNoetherianRing (MvPolynomial Empty (ZMod 1)) := by
  infer_instance

/-- Polynomial projective space with one coordinate over a field has a point. -/
public theorem nonempty_field_polynomial_proj (k : Type u) [Field k] :
    Nonempty (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin 1) k)) := by
  let coordinate : Fin 1 → k := fun _ => 1
  have hcoordinate : coordinate ≠ 0 := by
    intro h
    have hzero : (1 : k) = 0 := congrFun h 0
    exact one_ne_zero hzero
  exact ⟨ProjectiveSpace.homogeneousCoordinatePoint coordinate hcoordinate⟩

private theorem integer_projective_space (n : ℕ) :
    AlgebraicGeometry.IsNoetherian
      (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℤ)) :=
  ProjectiveSpace.isNoetherian_polynomialProj ℤ (Fin (n + 1))

private theorem field_projective_space (k : Type u) [Field k] (n : ℕ) :
    AlgebraicGeometry.IsNoetherian
      (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) :=
  ProjectiveSpace.isNoetherian_polynomialProj k (Fin (n + 1))

private theorem empty_coordinate_projective_space :
    AlgebraicGeometry.IsNoetherian
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule Empty ℤ)) :=
  ProjectiveSpace.isNoetherian_polynomialProj ℤ Empty

private theorem zero_ring_projective_space :
    AlgebraicGeometry.IsNoetherian
      (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule Empty (ZMod 1))) :=
  ProjectiveSpace.isNoetherian_polynomialProj (ZMod 1) Empty

private theorem every_subset_compact (R : Type u) [CommRing R]
    [IsNoetherianRing R] (ι : Type v) [Finite ι]
    (subset : Set (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule ι R))) :
    IsCompact subset := by
  let _ : AlgebraicGeometry.IsNoetherian
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule ι R)) :=
    ProjectiveSpace.isNoetherian_polynomialProj R ι
  exact NoetherianSpace.isCompact subset

private theorem finite_irreducible_components (R : Type u) [CommRing R]
    [IsNoetherianRing R] (ι : Type v) [Finite ι] :
    (irreducibleComponents
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule ι R))).Finite := by
  let _ : AlgebraicGeometry.IsNoetherian
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule ι R)) :=
    ProjectiveSpace.isNoetherian_polynomialProj R ι
  exact AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian

end ProjectiveSpaceTest
