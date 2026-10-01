/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveSpace.HomogeneousCoordinatePoint

namespace ProjectiveSpaceReader.PointExamples

universe u v

variable {k : Type u} [Field k] {ι : Type v}

private theorem coordinate_evaluation_and_nonvanishing
    (a : ι → k) (i : ι) (hi : a i ≠ 0) :
    ProjectiveSpace.homogeneousCoordinateMap a (MvPolynomial.X i) =
      Polynomial.C (a i) * Polynomial.X ∧
    MvPolynomial.X i ∉ ProjectiveSpace.homogeneousCoordinateIdeal a := by
  exact ⟨by simp, ProjectiveSpace.X_not_mem_homogeneousCoordinateIdeal a i hi⟩

private theorem ideal_reduces_to_cone_line_kernel (a : ι → k) :
    ProjectiveSpace.homogeneousCoordinateIdeal a =
      RingHom.ker (ProjectiveSpace.homogeneousCoordinateMap a).toRingHom := by
  rfl

private theorem point_unchanged_by_scalar
    (a : ι → k) (ha : a ≠ 0) (c : k) (hca : c • a ≠ 0) :
    ProjectiveSpace.homogeneousCoordinatePoint (c • a) hca =
      ProjectiveSpace.homogeneousCoordinatePoint a ha := by
  exact ProjectiveSpace.homogeneousCoordinatePoint_eq_of_eq_smul
    (c • a) a hca ha c rfl

private theorem projectivization_mk_point (a : ι → k) (ha : a ≠ 0) :
    ProjectiveSpace.projectivizationToProj (Projectivization.mk k a ha) =
      ProjectiveSpace.homogeneousCoordinatePoint a ha := by
  simp

#print axioms coordinate_evaluation_and_nonvanishing
#print axioms ideal_reduces_to_cone_line_kernel
#print axioms point_unchanged_by_scalar
#print axioms projectivization_mk_point

end ProjectiveSpaceReader.PointExamples
