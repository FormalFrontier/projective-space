/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original example proofs: Worker B Task hive-request-00a7647d0c694c4eaf4654c0548c0ab129c53130
UID be7b6056-8d20-41e1-b1be-2d825db69e8b
Reader selection and header: Worker A Task hive-request-a11cc160eed1b0c777c9d375b66b4c5b41de124b
UID 01de320f-d2fb-47c5-91b1-98d7a4984f70
Imported project mathematics: Atlas and Formal Frontier contributors (AI-assisted)
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
