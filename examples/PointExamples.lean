/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveSpace.HomogeneousCoordinatePoint

/-!
# Homogeneous-coordinate point recipes

Let `k : Type u` be a field and `ι : Type v` an index type. These recipes
use no finite-coordinate hypothesis.

## Evaluation and the cone-line kernel

For `a : ι → k` and `i : ι`, simplification gives
`ProjectiveSpace.homogeneousCoordinateMap a (MvPolynomial.X i) =
Polynomial.C (a i) * Polynomial.X`.
If `hi : a i ≠ 0`, use
`ProjectiveSpace.X_not_mem_homogeneousCoordinateIdeal a i hi` for
`MvPolynomial.X i ∉ ProjectiveSpace.homogeneousCoordinateIdeal a`.
The nonvanishing hypothesis belongs to this latter conclusion, not to
the evaluation formula.

The equality
`ProjectiveSpace.homogeneousCoordinateIdeal a =
RingHom.ker (ProjectiveSpace.homogeneousCoordinateMap a).toRingHom`
is definitional (`rfl`). It identifies the ideal with the kernel of the
map to the polynomial cone line; it does not require `a ≠ 0`.

## Scalar invariance and projectivization

For `ha : a ≠ 0`, `c : k`, and `hca : c • a ≠ 0`, the direct application
`ProjectiveSpace.homogeneousCoordinatePoint_eq_of_eq_smul
  (c • a) a hca ha c rfl`
identifies `ProjectiveSpace.homogeneousCoordinatePoint (c • a) hca` with
`ProjectiveSpace.homogeneousCoordinatePoint a ha`.
Keep both nonzero-vector witnesses: this recipe does not construct a
point from the zero vector and does not replace `hca` with an unstated
assumption on the scalar.

For `a : ι → k` and `ha : a ≠ 0`, simplification also gives
`ProjectiveSpace.projectivizationToProj (Projectivization.mk k a ha) =
ProjectiveSpace.homogeneousCoordinatePoint a ha`.
Thus the quotient constructor and the homogeneous-coordinate constructor
agree on this representative. This recipe starts with the supplied
nonzero vector; it does not choose a normalized representative.
-/
