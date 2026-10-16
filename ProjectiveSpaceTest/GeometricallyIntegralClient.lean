/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import ProjectiveSpace.GeometricallyIntegral

/-!
# Geometric integrality of the projective line

The projective line over a field is the standard positive-dimensional example
of the finite-dimensional geometric-integrality theorem. Its two homogeneous
coordinates give the usual polynomial affine-line charts.
-/

open AlgebraicGeometry

universe u

private theorem projectiveLine_geometricallyIntegral (k : Type u) [Field k] :
    GeometricallyIntegral (ProjectiveSpace.polynomialProjToSpec k (Fin 2)) := by
  exact ProjectiveSpace.polynomialProjToSpec_fin_geometricallyIntegral k 1
