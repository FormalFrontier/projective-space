/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.BasicOpenBasis
public import ProjectiveSpace.CoefficientRingBase
public import ProjectiveSpace.Compact
public import ProjectiveSpace.DegreeScaledMap
public import ProjectiveSpace.DegreeScaledMapPoint
public import ProjectiveSpace.Factorial
public import ProjectiveSpace.GlobalSections
public import ProjectiveSpace.GradedProjIso
public import ProjectiveSpace.HomogeneousCoordinateChart
public import ProjectiveSpace.HomogeneousCoordinateClosedPoint
public import ProjectiveSpace.HomogeneousCoordinatePoint
public import ProjectiveSpace.HomogeneousDimension
public import ProjectiveSpace.HomogeneousIdealChart
public import ProjectiveSpace.HomogeneousIdealChartLocalization
public import ProjectiveSpace.HomogeneousPolynomialChartLocalization
public import ProjectiveSpace.HomogeneousQuotientProj
public import ProjectiveSpace.HypersurfaceChart
public import ProjectiveSpace.Irreducible
public import ProjectiveSpace.ProjectiveNullstellensatz
public import ProjectiveSpace.Reduced
public import ProjectiveSpace.StandardChart
public import ProjectiveSpace.StandardChartScheme
public import ProjectiveSpace.SymmetricAlgebraAffineClosedPoint
public import ProjectiveSpace.SymmetricAlgebraClosedPoint
public import ProjectiveSpace.SymmetricAlgebraProj
public import ProjectiveSpace.UnitScaling
public import ProjectiveSpace.Veronese

/-!
# Projective space

Public aggregate import for the project's 27 mathematical modules. The library
develops basic opens and homogeneous ideals on `Proj`, polynomial standard
charts, chart covers and equation localizations, coordinate and closed points,
graded transport, symmetric-algebra models, geometric-cover global-sections
morphisms, positive-degree-scaled maps on their natural open domains, whole-arrow
invariance under unit scaling, positive-Veronese chart and whole-scheme
isomorphisms, and geometric properties. For
`p : (degreeScaledDomain 𝒜 ℬ f).toScheme`, the point-prime leaf gives the full
ordinary-ideal formula
`((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal =
Ideal.comap f (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal)`
and membership for arbitrary ring elements, including degree zero and
inhomogeneous elements. The generic map is not global on all of `Proj ℬ`;
the Veronese inclusion is the separately proved positive-index whole-domain case.

The total-degree grading on multivariable polynomials is deliberately scoped:
use `open scoped ProjectiveSpace` when relying on its instance. Chart
presentations and geometric finiteness results have their stated coordinate
finiteness assumptions; point classifications have their own field and
algebraic-closure hypotheses. See `README.md` and `docs/MODULES.md` for the
specific interfaces and restrictions. This root introduces no declarations.
-/
