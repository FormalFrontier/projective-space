# Projective-space module and API map

This library has 22 mathematical
leaves, one aggregate root, three private test clients, two diagnostic tests
and three complete reader examples: **31 Lean files**. All 22 leaves and the
root have native `module` headers and public imports; all four default targets,
including the aggregate root and its private import client, build on the
official pinned dependency graph. This table records actual direct imports and
principal public entry points, not independent release or proof acceptance. Typeclass and
size restrictions below come from the declarations, not just their names.
Imports within this repository use the `ProjectiveSpace.` prefix unless stated.
See the [reader guide](../README.md) for mathematical context, expected imports
and cache-first build commands; neither document certifies a release.

| File / status | Direct project/provider imports | Main interfaces and requirements |
| --- | --- | --- |
| `BasicOpenBasis` **native** | mathlib only | `AlgebraicGeometry.Proj.positiveBasicOpens`, `isTopologicalBasis_positiveBasicOpens`: any naturally graded commutative ring; positive degree. |
| `GradedProjIso` **native** | mathlib only | `ProjectiveSpace.map_irrelevant_le`, `irrelevant_le_map_of_comp_eq_id`, `projectiveSpectrumEquivOfInverseGradedRingHom`, `projectiveSpectrumHomeomorphOfInverseGradedRingHom`, `projClosedPointsEquivOfInverseGradedRingHom`: inverse degree-preserving homomorphisms, independent ring/carrier universes; `projIsoOfInverseGradedRingHom`, `closedPointsEquivOfIso`: scheme-level same carrier universe. Application equations marked `@[simp]`. |
| `HomogeneousCoordinatePoint` **native** | mathlib only | `homogeneousCoordinateMap`, `homogeneousCoordinateIdeal`, `mem_homogeneousCoordinateIdeal_iff_eval_eq_zero` (homogeneous polynomial), `homogeneousCoordinatePoint` (nonzero vector), `homogeneousCoordinatePoint_eq_of_eq_smul`, `projectivizationToProj`; arbitrary coordinate type over a field, no algebraic closure or finite type. Generator/mk equations marked `@[simp]`. |
| `HomogeneousDimension` **native** | mathlib only | `finrank_homogeneousSubmodule` (`Fintype ι`) and `finrank_homogeneousSubmodule_fin` (`Fin (n+1)`): commutative semiring + `StrongRankCondition`. |
| `Irreducible` **native** | mathlib only | `ProjectiveSpace.polynomialProj_irreducibleSpace` instance: coefficient ring is a domain, coordinate type `Nonempty`. |
| `ProjectiveNullstellensatz` **native** | mathlib only | `ProjectiveSpectrum.mem_vanishingIdeal_zeroLocus_iff_mem_radical`: arbitrary graded commutative ring and homogeneous ideal, homogeneous `f` of *strictly positive* degree, ordinary radical. |
| `StandardChart` native | mathlib only | `StandardChart`, `standardChartEquiv`, `coordinateRatio`, `standardChartAlgebra`, overlap localization and pairwise transition equivalences; polynomial presentation needs finite coordinates, several underlying overlap identities do not; arbitrary commutative ring/zero ring. `open scoped ProjectiveSpace` supplies the polynomial grading instance. |
| `StandardChartScheme` native | `StandardChart`; mathlib | `iSup_basicOpen_X_eq_top`, `standardCoordinateChartIso`, `standardCoordinateAffineOpenCover`, `standardCoordinateGlueData`, `standardCoordinateGluedIsoProj`: literal polynomial chart cover and gluing for a commutative base. |
| `HomogeneousPolynomialChartLocalization` native | `StandardChart` | `isLocalization_standardChartHomogeneousLocalization`, `standardChartPolynomialLocalizationEquiv`: arbitrary homogeneous polynomial, zero ring and zero/divisor polynomial allowed; polynomial chart presentation needs `Fintype ι`. |
| `HypersurfaceChart` native | `StandardChart` | `homogeneousPolynomialOnChart_overlap`, `standardChartHypersurfaceOverlapEquiv`: descend homogeneous equations and overlap transitions over a commutative ring including zero ring; finite indices for polynomial overlap quotients. |
| `HomogeneousIdealChart` native | `HypersurfaceChart` | `dehomogenizedIdeal`, `localizedDehomogenizedIdeal`, `standardChartHomogeneousIdealOverlapEquiv`: arbitrary family of homogeneous equations (a separate family-index type); polynomial ideal presentation assumes `Fintype ι`. |
| `HomogeneousIdealChartLocalization` native | `HomogeneousIdealChart`; mathlib | `isLocalization_standardChartHomogeneousIdealOverlap`, `standardChartHomogeneousIdealLocalizationEquiv`: quotient chart overlap as localization, `Fintype ι`. |
| `HomogeneousQuotientProj` native | **`GradedRings.Quotient`**; mathlib | `Ideal.Quotient.quotient_irrelevant_le_map`, quotient projective-spectrum point and induced closed immersion with image the projective zero locus; `Ideal.IsHomogeneous` prerequisite. Official Graded Rings dependency. |
| `HomogeneousCoordinateChart` native | `HomogeneousCoordinatePoint`, `StandardChartScheme` | `normalizedCoordinates`, `affineCoordinatePoint`, `homogeneousCoordinatePoint_mem_basicOpen_X_iff`, `standardCoordinateChartMap_affineCoordinatePoint`: coordinates `a j / a i` when `a i ≠ 0`; field, nonzero coordinate. The `chartEvaluation` helpers are **private**, not a client API. |
| `HomogeneousCoordinateClosedPoint` native | `HomogeneousCoordinateChart`; mathlib | `homogeneousCoordinatePoint_isClosed` and `projectivizationToProj_injective` over a field; `projectivizationToProj_surjective_on_closedPoint`, `projectivizationEquivClosedPoints` for **algebraically closed field + finite coordinates**. |
| `SymmetricAlgebraProj` native | `GradedProjIso`, **`GradedRings.SymmetricAlgebra`** | graded polynomial/symmetric algebra transport: `symmetricAlgebraProjectiveSpectrumEquivOfLinearEquiv`, `symmetricAlgebraProjIsoOfLinearEquiv`, `mvPolynomialProjClosedPointsEquivSymmetricAlgebra`; official Graded Rings dependency. |
| `SymmetricAlgebraClosedPoint` native | `HomogeneousCoordinateClosedPoint`, `SymmetricAlgebraProj`; mathlib | basis-free cone-line ideal, `symmetricAlgebraHomogeneousCoordinatePoint`, `projectivizationEquivSymmetricAlgebraClosedPoints`, `oneDimensionalSubspacesEquivSymmetricAlgebraClosedPoints`; finite-dimensional vector space, algebraically closed field for classification. |
| `SymmetricAlgebraAffineClosedPoint` native | `SymmetricAlgebraClosedPoint`; mathlib | affine evaluation ideal and `symmetricAlgebraAffineClosedPointsEquiv`: vectors identify affine closed points over algebraically closed field with finite-dimensional vector space; includes naturality and scalar specialization. |
| `CoefficientRingBase` native | `StandardChart`; mathlib | `mvPolynomialDegreeZeroEquiv`, `polynomialProjToSpecULift` (independent universes), `polynomialProjToSpec` (direct small-enough index universe); *finite coordinates* for locally finite type and quasicompact instances. |
| `Compact` native | `StandardChartScheme`; mathlib | `ProjectiveSpace.instCompactSpaceProj`: finite coordinates, arbitrary commutative ring; uses finite affine cover. |
| `Reduced` native | `StandardChartScheme`; mathlib | `ProjectiveSpace.proj_isReduced` for a reduced commutative graded ring, plus `polynomialProj_isReduced` for reduced polynomial base (no nonempty-index restriction). |
| `Factorial` native | `StandardChartScheme`, **`SchemeProperties.FactorialNormal`** | `polynomialProj_isFactorial`, `polynomialProj_isNormal`: finite coordinates, `UniqueFactorizationMonoid` commutative ring, including empty indices; official Scheme Properties dependency. |
| `ProjectiveSpace.lean` **native root, built whole graph** | direct public imports of all 22 mathematical leaves | Ordinary `import ProjectiveSpace` entry point; no new declarations. Release decisions are recorded separately. |
| `ProjectiveSpaceTest.PointClient` **native private test** | `HomogeneousCoordinatePoint`, `GradedProjIso` | Public generator simplification, definitional kernel, stored algebra map, irrelevant-map bound across independent universes. Not a published theorem API. |
| `ProjectiveSpaceTest.GeometryClient` **native private test** | `BasicOpenBasis`, `ProjectiveNullstellensatz`, `Irreducible`, `HomogeneousDimension` | Positive-degree radical/basis, semiring finrank, domain/nonempty irreducibility. Not a published theorem API. |
| `ProjectiveSpaceTest.RootClient` **native private test; built** | ordinary `import ProjectiveSpace` only | Scoped chart algebra and cover, polynomial reducedness/compactness, point chart/evaluation, graded transport; all named checks are private. |
| `Tests.GradedTransportAxioms` **diagnostic** | `GradedProjIso`, `SymmetricAlgebraProj` | Ordinary public imports and literal transport `#print axioms` commands; listing is not a new axiom check. |
| `Tests.SymmetricAlgebraAxioms` **diagnostic** | `import all` of `SymmetricAlgebraClosedPoint`, `SymmetricAlgebraAffineClosedPoint` | Internal-name axiom diagnostics, including private names; not an ordinary public-API client. |
| `examples.GeometryExamples` **reader example** | `BasicOpenBasis`, `ProjectiveNullstellensatz`, `HomogeneousDimension`, `Irreducible` | Complete private geometry examples with scoped grading. |
| `examples.PointExamples` **reader example** | `HomogeneousCoordinatePoint` | Complete private coordinate-point examples. |
| `examples.TransportExamples` **reader example** | `GradedProjIso` | Complete private transport examples with independent universes. |

The three complete modules in [`examples/`](../examples/) independently
ordinary-import selected production leaves and provide additional private
downstream usage, not new public theorems. New users may import
`ProjectiveSpace` for the intended whole API or an individual leaf; use
`open scoped ProjectiveSpace` where polynomial grading is needed. The
`ProjectiveSpace` target names root and all leaves, `ProjectiveSpaceTest` all
three clients, `ProjectiveSpaceAxiomTests` both diagnostic modules, and
`ProjectiveSpaceReaderExamples` all three examples; defaults name every target.
The resolved 13-package manifest pins mathlib, official Graded Rings and official
Scheme Properties directly and inherits their exact supporting dependencies.
Compilation and transitive axiom results remain subject to independent review;
this lightweight map does not assert source coverage or release acceptance.
