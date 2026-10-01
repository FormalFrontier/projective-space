# Projective space

Reusable Lean theory of `Proj` of naturally graded commutative rings and, in
particular, total-degree graded polynomial rings. The library includes
positive-degree basic-open topology, a projective radical criterion, coordinate
points, graded-map transport, homogeneous-component dimensions, polynomial
standard charts and transitions, gluing, equations and quotients,
symmetric-algebra models, geometric-cover global-sections morphisms, whole-arrow
unit-scaling invariance, positive-degree-scaled maps on their natural open
domains with ordinary point-prime contraction, positive-Veronese chart
equivalences and whole-scheme invariance, and geometric properties. See
[the module and API map](docs/MODULES.md) for the per-file imports and hypotheses. This guide
describes the mathematical interfaces; source-specific correspondence and
coverage decisions are separate.

## Headline results

- Inverse degree-preserving graded ring maps give whole-scheme `Proj`
  isomorphisms through `ProjectiveSpace.projIsoOfInverseGradedRingHom` and
  homeomorphisms and closed-point equivalences through
  `ProjectiveSpace.projectiveSpectrumHomeomorphOfInverseGradedRingHom` and
  `ProjectiveSpace.projClosedPointsEquivOfInverseGradedRingHom`.
  Scheme transport uses one universe for underlying rings; point transport
  permits independent ring universes. See the
  [module](ProjectiveSpace/GradedProjIso.lean) and
  [point client](ProjectiveSpaceTest/PointClient.lean).
- Compatible graded tails with equivalent degree-zero rings and high-degree
  pieces induce an isomorphism of **entire projective schemes**
  `E.projIso n hNn hn` for `N ≤ n` and `0 < n`, with both forward and inverse
  equalities over the actual degree-zero base. No graded map on the omitted
  low-degree original components, finite generation, domain, reducedness or
  `Nontrivial` is needed. The algebraic `TailEquiv` is provided by the official
  Graded Rings dependency; this library proves the geometric transfer. See
  [the coherent-tail guide](docs/CoherentTailProj.md),
  [module](ProjectiveSpace/CoherentTailProj.lean) and
  [client](ProjectiveSpaceTest/CoherentTailProjClient.lean).
- Every positive selected-component Veronese has a whole-scheme isomorphism
  `AlgebraicGeometry.Proj.Veronese.schemeIso`, compatible with the degree-zero
  coefficient map; its charts accommodate zero divisors and nilpotents.
  Selected-component ring algebra comes from Graded Rings. See
  [the Veronese guide](docs/Veronese.md),
  [module](ProjectiveSpace/Veronese.lean) and
  [client](ProjectiveSpaceTest/VeroneseClient.lean).
- A positive degree-scaled ring hom constructs a projective scheme arrow on
  the **actual open complement** of its image-irrelevant zero locus, with
  coefficient naturality and arbitrary-element ordinary point-prime
  contraction. The generic arrow is not asserted to extend to all of `Proj`.
  See the [degree-scaled guide](docs/DegreeScaledMap.md),
  [point-prime guide](docs/DegreeScaledMapPoint.md) and
  [direct client](ProjectiveSpaceTest/DegreeScaledMapPointClient.lean).
- Positive-degree homogeneous basic opens form a basis on arbitrary graded
  `Proj`, including the zero ring; the positive-degree projective radical
  criterion identifies vanishing with membership in an **ordinary** radical.
  The latter needs a positive-degree homogeneous element, not a field or
  Noetherianity. See the [basis module](ProjectiveSpace/BasicOpenBasis.lean),
  [radical module](ProjectiveSpace/ProjectiveNullstellensatz.lean) and
  [geometry client](ProjectiveSpaceTest/GeometryClient.lean).

## Mathematical scope

- `ProjectiveSpace.BasicOpenBasis` gives a basis of positive-degree homogeneous
  basic opens for `Proj` of **any** naturally graded commutative ring, including
  the zero ring.
- `ProjectiveSpace.ProjectiveNullstellensatz` identifies vanishing of a
  homogeneous element of **strictly positive degree** on relevant homogeneous
  primes above a homogeneous ideal `I` with membership in the **ordinary**
  radical `I.toIdeal.radical`. It assumes neither a field, Noetherianity,
  nontriviality nor containment of `I` in the irrelevant ideal. It does not
  assert an unrestricted equality of homogeneous ideals.
- `ProjectiveSpace.HomogeneousCoordinatePoint` sends a nonzero vector
  `a : ι → k` over a **field** to the kernel of `X i ↦ (a i) t`, a relevant
  homogeneous prime and a projective-spectrum point; it gives a homogeneous
  evaluation criterion and invariance under nonzero scaling without requiring
  finite coordinates or algebraic closure. The distinct **closed-point
  classification** in `ProjectiveSpace.HomogeneousCoordinateClosedPoint` does
  require an algebraically closed field **and finite coordinates**.
- `ProjectiveSpace.GradedProjIso` supplies projective-spectrum equivalences,
  homeomorphisms and closed-point equivalences for inverse degree-preserving
  ring maps, with **independent universes** for the ring and grading carriers.
  Transport is contravariant: `f : 𝒜 →+*ᵍ ℬ` sends `Proj ℬ` to `Proj 𝒜`.
  Scheme-level `Proj` isomorphisms retain mathlib's same-carrier-universe
  restriction. Its `AlgebraicGeometry.Proj.map_toSpecZero` compares the actual
  native graded `Proj.map` with the degree-zero coefficient ring homomorphism.
- `ProjectiveSpace.HomogeneousDimension` counts degree-`d` components for
  finite coordinate types by `card ι` multichoose `d`, specializing to
  `(n + d).choose d` for `Fin (n + 1)`. The coefficient type needs only a
  **commutative semiring with `StrongRankCondition`**, not a field or ring.
- `ProjectiveSpace.Irreducible` proves polynomial `Proj` irreducible over an
  **integral domain with a nonempty coordinate type**; this is not a claim for
  arbitrary bases or empty coordinates.
- `ProjectiveSpace.GlobalSections` constructs `X ⟶ Proj 𝒜` from an ordinary
  ring homomorphism `A →+* Γ(X, ⊤)` **from** a graded ring when the actual
  positive-homogeneous source basic opens cover `X`. It also provides chart
  and degree-zero identities and recovers mathlib's stronger construction
  under its separate irrelevant-ideal hypothesis. See the
  [global-sections guide](docs/GlobalSections.md); no affine or
  ideal-equals-top hypothesis is needed for the new construction.
- `ProjectiveSpace.UnitScaling` proves that degree-weighted multiplication by
  a global unit preserves the **whole** geometric-cover Proj morphism, even
  with independently supplied cover witnesses. It compares degree-zero
  fractions, source basic opens and complete chart arrows without requiring
  an affine source, reducedness, a field or an irrelevant-ideal-equals-top
  assumption. It needs an actual positive-homogeneous source-open cover for
  the whole-arrow conclusion; see the [unit-scaling guide](docs/UnitScaling.md).
- `ProjectiveSpace.DegreeScaledMap` constructs an actual morphism
  `U.toScheme ⟶ Proj 𝒜` from an ordinary unital `f : A →+* B` that sends
  degree `n` into degree `d * n` for **positive** `d`. The open `U` in `Proj ℬ`
  is the complement of the image-irrelevant zero locus, not automatically all
  of `Proj ℬ`. The API proves both overlap faces, whole-chart fraction laws,
  uniqueness, degree-zero base naturality and `U`-relative basic-open
  preimages. See the [degree-scaled-map guide](docs/DegreeScaledMap.md).
- `ProjectiveSpace.DegreeScaledMapPoint` computes the **entire ordinary ideal**
  of each point under the existing degree-scaled morphism on its **actual open
  domain** as `Ideal.comap f` of the domain point's prime, and proves
  membership for **every** ring element, including degree zero and
  inhomogeneous elements. It retains positive `d` and a common universe for
  the two underlying rings; it does not extend the morphism to all of
  `Proj ℬ`. See the [point-prime guide](docs/DegreeScaledMapPoint.md).
- `ProjectiveSpace.Veronese` identifies `Proj 𝒮` with the **whole scheme**
  `Proj (GradedRing.Veronese.component 𝒮 n)` for `0 < n`. The complete
  selected-component ring exists for any `n`, but injective inclusion,
  degree-zero comparison, chart equivalences and scheme invariance require
  positivity. Charts include zero and nilpotent parameters, without a
  domain, reducedness, finite generation or degree-one-generation assumption.
  Its canonical forward arrow contracts arbitrary ordinary point ideals
  and commutes with the degree-zero coefficient-ring arrow. See the
  [Veronese guide](docs/Veronese.md).
- `ProjectiveSpace.CoherentTailProj` uses the official Graded Rings coherent
  `TailEquiv` to identify **whole sheaf-bearing** `Proj` schemes at every
  selected positive degree beyond the cutoff. Its selected and whole isos,
  exact composite map, and both actual degree-zero coefficient triangles
  require no original-ring extension across the omitted low degrees. Native
  `Proj.map` requires the underlying rings in one universe, but the original
  grading-carrier universes are independent. See the
  [coherent-tail guide](docs/CoherentTailProj.md).

Other files give polynomial standard-chart algebras and overlaps over any
commutative ring (including the zero ring), finite-coordinate polynomial
presentations and affine covers, homogeneous-equation chart ideals and
localization. They give reducedness of `Proj` for a reduced commutative graded
ring and of polynomial `Proj` for a reduced base, finite-coordinate
quasicompactness and locally finite-type structure morphisms, and
finite-coordinate factoriality and normality over a unique-factorization
base. Neither finite type nor quasicompactness is claimed for unrestricted
coordinate types. Total fractions of a field cannot replace localization
over a base ring with zero divisors.

## Imports and build

The 28 mathematical leaves are public `module` files, and
[`ProjectiveSpace.lean`](ProjectiveSpace.lean) publicly imports all of them.
Use `import ProjectiveSpace` for the whole library or import an individual
`ProjectiveSpace.*` leaf. Use `open scoped ProjectiveSpace` for the polynomial
total-degree grading. The hand-maintained [module and API map](docs/MODULES.md)
lists each leaf, its direct imports and hypotheses, all nine test clients, two
diagnostic modules and three [complete reader examples](examples/). The clients,
diagnostics and private examples are not additional production theorem APIs.

The four default Lake targets are `ProjectiveSpace`, `ProjectiveSpaceTest`,
`ProjectiveSpaceAxiomTests` and `ProjectiveSpaceReaderExamples`. The project pins
Lean `v4.34.0-rc2`, mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`,
official Graded Rings `db2a1d555639e2a381abbf755982ffdcf126621e` and
official Scheme Properties `6b204a3e49f022e51d78a9f93e77513b99a87e00`;
`lake-manifest.json` records the complete resolved 13-package graph. Access to
the pinned private dependencies is presently required. Fetch the matching
mathlib cache *before* building:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
lake --wfail build
```

The matching mathlib cache occupies several gigabytes on an initial pinned-
graph checkout. As historical guidance only, a **33-file** four-target build
in native CI took about **52 seconds after cache preparation**; this is not a
43-file timing, a cold installation estimate or a RAM measurement. Dependency
fetches and other machines may take longer. `LEAN_NUM_THREADS=2` may limit
Lean runtime threads during a build, but it is not an aggregate memory cap.

The two `Tests` modules contain selected-name `#print axioms` diagnostics;
those prints are not a complete transitive audit of every shipped declaration.
The historical 43-file graph received a four-target build and a transitive
standard-three audit of 859 declaration origins, including 313 private-prefix
names and generated declarations, at its recorded original code revision.
Changed headers and module comments in this repository require an applicability
decision for that evidence; the historical result is not a check of modified
whole-file bytes. Release and source-coverage decisions remain separate.

## Why the principal results hold

For the basis theorem, refine a `Proj.basicOpen` neighborhood using a
positive-degree homogeneous component **outside the point's prime ideal**;
products of component opens refine the chosen neighborhood. For the radical
criterion, if positive-degree `f` is not in the radical, take a prime above
`I` avoiding powers of `f`, pass to its homogeneous core and use `f` to rule
out the irrelevant ideal; the reverse implication uses primality. For
coordinate points, the kernel of the cone-line map is prime because its
polynomial codomain over a field is a domain; homogeneous evaluation makes
the kernel homogeneous. A nonzero coordinate excludes the irrelevant ideal,
and substitution `t ↦ c t` proves nonzero-scalar invariance. The monomial
basis for the degree-`d` component is indexed by weak compositions, counted
by multichoose. Over a domain with at least one coordinate, the homogeneous
zero ideal provides a relevant generic point for irreducibility. Inverse
graded map/comap identities give the point equivalence, whose homeomorphism
transports closed points. The [module map](docs/MODULES.md) locates the other
interfaces.

## Contributors and provenance

Authors: Formal Frontier Agents.

The original project mathematical development was AI-assisted work by Atlas;
later Formal Frontier AI agents separately authored native adaptations,
geometric-cover and unit-scaling constructions, degree-scaled and point-prime
proofs, positive-Veronese and coherent-tail geometry, reader examples and
client modules. Original coherent-tail and Veronese algebra is supplied by
Graded Rings, not reauthored here. Atlas assembled and accepted the library;
independent reviewers examined bounded candidate revisions. See
[CONTRIBUTORS.md](CONTRIBUTORS.md) for distinct contribution roles and
[NOTICE](NOTICE) for retained mathlib attributions and license boundaries.
These credits do not assert copyright ownership or source coverage.

Original project contributions are offered under [Apache-2.0](LICENSE).
Mathlib, Graded Rings and Scheme Properties are separately licensed dependencies.
The adapted mathlib chart and gluing text retains Andrew Yang's 2024 copyright
and license notice; the homogeneous-localization lineage retains Jujian
Zhang's 2022 credit and Eric Wieser's role. No motivating source PDF is included.
