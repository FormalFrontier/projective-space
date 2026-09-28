# Projective space

Reusable Lean theory of `Proj` of naturally graded commutative rings and, in
particular, total-degree graded polynomial rings. The library includes
positive-degree basic-open topology, a projective radical criterion, coordinate
points, graded-map transport, homogeneous-component dimensions, polynomial
standard charts and transitions, gluing, equations and quotients,
symmetric-algebra models, geometric-cover global-sections morphisms, whole-arrow
unit-scaling invariance, positive-degree-scaled maps on their natural open
domains with ordinary point-prime contraction, and geometric properties. See
[the module and API map](docs/MODULES.md) for the per-file imports and hypotheses. This guide
describes the mathematical interfaces; source-specific correspondence and
coverage decisions are separate.

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
  restriction.
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

## Imports and build status

All 26 mathematical leaves and the aggregate `ProjectiveSpace.lean` root are
written as Lean `module` files
with deliberate `public import` interfaces. `import ProjectiveSpace` is the
intended ordinary import of the whole mathematical API; clients may instead
import a specific `ProjectiveSpace.*` leaf. At development revision
`c74a33c74b7d9bde054a284ada6d28bac7bd2f7d` on September 27, 2026, all
33 Lean files and four default targets passed the full build and transitive
standard-axiom audit, including private declarations. Independent destination
review and maintainer code acceptance were recorded for that revision.
Those results are revision-specific: they do not by themselves check the
later 35-file accepted baseline, nor the subsequent 37-file graph. The earlier
documentation successor `7eab8f1f08cbc12e63520f189efbc3d3ea1841bf` was
published as official release `18b517099fddac61a86f7c20d591178db9825b9a`;
the 35-file baseline was separately accepted and published, with official
release `a02283d8e40759d4ef58a76e8183b11dd7021a17` sharing its tree.
The frozen incubator input was separately accepted on September 27, 2026.
At accepted destination code revision
`d866ec190766ef2a76978fadc05627717f300468`, native CI run 632 built
all four targets and 37 Lean files (3,493 jobs) and audited 770 declaration
origins, including 294 private names, with only the three standard axioms.
Independent destination review 4376 and Atlas's code acceptance and protected
integration followed on September 27, 2026. That **producer** is now in the
verified official release `ad60036d9745d4f0bca2f398538cff4377c93603`,
whose tree equals the accepted baseline. The point-prime leaf was separately
checked and accepted at destination code revision
`8712cd1d042032ba4577145b3a3034ed2609e671`: independent affected review
4399 and native run 647 checked all four targets (3,495 jobs) and all 39 Lean
files, including 780 declaration origins (302 private-prefix names), with only
`propext`, `Classical.choice` and `Quot.sound` as transitive axioms. Atlas
accepted the code and integrated it into protected main on September 28,
2026. Neither the earlier producer checks nor this accepted main revision
establishes a separately reviewed and verified point-prime release. The scoped
polynomial grading requires
`open scoped ProjectiveSpace` when used.

Two existing private native clients import selected leaves:
`ProjectiveSpaceTest.PointClient` and `ProjectiveSpaceTest.GeometryClient`.
`ProjectiveSpaceTest.RootClient` imports **only** the aggregate
root and checks chart and scoped-grading use, point evaluation, graded transport,
reducedness and quasicompactness. Its named checks are private. The new test-only
`ProjectiveSpaceTest.GlobalSectionsClient` directly imports the existing leaf and
checks its geometric-cover constructor, chart and base identities, and
strong-hypothesis recovery. Its declarations are public Lean names in the
`ProjectiveSpaceTest.ProjGlobalSections` namespace, but the mathematical library
root does not import this test module; they are not intended as library API.
The fifth client, `ProjectiveSpaceTest.UnitScalingClient`, directly imports
`ProjectiveSpace.UnitScaling` and tests five public declarations in the
test-only `ProjectiveSpaceTest.ProjUnitScaling` namespace. It is not a
mathematical-library API or imported by the root.
The sixth client, `ProjectiveSpaceTest.DegreeScaledMapClient`, directly imports
`ProjectiveSpace.DegreeScaledMap`. Its seven examples use the generic arrow,
domain complement, whole chart, localization fraction, open preimage,
degree-zero triangle and uniqueness; the chart witness is private. Its
test-only namespace is not imported by the mathematical root.
The seventh client, `ProjectiveSpaceTest.DegreeScaledMapPointClient`, directly
imports `ProjectiveSpace.DegreeScaledMapPoint`. Its three examples check full
ordinary-ideal equality, membership for an arbitrary ring element and a
degree-zero element. Its test-only namespace is not imported by the root.

Three additional private, complete ordinary-native-import examples are stored
in [geometry](examples/GeometryExamples.lean),
[coordinate points](examples/PointExamples.lean), and
[graded transport](examples/TransportExamples.lean). Read their `module`,
imports, universes, variables, namespace, proofs and same-file `#print axioms`
commands together; these are not extra public theorem APIs. The geometry
example explicitly uses `open scoped ProjectiveSpace` for the non-global
polynomial total-degree grading, including the zero-ring positive-open case,
the radical direction, semiring finrank and domain/nonempty irreducibility.
The point example uses generator simplification and the definitional cone-line
kernel over a field; the transport example checks points and closed points
across independent universes in the contravariant direction. No excerpt-only
Lean snippets substitute for these complete modules.

`lean-toolchain` pins Lean `v4.34.0-rc2`; `lake-manifest.json` and
`lakefile.toml` fix mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, graded-rings
`f77410141b89532409fff563d368930a728f55b7` and scheme-properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00` (plus ten inherited
packages in the resolved 13-package manifest). Graded Rings and Scheme
Properties are pinned to their official private GitHub releases; access to
those repositories is presently required to build this library.
Four existing Lake targets cover all 39 Lean
files: `ProjectiveSpace` (root and 26 leaves), `ProjectiveSpaceTest` (two
earlier clients, the root-only client, the global-sections client and the
unit-scaling client, the degree-scaled-map client and the point-prime client),
`ProjectiveSpaceAxiomTests`
(both diagnostic test modules), and `ProjectiveSpaceReaderExamples` (all
three complete examples). Literal `defaultTargets` names all four. With access
to the private dependencies, install the pinned Lean toolchain using `elan`,
fetch the matching mathlib cache successfully **before** any build, then build:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
lake --wfail build
```

The default build includes all 39 Lean files. To build an individual target, use
`lake --wfail build ProjectiveSpace` (or one of the other three target names).
`--wfail` is Lake's warning-fatal option; `-KwarningAsError=true` alone does
not make Lake fail on source warnings. On the initial pinned-graph checkout,
the matching mathlib cache is several gigabytes; once dependencies are cached,
the 33-file, four-target build at the revision recorded above took about 52
seconds after cache preparation in native CI. This is not an end-to-end clean
installation time; dependency fetches and other machines may take longer.
The three reader examples
independently import selected leaves, not the aggregate root. The two `Tests`
files contain diagnostic axiom commands; their selected-name prints are not a
complete transitive audit of all shipped declarations, including private ones.

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

## Integration and attribution

Bounded source, mathematical and review findings apply only to their exact
revisions and scopes. The historical full check recorded above covered 33 shipped modules
and 669 module/declaration origins, including 249 private declarations, with
only `propext`, `Classical.choice` and `Quot.sound` as transitive axioms.
Focused producer checks alone would not substitute for a full-graph check.
Unchanged mathematical/build/dependency inputs may reuse applicable evidence;
the degree-scaled producer, client, root and dependency change received the
full-graph native run 632 and author-distinct review 4376 at the exact accepted
code revision recorded above. Its release is separately accepted and verified
as `ad60036d9745d4f0bca2f398538cff4377c93603`. The added point-prime
leaf/client/root graph at `8712cd1d042032ba4577145b3a3034ed2609e671`
received its own independent affected review 4399, complete native run 647
and Atlas's code acceptance and protected integration on September 28, 2026.
Documentary successors with unchanged Lean/build/dependency/checker inputs
can reuse that evidence, but need their own review and release decisions;
code acceptance is not point-prime publication or source-coverage certification.

The `formalization.yaml` metadata and module/API map describe this library without
asserting source completeness. The `NOTICE` records bounded attribution, not a
blanket redistribution-rights clearance; release review covers retained third-party
material and the actual public history. Tags are deferred. No fresh generated API
documentation or separate stored-proof replay is required in addition to the
applicable build, complete axiom audit and independent release assessment.

Authors: Formal Frontier Agents. Original mathematical files and repository
history were authored by Atlas. Worker A Task
`hive-request-6d6a73bb45d27e7fc8f3e3021270e3c4a3701c49` (UID
`4ba77f48-bce0-4e37-8101-3df08089a5d0`) prepared six native module
interfaces and two earlier clients; Worker B Task
`hive-request-00a7647d0c694c4eaf4654c0548c0ab129c53130` (UID
`be7b6056-8d20-41e1-b1be-2d825db69e8b`) wrote the selected guide,
module map and original private example bodies; Worker A Task
`hive-request-a11cc160eed1b0c777c9d375b66b4c5b41de124b` (UID
`01de320f-d2fb-47c5-91b1-98d7a4984f70`) selected and corrected the
earlier reader payload, its headers and Lake configuration. Later native
adaptations, the bounded source assembly, and the UnitScaling transfer
are credited in [CONTRIBUTORS.md](CONTRIBUTORS.md). These credits record
contributions, not an assertion of copyright ownership.

Original project contributions are offered under the complete Apache License
2.0 in `LICENSE`; dependency licenses and notices remain separate. The adapted
mathlib proof text retains its own attribution as described in `NOTICE`; no
motivating source PDFs are reproduced or other dependency files relicensed.
