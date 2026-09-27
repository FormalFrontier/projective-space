# Projective space

Reusable Lean theory of `Proj` of naturally graded commutative rings and, in
particular, total-degree graded polynomial rings. The library includes
positive-degree basic-open topology, a projective radical criterion, coordinate
points, graded-map transport, homogeneous-component dimensions, polynomial
standard charts and transitions, gluing, equations and quotients,
symmetric-algebra models, and geometric properties. See [the module and API
map](docs/MODULES.md) for the per-file imports and hypotheses. This guide
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

All 23 mathematical leaves and the aggregate `ProjectiveSpace.lean` root are
written as Lean `module` files
with deliberate `public import` interfaces. `import ProjectiveSpace` is the
intended ordinary import of the whole mathematical API; clients may instead
import a specific `ProjectiveSpace.*` leaf. At development revision
`c74a33c74b7d9bde054a284ada6d28bac7bd2f7d` on September 27, 2026, all
33 Lean files and four default targets passed the full build and transitive
standard-axiom audit, including private declarations. Independent destination
review and maintainer code acceptance were recorded for that revision.
These results are revision-specific; exact release acceptance and publication
are separate decisions recorded for each release. The scoped polynomial grading requires
`open scoped ProjectiveSpace` when used.

Two existing private native clients import selected leaves:
`ProjectiveSpaceTest.PointClient` and `ProjectiveSpaceTest.GeometryClient`.
`ProjectiveSpaceTest.RootClient` imports **only** the aggregate
root and checks chart and scoped-grading use, point evaluation, graded transport,
reducedness and quasicompactness. Its named checks are private. The new test-only
`ProjectiveSpaceTest.GlobalSectionsClient` directly imports the new leaf and
checks its geometric-cover constructor, chart and base identities, and
strong-hypothesis recovery. Its declarations are public Lean names in the
`ProjectiveSpaceTest.ProjGlobalSections` namespace, but the mathematical library
root does not import this test module; they are not intended as library API.

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
`4a89b5f5431e7e7976bb8447702114048e697d2e` and scheme-properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00` (plus ten inherited
packages in the resolved 13-package manifest). Graded Rings and Scheme
Properties are pinned to their official private GitHub releases; access to
those repositories is presently required to build this library.
Four existing Lake targets cover all 33 Lean
files: `ProjectiveSpace` (root and 23 leaves), `ProjectiveSpaceTest` (two
earlier clients, the root-only client, and the new global-sections client), `ProjectiveSpaceAxiomTests`
(both diagnostic test modules), and `ProjectiveSpaceReaderExamples` (all
three complete examples). Literal `defaultTargets` names all four. With access
to the private dependencies, install the pinned Lean toolchain using `elan`,
fetch the matching mathlib cache successfully **before** any build, then build:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
lake --wfail build
```

The default build includes all 33 files. To build an individual target, use
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
revisions and scopes. The full check recorded above covered 33 shipped modules
and 669 module/declaration origins, including 249 private declarations, with
only `propext`, `Classical.choice` and `Quot.sound` as transitive axioms.
Focused producer checks alone would not substitute for that full-graph check.
Unchanged mathematical/build/dependency inputs may reuse this evidence; changed
inputs need reassessment. The maintainer's dated release record identifies the
exact independently assessed artifact, release acceptance and verified
publication. A passing build or development-main acceptance alone does not make
a candidate an official release; no source-coverage certification is implied.

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
adaptations, the bounded source assembly, and this source-only preparation
are credited in [CONTRIBUTORS.md](CONTRIBUTORS.md). These credits record
contributions, not an assertion of copyright ownership.

Original project contributions are offered under the complete Apache License
2.0 in `LICENSE`; dependency licenses and notices remain separate. The adapted
mathlib proof text retains its own attribution as described in `NOTICE`; no
motivating source PDFs are reproduced or other dependency files relicensed.
