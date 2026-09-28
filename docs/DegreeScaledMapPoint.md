# Underlying primes of positive-degree-scaled Proj morphisms

**Public import:** `ProjectiveSpace.DegreeScaledMapPoint` (or the aggregate
`ProjectiveSpace`). **Status:** the producer is in verified official release
`ad60036d9745d4f0bca2f398538cff4377c93603`. This separate point-prime
leaf received independent affected-destination review 4399 and native run 647
at exact code revision `8712cd1d042032ba4577145b3a3034ed2609e671`:
all four targets and 39 Lean files built, and the complete transitive audit
included private and generated declarations with only the three standard
axioms. Atlas accepted and integrated that code on September 28, 2026.
The original isolated point proof had its own earlier review and acceptance;
the destination review and checks are distinct. Release acceptance and
verified publication require separate revision-specific decisions.

For commutative rings `A` and `B` in the same underlying-ring universe, arbitrary
independently represented `ℕ`-gradings `𝒜` and `ℬ` (whose grading-carrier types
may inhabit different universes), an ordinary unital ring homomorphism
`f : A →+* B`, `d : ℕ` with `hd : 0 < d`, and
`hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n)`, the existing
`degreeScaledMap 𝒜 ℬ f d hd hdeg` maps the actual open domain
`U = degreeScaledDomain 𝒜 ℬ f` into `Proj 𝒜`. For **every** `p : U.toScheme`,
`degreeScaledMap_pointIdeal` proves equality of entire **ordinary** ideals:

```lean
((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal =
  Ideal.comap f ((U.ι p).asHomogeneousIdeal.toIdeal)
```

`degreeScaledMap_mem_pointIdeal` immediately gives membership equivalence
`a ∈ ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal ↔
f a ∈ ((U.ι p).asHomogeneousIdeal.toIdeal)` for **any** `a : A`, without
requiring it to have positive degree or to be homogeneous. The test-only
`ProjectiveSpaceTest.DegreeScaledMapPointClient` directly imports this leaf
and checks ideal equality, arbitrary-element membership and a dedicated
degree-zero element of `𝒜 0`.

The proof uses the accepted positive-basic-open preimage theorem for homogeneous
positive degrees. At degree zero, it takes a positive image-chart witness from
the domain and applies the positive law to its product with the tested element;
primality cancels the witness on both sides. For all elements, it decomposes the
source into its homogeneous components, shows that `f` commutes with the component
at `n` and the component at `d * n` using `d > 0`, then applies native
`Ideal.IsHomogeneous.mem_iff` on the two ideals. No second morphism, inverse,
new regrading framework, or global irrelevant-ideal containment is assumed.

The theorem also covers empty Proj/domain cases vacuously and zero or nilpotent
image charts (which contribute no domain points). It makes no nonemptiness,
domain, field, reducedness, finite-generation, degree-one-generation,
injectivity or surjectivity assumption; it does not assert that the morphism
extends beyond `U`. In particular, the contraction formula is *not* obtained
by silently replacing the actual open domain with all of `Proj ℬ`.

**Provenance and credit:** The original point-ideal proof and client
are by Formal Frontier Hive Task
`hive-request-2ca332a8ced6485f6ca92c839afc566e562ec00c`, UID
`12e28acb-0999-4a80-b88f-3a412dbf506b`, worker-a. The bounded destination
copy, import/namespace adaptation and guide were prepared by worker-b Hive
Task `hive-request-197d52a7faa4409faaaac7f6900b65c94f27f679` (UID
`f53c2615-2efd-484d-80e0-2a9ef1edc8ec`), not as new mathematical
authorship. The point proof builds on the `DegreeScaledMap` producer by Task
`hive-request-c02fd45fba823c878651639dde4a50bf798e1cc4` (UID
`f1443f68-aae3-4e03-989a-43eac40bc9a9`, worker-b) and the published
`GradedRings.HomogeneousLocalizationMap` contribution by Hive Task
`hive-request-b0b74cdb7e102204e305196597835a728b60ad9a` (UID
`02a35b9d-d5a4-4ab9-bebc-4d467cf904c6`, worker-a). Native Proj chart/gluing
technology credits Andrew Yang; homogeneous-localization technology credits
Jujian Zhang and Eric Wieser. Mathlib supplies the native graded decomposition,
homogeneous ideals and prime-ideal lemmas. The code carries the Apache-2.0 SPDX
identifier consistent with the imported producer and upstream mathlib license;
this description makes no blanket rights or clearance claim about other material.

**Reproduction after checks are authorized:** Use this repository's unchanged
`lakefile.toml`, `lake-manifest.json` and `lean-toolchain`
(`leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, official Graded Rings
`f77410141b89532409fff563d368930a728f55b7` and official Scheme Properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00`). With access to the
private dependencies, from the Projective Space root:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
lake --wfail build
```

The cache fetch must succeed before building the four default targets. These
are reproduction instructions, not a claim that a later documentary or release
revision was rebuilt. Native run 647 checked the accepted code revision above,
including private and generated declarations, with transitive axioms limited
to `propext`, `Classical.choice` and `Quot.sound`. Release review, acceptance
and verified publication are distinct from that code acceptance; source
correspondence and coverage are separate.
