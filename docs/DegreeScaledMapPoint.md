# Underlying primes of positive-degree-scaled Proj morphisms

**Public import:** [the point-prime leaf](../ProjectiveSpace/DegreeScaledMapPoint.lean)
or the aggregate `ProjectiveSpace`. The [direct client](../ProjectiveSpaceTest/DegreeScaledMapPointClient.lean)
checks both the full ideal equality and arbitrary-element membership. This
point result uses the separate [degree-scaled producer](DegreeScaledMap.md)
and its actual open domain, not a global morphism.

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

The proof uses the positive-basic-open preimage theorem for homogeneous
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

**Provenance and credit:** A Formal Frontier AI-agent contributor wrote
the original point-prime proof and client; another adapted the point leaf for
this library and wrote this guide. The point proof builds on the separately
authored `DegreeScaledMap` producer and official Graded Rings localization
contribution.
Mathlib chart/gluing work credits Andrew Yang, and mathlib homogeneous
localization credits Jujian Zhang and Eric Wieser. Mathlib also supplies
native graded decomposition and homogeneous ideal/prime lemmas. See
[`CONTRIBUTORS.md`](../CONTRIBUTORS.md) and [`NOTICE`](../NOTICE) for distinct
roles and license notices, not blanket rights clearance.

**Reproduction:** Use this repository's
`lakefile.toml`, `lake-manifest.json` and `lean-toolchain`
(`leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, official Graded Rings
`db2a1d555639e2a381abbf755982ffdcf126621e` and official Scheme Properties
`6b204a3e49f022e51d78a9f93e77513b99a87e00`). With access to
the private dependencies, from the Projective Space root:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
lake --wfail build
```

The cache fetch must succeed before building the four default targets.
