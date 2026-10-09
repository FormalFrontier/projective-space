# Proj morphisms from geometrically covering global sections

Import `ProjectiveSpace.GlobalSections` for this API alone, or import
`ProjectiveSpace` for the full library. Both expose the declarations in
`AlgebraicGeometry.Proj`; the test-only
`ProjectiveSpaceTest.GlobalSectionsClient` exercises the direct public import.
The client's declarations are public Lean names in its test namespace, not
private declarations; the mathematical library root does not import them.

## Geometric hypothesis and construction

Let `A : Type u` be a commutative ring with grading `𝒜 : ℕ → σ` (with
`SetLike σ A`, `AddSubgroupClass σ A` and `GradedRing 𝒜`), let
`X : Scheme.{u}`, and let `f : A →+* Γ(X, ⊤)` be an **ordinary ring homomorphism
from the graded ring** to global sections. There is no grading on the target
in this API. Assume the *actual* positive-degree homogeneous basic opens of
`X` cover it:

```lean
hcover : TopologicalSpace.IsOpenCover
  (fun ir : Σ' n r, 0 < n ∧ r ∈ 𝒜 n ↦ X.basicOpen (f ir.2.1))
```

Then `Proj.fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcover : X ⟶ Proj 𝒜`.
`Proj.openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcover` is the associated
`Scheme.OpenCover`. The construction glues mathlib's existing full chart
morphisms `Proj.toBasicOpenOfGlobalSections` on intersections of source basic
opens; no affine hypothesis, ideal-equals-top hypothesis, nonempty-source
assumption, pre-existing map to `Proj`, or separately assumed overlap equality
is required.

## Chart and base identities

For every `r : A` of degree `n > 0` (that is, `r ∈ 𝒜 n`), the following
declarations describe the map:

- `Proj.fromOfGlobalSectionsOfIsOpenCover_preimage_basicOpen` identifies the
  inverse image of `Proj.basicOpen 𝒜 r` with `X.basicOpen (f r)`.
- `Proj.fromOfGlobalSectionsOfIsOpenCover_morphismRestrict` identifies the
  target-chart restriction with the existing chart arrow, after transporting
  along the equality of source opens.
- `Proj.fromOfGlobalSectionsOfIsOpenCover_resLE` identifies the restricted
  arrow from `X.basicOpen (f r)` with
  `Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hn hr`.
- `Proj.fromOfGlobalSectionsOfIsOpenCover_toSpecZero` identifies **whole**
  scheme morphisms to the degree-zero affine spectrum:

```lean
Proj.fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcover ≫ Proj.toSpecZero 𝒜 =
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (f.comp (algebraMap _ _)))
```

The separate
`Proj.fromOfGlobalSectionsOfIsOpenCover_eq_fromOfGlobalSections`
recovers mathlib's `Proj.fromOfGlobalSections 𝒜 f hf` when its **stronger**
native assumption `(HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤` is
available. That stronger assumption supplies a geometric cover, but a
geometric cover is not asserted to imply it. This general scheme-level API
does not itself specialize to polynomials or classify maps into projective
space.

## Build and attribution

The library pins Lean `leanprover/lean4:v4.34.0-rc2` and mathlib commit
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; see the repository
`lake-manifest.json` for the entire resolved dependency graph. With access
to the pinned dependencies, fetch the matching mathlib cache first, then
check the two affected modules with warnings fatal:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build +ProjectiveSpace.GlobalSections:olean
LEAN_NUM_THREADS=2 lake --wfail build +ProjectiveSpaceTest.GlobalSectionsClient:olean
```

For the four library targets, see the [reader guide](../README.md). The
[module map](MODULES.md) links the producer and direct client.

The gluing and chart arguments adapt `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`
by Andrew Yang (copyright 2024, Apache-2.0); his attribution and license
are preserved in the producer. One Formal Frontier AI-agent contributor
prepared the original adaptation, direct client and starting guide; another
provided its library import and revised this guide. See
[`CONTRIBUTORS.md`](../CONTRIBUTORS.md) and [`NOTICE`](../NOTICE) for these
distinct roles and authentic third-party notices, not blanket rights clearance.
