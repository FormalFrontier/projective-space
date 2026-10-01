# Whole projective schemes from coherent graded tails

Import `ProjectiveSpace.CoherentTailProj` for the geometric results, or
`ProjectiveSpace` for the aggregate library. The algebraic input is
`GradedRing.Veronese.CoherentTail.TailEquiv 𝒜 ℬ N` from the official
`GradedRings.CoherentTailVeronese` dependency. It supplies a positive cutoff
`N`, a **ring** equivalence `E.zero` between the degree-zero components,
additive equivalences of the original components in every degree `d ≥ N`,
and their compatibility with coefficient multiplication and products of
high-degree components. It does not require a map of the original graded rings.

For `N ≤ n` and `0 < n`, use `E.selectedProjIso n hNn` for the entire selected
Veronese schemes and `E.projIso n hNn hn` for the entire original schemes:

```lean
E.selectedProjIso n hNn :
  Proj (GradedRing.Veronese.component 𝒜 n) ≅
    Proj (GradedRing.Veronese.component ℬ n)
E.projIso n hNn hn : Proj 𝒜 ≅ Proj ℬ
```

The construction uses the existing `ProjectiveSpace.projIsoOfInverseGradedRingHom`
on `E.selectedGradedHomSymm` and `E.selectedGradedHom`, then composes the
positive-Veronese whole-scheme isomorphism for `𝒜`, the selected isomorphism,
and the inverse positive-Veronese isomorphism for `ℬ`. Contravariance matters:
the selected A-to-B scheme arrow is the native `Proj.map` of the **inverse**
selected graded hom. `E.projIso_hom` records the actual composite arrow;
`E.projIso_comp_selected_inv` gives a cancellation formula. These are
isomorphisms of schemes with their structure sheaves, not merely point maps.

## Coefficients and maps

The new generic theorem `AlgebraicGeometry.Proj.map_toSpecZero`, in
`ProjectiveSpace.GradedProjIso`, compares native *whole-domain* graded `Proj.map`
to the actual degree-zero ring homomorphism:

```lean
Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
  Proj.toSpecZero ℬ ≫
    Spec.map (CommRingCat.ofHom (GradedRingHom.gradedZeroRingHom f))
```

Here `f : 𝒜 →+*ᵍ ℬ` and the native map hypothesis is
`hf : ℬ₊ ≤ 𝒜₊.map f`. Its proof compares the affine open cover and homogeneous
localizations; it is distinct from the positive degree-*scaled*, restricted-
domain coefficient theorem in `ProjectiveSpace.DegreeScaledMap`.
`E.selected_zero_spec` uses the algebra dependency's actual `E.selected_zero`
ring-hom identity. Combined with native `Proj.map_toSpecZero` and the existing
`Veronese.forward_toSpecZero` on both sides, it gives the actual morphism
triangle `E.projIso_toSpecZero` and inverse triangle
`E.projIso_inv_toSpecZero`:

```lean
(E.projIso n hNn hn).hom ≫ Proj.toSpecZero ℬ ≫
  Spec.map (CommRingCat.ofHom E.zero.toRingHom) = Proj.toSpecZero 𝒜
(E.projIso n hNn hn).inv ≫ Proj.toSpecZero 𝒜 =
  Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom E.zero.toRingHom)
```

The generic result and selected map use mathlib's native same-universe
`Proj.map`: the two **underlying rings** must inhabit one universe, while the
original grading-carrier universes may differ. The hypotheses do not imply
an original-ring graded homomorphism extending the tail across exceptional
positive low degrees, cutoff independence, finite generation, generation in
degree one, a domain, reducedness, a field, or `Nontrivial`.

## Examples and reproduction

The [production module](../ProjectiveSpace/CoherentTailProj.lean) exposes these
results. [`ProjectiveSpaceTest.CoherentTailProjClient`](../ProjectiveSpaceTest/CoherentTailProjClient.lean)
is a test-only client; it imports
the **flat** `CoherentTailVeronese` module from the published Graded Rings
`GradedRingsTests` target (source directory `test`, namespace
`GradedRingsTest.CoherentTailVeronese`). It reuses its missing-linear
integer-polynomial example and the genuine theorem
`missingLinear_no_extension`: a hypothetical graded map agreeing with the
original high-component identity **for every high-degree element** is
impossible, although the entire Proj schemes are isomorphic. It also checks
the nonidentity degree-zero coefficient swap on `(ZMod 4 × ZMod 4)[t]`, the
actual coefficient triangle and both scheme inverse laws, and a `ZMod 1`
example without `Nontrivial`. The separate private generic witness in
`ProjectiveSpaceTest.RootClient` imports only the aggregate production root.
The concrete fixture is not a production dependency or copied into this
repository.

For the pinned Lean `v4.34.0-rc2` and dependencies in `lakefile.toml` and
`lake-manifest.json`, a reproducing checkout must fetch the matching
precompiled mathlib cache **before** building the four registered targets:

```sh
lake exe cache get
lake build ProjectiveSpace ProjectiveSpaceTest \
  ProjectiveSpaceAxiomTests ProjectiveSpaceReaderExamples
```

The upstream algebra is supplied by official Graded Rings release
`db2a1d555639e2a381abbf755982ffdcf126621e`. The original 43-file
destination graph, including the cross-package fixture and client, passed a
four-target build and complete private/generated-inclusive transitive
standard-three audit on its recorded original inputs. Later changed-header
revisions require an evidence-applicability decision and their own independent
review; neither a guide nor the upstream check alone certifies such changes.

The mathematical motivation includes Ravi Vakil, *The Rising Sea*, October 21,
2025 draft, §7.4.4, Exercise 7.4.F (printed p. 215); coefficient conventions
appear on pp. 151–152. No source text is copied here, and the library makes
no source-correspondence or coverage assertion. The original coherent-tail
algebra, original geometry, official Graded Rings adaptation and this
destination transfer have distinct contributor credits in `CONTRIBUTORS.md`.
