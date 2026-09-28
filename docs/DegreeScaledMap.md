# Positive-degree-scaled maps of projective spectra

Import `ProjectiveSpace.DegreeScaledMap` for the leaf, or `ProjectiveSpace` for
the aggregate library. The ordinary-import examples in
[`ProjectiveSpaceTest.DegreeScaledMapClient`](../ProjectiveSpaceTest/DegreeScaledMapClient.lean)
exercise the scheme arrow, chart, fractions, basic opens, base triangle and
uniqueness. The destination code revision
`d866ec190766ef2a76978fadc05627717f300468` received independent
promotion review 4376, a complete native four-target build and transitive
standard-axiom audit in run 632, and maintainer code acceptance on
September 27, 2026. This guide does not itself certify a later documentary
revision. The reviewed producer is now in verified official release
`ad60036d9745d4f0bca2f398538cff4377c93603`. The separate point-prime
leaf received its own independent affected review 4399 and native run 647
on exact code revision `8712cd1d042032ba4577145b3a3034ed2609e671`;
Atlas accepted and integrated it on September 28, 2026. Neither code
acceptance nor this guide certifies a later point-prime release.

## Data and domain

Let `𝒜 : ℕ → σ` and `ℬ : ℕ → τ` grade commutative rings `A` and `B`. The
underlying rings share a Lean type universe for the native scheme category;
their grading-value carrier types may have different universes. Give an
**ordinary unital** ring homomorphism `f : A →+* B`, a multiplier `d : ℕ`,
`hd : 0 < d` and

```lean
hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n)
```

No finite generation, integral-domain, reducedness, degree-one generation,
nontriviality or global image-nonvanishing hypothesis is required. Positivity
is necessary for this Proj construction; no `d = 0` Proj arrow is asserted.

`imageIrrelevant 𝒜 f : Ideal B` is the image of the source irrelevant ideal.
`chartOpen 𝒜 ℬ f i` is the image basic open `D₊(f a)` indexed by a
positive homogeneous source element `i : Σ n : PNat, 𝒜 n` with `a := i.2`.
The union `U := degreeScaledDomain 𝒜 ℬ f` is an open of `Proj ℬ`;
`degreeScaledDomain_eq_zeroLocus_compl` identifies its underlying set with
the complement of `ProjectiveSpectrum.zeroLocus ℬ (imageIrrelevant 𝒜 f)`.
Vanishing image charts and an empty `U` are allowed. `chartCover 𝒜 ℬ f`
covers precisely this open, not necessarily all of `Proj ℬ`.

## Scheme arrow and computations

The main declaration constructs an actual scheme morphism, not merely a
function on points:

```lean
degreeScaledMap 𝒜 ℬ f d hd hdeg : U.toScheme ⟶ Proj 𝒜
```

`degreeScaledChartMap` constructs each chart arrow. The theorem
`degreeScaledChartMap_compatible` proves equality on **both faces** of
each pullback overlap, so compatibility is not an input. `chartCover_map`
identifies the glued arrow's restriction with that chart arrow. In particular,
`degreeScaledMap_chartSpec` computes the **whole** arrow from an image affine
chart, after the inverse `basicOpenIsoSpec`, as

```lean
Spec.map (CommRingCat.ofHom
  (Away.mapDegreeMul 𝒜 ℬ f d hdeg (i.2 : A))) ≫
    awayι 𝒜 (i.2 : A) i.2.2 i.1.2
```

The official `GradedRings.HomogeneousLocalizationMap` supplies
`Away.mapDegreeMul_mk`: a homogeneous fraction `b/a^k` maps to
`f(b)/(f(a))^k` with numerator and denominator degrees multiplied by `d`.
The chart equation therefore also specifies the structure-sheaf map. The
theorem `degreeScaledMap_unique` says that this family of chart equations
uniquely determines any arrow `U.toScheme ⟶ Proj 𝒜`.

For `r ∈ 𝒜 n` with `0 < n`, the inverse image is **an open of `U`**:

```lean
degreeScaledMap 𝒜 ℬ f d hd hdeg ⁻¹ᵁ basicOpen 𝒜 r =
  U.ι ⁻¹ᵁ basicOpen ℬ (f r)
```

This is `degreeScaledMap_preimage_basicOpen`; the preceding chart-level
`degreeScaledChartSpec_preimage_basicOpen` and
`degreeScaledChartMap_preimage_basicOpen` are also available. The supporting
`mapDegreeMul_isLocalizationElem_pow` gives the chart parameter power law.
This producer theorem concerns **positive-degree homogeneous basic opens**.
For the separate **entire ordinary point-prime contraction** law and
membership for every element (including degree zero and inhomogeneous ones),
import `ProjectiveSpace.DegreeScaledMapPoint` and see
[`DegreeScaledMapPoint.md`](DegreeScaledMapPoint.md). That point leaf retains
the same actual domain `U` and hypotheses; it is not a globality extension.

`degreeZeroRingHom 𝒜 ℬ f d hdeg : 𝒜 0 →+* ℬ 0` restricts `f` to
degree-zero components. `mapDegreeMul_fromZeroRingHom` and
`degreeScaledChart_base` give its localized and chart equations, while
`degreeScaledMap_toSpecZero` identifies the whole base triangle:

```lean
degreeScaledMap 𝒜 ℬ f d hd hdeg ≫ toSpecZero 𝒜 =
  U.ι ≫ toSpecZero ℬ ≫
    Spec.map (CommRingCat.ofHom (degreeZeroRingHom 𝒜 ℬ f d hdeg))
```

The module builds on native mathlib Proj charts, gluing and pullbacks and on
the official Graded Rings degree-multiplying localization map. It neither
claims a global `Proj ℬ ⟶ Proj 𝒜` without an image-chart cover nor proves
composition, classification or a radical globality condition. Its own
positive-basic-open theorem is the input to the **separate** point-prime
leaf, not a claim that this producer leaf itself exports the all-element
contraction formula. Dependency and original adapted-mathlib credits
are recorded in [`CONTRIBUTORS.md`](../CONTRIBUTORS.md) and
[`NOTICE`](../NOTICE); the complete public API is mapped in
[`MODULES.md`](MODULES.md).
