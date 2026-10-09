# Unit scaling of Proj morphisms

Import `ProjectiveSpace.UnitScaling` for this API alone, or import
`ProjectiveSpace` for the whole library. Both expose the eight declarations
below in `AlgebraicGeometry.Proj`. The direct-public-import client is
`ProjectiveSpaceTest.UnitScalingClient`; its five test-namespace theorems
are not imported by the mathematical library root. The geometric-cover
constructor being compared is described in the [global-sections guide](GlobalSections.md);
see also the [module and API map](MODULES.md).

Degree-weighted multiplication by a global unit preserves **entire** scheme
morphisms arising from two evaluations of a graded ring in global sections.
Let `𝒜` grade a commutative ring `A` by `ℕ` (with `SetLike σ A`,
`AddSubgroupClass σ A` and `GradedRing 𝒜`), let `X : Scheme.{u}` have the same
universe as `A : Type u`, and let `f g : A →+* Γ(X, ⊤)` be *ordinary unital ring
maps*. Suppose `unit : Γ(X, ⊤)ˣ` and, for **every** homogeneous `a ∈ 𝒜 d`,
`g a = (unit : Γ(X, ⊤))^d * f a`. If the actual basic opens of
positive-degree homogeneous `f a` cover `X`, then those for `g a` also cover
`X`, and `Proj.fromOfGlobalSectionsOfIsOpenCover 𝒜 f` equals
`Proj.fromOfGlobalSectionsOfIsOpenCover 𝒜 g` **as a scheme arrow**. Both
witnesses of the geometric cover can alternatively be supplied independently.

## Public interface

- `Proj.awayMapOfIsUnit` evaluates degree-zero homogeneous fractions when
  the denominator maps to a unit in any commutative target ring.
- `Proj.awayMapOfIsUnit_mk_spec` specifies evaluation by cross-multiplication,
  with no inverse operation required in the target.
- `Proj.awayMapOfIsUnit_eq_of_unitScaling` compares all fractions after
  weighted unit scaling, including degenerate localizations.
- `Proj.basicOpen_eq_of_unitScaling` identifies each pair of source opens.
- `Proj.isOpenCover_of_unitScaling` transfers the actual geometric cover.
- `Proj.toBasicOpenOfGlobalSections_eq_of_unitScaling` identifies complete
  affine-chart arrows after the named source-open isomorphism.
- `Proj.fromOfGlobalSectionsOfIsOpenCover_eq_of_unitScaling` compares the
  complete arrows with two independently supplied cover witnesses.
- `Proj.fromOfGlobalSectionsOfIsOpenCover_unitScaling` compares the complete
  arrows using a single cover for `f`, transferring the cover for `g`.

## Why the comparison is local

For a positive-degree homogeneous `t ∈ 𝒜 d`, the unit makes
`D(f t) = D(g t)`. A degree-zero fraction `a/t^k` in the chart has
`a ∈ 𝒜 (k • d)`. Its numerator changes by `unit^(k • d)`, while the
denominator changes by `(unit^d)^k`: both factors are equal. The proof
uses `HomogeneousLocalization.Away.mk_surjective`, including its degenerate
nilpotent case, to check *all* elements of the common chart ring.

For scheme arrows, fractions are evaluated in sections of the **same source
open**. The ordinary localizations of `Γ(X, ⊤)` at `f t` and `g t` are
different intermediates and are not assumed definitionally identical.
Affine-arrow extensionality upgrades equality of the corresponding ring maps
to equality of complete chart morphisms; source-open-cover extensionality
then yields equality of complete arrows into `Proj 𝒜`. No affine, reduced,
domain, field, nonzero-chart, or global-irrelevant-ideal-equals-top hypothesis
is used. Empty opens, nilpotents and zero rings are included. This does not
classify maps into projective space or add a polynomial specialization.

## Using this result

The [client](../ProjectiveSpaceTest/UnitScalingClient.lean) directly imports
the [producer](../ProjectiveSpace/UnitScaling.lean); the
[reader guide](../README.md) supplies the cache-first four-target build recipe.
A Formal Frontier AI-agent contributor developed the original producer and
client; a separate contributor adapted the producer for this library and wrote
this guide. The chart construction and gluing adapt Andrew Yang's 2024 mathlib
work; his Apache-2.0 notice remains in the producer. See
[`CONTRIBUTORS.md`](../CONTRIBUTORS.md) and [`NOTICE`](../NOTICE).
