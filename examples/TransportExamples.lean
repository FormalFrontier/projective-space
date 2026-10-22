/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveSpace.GradedProjIso

/-!
# Transport along inverse graded ring homomorphisms

Use independent universes `uA`, `uB`, `uσ`, and `uτ` for
`A : Type uA`, `B : Type uB`, `σ : Type uσ`, and `τ : Type uτ`.
Both rings are commutative. The grade carriers have `SetLike σ A`,
`AddSubgroupClass σ A`, `SetLike τ B`, and `AddSubgroupClass τ B`.
Let `𝒜 : ℕ → σ` and `ℬ : ℕ → τ` have `GradedRing 𝒜` and `GradedRing ℬ`.

Take `f : 𝒜 →+*ᵍ ℬ` and `g : ℬ →+*ᵍ 𝒜`, with
`hfg : f.comp g = GradedRingHom.id ℬ` and
`hgf : g.comp f = GradedRingHom.id 𝒜`.
Both composition identities are inputs, not consequences of an arbitrary
graded homomorphism.

## Roundtrip on the projective spectrum

The producer
`ProjectiveSpace.projectiveSpectrumEquivOfInverseGradedRingHom f g hfg hgf`
sends `p : ProjectiveSpectrum ℬ` to the spectrum for `𝒜`.
Writing this equivalence as `e`, its existing field `e.left_inv p` proves
`e.symm (e p) = p`. Use that equivalence law directly rather than a
specialized roundtrip lemma. Notice the contravariant direction relative
to `f`.

## Underlying point of transported closed points

For `p : closedPoints (AlgebraicGeometry.Proj ℬ)`, apply
`ProjectiveSpace.projClosedPointsEquivOfInverseGradedRingHom_apply_coe
  f g hfg hgf p`.
It identifies
`(ProjectiveSpace.projClosedPointsEquivOfInverseGradedRingHom
  f g hfg hgf p).1`
with
`AlgebraicGeometry.ProjectiveSpectrum.comapFun f
  (ProjectiveSpace.irrelevant_le_map_of_comp_eq_id f g hfg) p.1`.
If needed, `simpa only using` this existing equality gives that precise
underlying-point statement. The irrelevant-ideal condition is supplied
by the named producer using `hfg`; the closed-point equivalence itself
still takes both inverse identities. This recipe concerns the underlying
point of a closed-point subtype, not an extra scheme-level isomorphism.
-/
