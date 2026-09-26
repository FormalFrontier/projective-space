/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Contributors: Atlas and Formal Frontier contributors (AI-assisted)
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Positive-degree projective basic opens

For an arbitrary naturally graded commutative ring, this file packages the
positive-degree homogeneous projective basic opens and proves that they form a
topological basis of `Proj`.
-/

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.Proj

universe u v

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The projective basic opens associated to positive-degree homogeneous
elements. -/
def positiveBasicOpens : Set (Set (Proj 𝒜)) :=
  Set.range fun i : Σ n : PNat, 𝒜 (n : ℕ) =>
    (Proj.basicOpen 𝒜 (i.2 : A) : Set (Proj 𝒜))

/-- The positive-degree homogeneous projective basic opens form a topological
basis of `Proj`. -/
theorem isTopologicalBasis_positiveBasicOpens :
    TopologicalSpace.IsTopologicalBasis (positiveBasicOpens 𝒜) := by
  classical
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨i, rfl⟩
    exact (Proj.basicOpen 𝒜 (i.2 : A)).isOpen
  · intro x U hxU hU
    let U' : TopologicalSpace.Opens (Proj 𝒜) := ⟨U, hU⟩
    have hxU' : x ∈ U' := hxU
    have hb : ∀ {V : TopologicalSpace.Opens (Proj 𝒜)} {y : Proj 𝒜}, y ∈ V →
        ∃ V' ∈ Set.range (Proj.basicOpen 𝒜), y ∈ V' ∧ V' ≤ V :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen 𝒜)
    obtain ⟨_, ⟨r, rfl⟩, hxr, hrU⟩ := hb hxU'
    rw [Proj.basicOpen_eq_iSup_proj] at hxr
    obtain ⟨n, hxn⟩ := TopologicalSpace.Opens.mem_iSup.mp hxr
    obtain ⟨a, ha, hax⟩ := SetLike.not_le_iff_exists.mp x.not_irrelevant_le
    have hex : ∃ j : ℕ, GradedRing.proj 𝒜 j a ∉ x.asHomogeneousIdeal := by
      by_contra! H
      apply hax
      rw [← DirectSum.sum_support_decompose 𝒜 a]
      exact Ideal.sum_mem _ fun j _ => H j
    obtain ⟨j, hj⟩ := hex
    have hj0 : j ≠ 0 := by
      intro hj0
      subst j
      rw [(HomogeneousIdeal.mem_irrelevant_iff 𝒜 a).mp ha] at hj
      exact hj (Ideal.zero_mem _)
    let e : PNat := ⟨j, Nat.pos_iff_ne_zero.mpr hj0⟩
    let i : 𝒜 (e : ℕ) :=
      ⟨GradedRing.proj 𝒜 j a, by
        rw [GradedRing.proj_apply]
        exact ((DirectSum.decompose 𝒜) a j).2⟩
    have hxi : x ∈ Proj.basicOpen 𝒜 (i : A) := hj
    let d : PNat := ⟨n + (e : ℕ), Nat.add_pos_right n e.2⟩
    let q : 𝒜 (d : ℕ) :=
      ⟨GradedRing.proj 𝒜 n r * (i : A),
        SetLike.mul_mem_graded (by
          rw [GradedRing.proj_apply]
          exact ((DirectSum.decompose 𝒜) r n).2) i.2⟩
    refine ⟨(Proj.basicOpen 𝒜 (q : A) : Set (Proj 𝒜)), ⟨⟨d, q⟩, rfl⟩, ?_, ?_⟩
    · rw [show (q : A) = GradedRing.proj 𝒜 n r * (i : A) by rfl,
        Proj.basicOpen_mul]
      exact ⟨hxn, hxi⟩
    · intro y hy
      apply hrU
      rw [show (q : A) = GradedRing.proj 𝒜 n r * (i : A) by rfl,
        Proj.basicOpen_mul] at hy
      rw [Proj.basicOpen_eq_iSup_proj]
      exact (le_iSup (fun k => Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 k r)) n) hy.1

end AlgebraicGeometry.Proj
