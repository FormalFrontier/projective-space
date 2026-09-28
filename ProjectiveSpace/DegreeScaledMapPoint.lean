/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Hive Task hive-request-2ca332a8ced6485f6ca92c839afc566e562ec00c
  (UID 12e28acb-0999-4a80-b88f-3a412dbf506b, worker-a)
-/
module

public import ProjectiveSpace.DegreeScaledMap

@[expose] public section

set_option warningAsError true

/-!
# Underlying primes of degree-scaled projective morphisms

Computes the entire ordinary prime ideal at a point of the natural open domain of
`degreeScaledMap`, without restricting to positive homogeneous elements.
-/

noncomputable section

namespace AlgebraicGeometry.Proj

open CategoryTheory

universe u v w

variable {A B : Type u} {σ : Type v} {τ : Type w}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ]
variable (f : A →+* B) (d : ℕ) (hd : 0 < d)
  (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))

private theorem degreeScaledMap_decompose (hd : 0 < d)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n)) (x : A) (n : ℕ) :
    f (DirectSum.decompose 𝒜 x n : A) =
      (DirectSum.decompose ℬ (f x) (d * n) : B) := by
  classical
  let s := (DirectSum.decompose 𝒜 x).support
  have hs : (∑ j ∈ s, (DirectSum.decompose 𝒜 x j : A)) = x :=
    DirectSum.sum_support_decompose 𝒜 x
  have hfx : (∑ j ∈ s, f (DirectSum.decompose 𝒜 x j : A)) = f x := by
    rw [← map_sum, hs]
  symm
  calc
    (DirectSum.decompose ℬ (f x) (d * n) : B) =
        (DirectSum.decompose ℬ
          (∑ j ∈ s, f (DirectSum.decompose 𝒜 x j : A)) (d * n) : B) :=
      congrArg (fun y : B => (DirectSum.decompose ℬ y (d * n) : B)) hfx.symm
    _ = ∑ j ∈ s, (DirectSum.decompose ℬ
        (f (DirectSum.decompose 𝒜 x j : A)) (d * n) : B) := by
          rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
            AddSubmonoidClass.coe_finsetSum]
    _ = ∑ j ∈ s, if j = n then f (DirectSum.decompose 𝒜 x j : A) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : j = n
      · subst j
        simp only [ite_true]
        exact DirectSum.decompose_of_mem_same ℬ
          (hdeg n _ (DirectSum.decompose 𝒜 x n).property)
      · simp only [h, ite_false]
        exact DirectSum.decompose_of_mem_ne ℬ
          (hdeg j _ (DirectSum.decompose 𝒜 x j).property)
          (by intro heq; exact h (Nat.mul_left_cancel hd heq))
    _ = f (DirectSum.decompose 𝒜 x n : A) := by
      by_cases hn : n ∈ s
      · simp [Finset.sum_ite_eq', hn]
      · have hz : (DirectSum.decompose 𝒜 x n : A) = 0 := by
          have : DirectSum.decompose 𝒜 x n = 0 := DFinsupp.notMem_support_iff.mp hn
          simp [this]
        simp [Finset.sum_ite_eq', hn, hz]

private theorem degreeScaledMap_mem_of_pos (p : (degreeScaledDomain 𝒜 ℬ f).toScheme)
    {n : ℕ} (a : A) (ha : a ∈ 𝒜 n) (hn : 0 < n) :
    a ∈ ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal ↔
      f a ∈ (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal) := by
  have h := congrArg (fun V : (degreeScaledDomain 𝒜 ℬ f).toScheme.Opens => p ∈ V)
    (degreeScaledMap_preimage_basicOpen 𝒜 ℬ f d hd hdeg a ha hn)
  simpa only [Scheme.Hom.mem_preimage, mem_basicOpen, HomogeneousIdeal.mem_iff, not_not]
    using h.to_iff.not

private theorem degreeScaledMap_mem_of_zero (p : (degreeScaledDomain 𝒜 ℬ f).toScheme)
    (a : A) (ha : a ∈ 𝒜 0) :
    a ∈ ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal ↔
      f a ∈ (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal) := by
  classical
  have hp : (degreeScaledDomain 𝒜 ℬ f).ι p ∈ degreeScaledDomain 𝒜 ℬ f := p.property
  change (degreeScaledDomain 𝒜 ℬ f).ι p ∈
    (⨆ i : Σ n : PNat, 𝒜 n, chartOpen 𝒜 ℬ f i) at hp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  change f (i.2 : A) ∉
    (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal) at hi
  have hnot : (i.2 : A) ∉
      ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal := by
    intro h
    exact hi ((degreeScaledMap_mem_of_pos 𝒜 ℬ f d hd hdeg p
      (i.2 : A) i.2.2 i.1.2).mp h)
  have hamul : a * (i.2 : A) ∈ 𝒜 i.1 := by
    simpa only [zero_add] using (SetLike.mul_mem_graded ha i.2.2)
  have hmul := degreeScaledMap_mem_of_pos 𝒜 ℬ f d hd hdeg p
    (a * (i.2 : A)) hamul i.1.2
  let source := ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal
  let target := (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal)
  have hsource : source.IsPrime := (degreeScaledMap 𝒜 ℬ f d hd hdeg p).isPrime
  have htarget : target.IsPrime := ((degreeScaledDomain 𝒜 ℬ f).ι p).isPrime
  change a ∈ source ↔ f a ∈ target
  constructor
  · intro h
    have hm : a * (i.2 : A) ∈ source :=
      (Ideal.IsPrime.mul_mem_iff_mem_or_mem hsource).mpr (Or.inl h)
    have hfm : f a * f (i.2 : A) ∈ target := by
      rw [← map_mul]
      exact hmul.mp hm
    exact (htarget.mul_mem_iff_mem_or_mem.mp hfm).resolve_right hi
  · intro h
    have hfm : f (a * (i.2 : A)) ∈ target := by
      rw [map_mul]
      exact htarget.mul_mem_iff_mem_or_mem.mpr (Or.inl h)
    have hm : a * (i.2 : A) ∈ source := hmul.mpr hfm
    exact (hsource.mul_mem_iff_mem_or_mem.mp hm).resolve_right hnot

private theorem degreeScaledMap_comap_isHomogeneous (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    (p : (degreeScaledDomain 𝒜 ℬ f).toScheme) :
    (Ideal.comap f
      (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal)).IsHomogeneous 𝒜 := by
  intro n x hx
  change f x ∈ (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal) at hx
  change f (DirectSum.decompose 𝒜 x n : A) ∈
    (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal)
  rw [degreeScaledMap_decompose 𝒜 ℬ f d hd hdeg x n]
  exact ((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.isHomogeneous (d * n) hx

/-- The underlying ordinary prime of the open-domain degree-scaled morphism is
the ordinary contraction of the prime at the domain point, on every ring element. -/
theorem degreeScaledMap_pointIdeal (p : (degreeScaledDomain 𝒜 ℬ f).toScheme) :
    ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal =
      Ideal.comap f (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal) := by
  let source := ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal
  let target := Ideal.comap f
    (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal)
  have hsource : source.IsHomogeneous 𝒜 :=
    ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.isHomogeneous
  have htarget : target.IsHomogeneous 𝒜 :=
    degreeScaledMap_comap_isHomogeneous 𝒜 ℬ f d hd hdeg p
  change source = target
  ext x
  rw [hsource.mem_iff, htarget.mem_iff]
  apply forall_congr'
  intro n
  have hmem : (DirectSum.decompose 𝒜 x n : A) ∈ source ↔
      f (DirectSum.decompose 𝒜 x n : A) ∈
        (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal) := by
    by_cases hn : n = 0
    · subst n
      exact degreeScaledMap_mem_of_zero 𝒜 ℬ f d hd hdeg p _
        (DirectSum.decompose 𝒜 x 0).property
    · exact degreeScaledMap_mem_of_pos 𝒜 ℬ f d hd hdeg p _
        (DirectSum.decompose 𝒜 x n).property (Nat.pos_of_ne_zero hn)
  exact hmem

/-- Membership in the underlying prime of `degreeScaledMap` for an arbitrary
element, including degree-zero and inhomogeneous elements. -/
theorem degreeScaledMap_mem_pointIdeal (p : (degreeScaledDomain 𝒜 ℬ f).toScheme)
    (a : A) :
    a ∈ ((degreeScaledMap 𝒜 ℬ f d hd hdeg) p).asHomogeneousIdeal.toIdeal ↔
      f a ∈ (((degreeScaledDomain 𝒜 ℬ f).ι p).asHomogeneousIdeal.toIdeal) := by
  rw [degreeScaledMap_pointIdeal 𝒜 ℬ f d hd hdeg p]
  rfl

end AlgebraicGeometry.Proj
