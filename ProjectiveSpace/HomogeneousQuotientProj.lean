/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Contributors: Atlas and Formal Frontier contributors (AI-assisted)
-/
module

public import GradedRings.Quotient
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Proj of a homogeneous quotient

For a homogeneous ideal `I` in an `ℕ`-graded commutative ring, this file constructs the
canonical morphism from `Proj (A ⧸ I)` to `Proj A`. It proves that the morphism is a closed
immersion and that its range on points is the projective zero locus of `I`.
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousIdeal

namespace Ideal.Quotient

section ProjectiveSpectrum

universe u v

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (I : Ideal A) (hI : I.IsHomogeneous 𝒜)

/-- Every positive-degree component of the quotient grading is in the image of the source
irrelevant ideal. -/
theorem quotient_irrelevant_le_map :
    letI := gradedRing 𝒜 I hI
    (gradedComponent 𝒜 I)₊ ≤ 𝒜₊.map (gradedRingHom 𝒜 I) := by
  let _ := gradedRing 𝒜 I hI
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  rcases hx with ⟨a, ha, rfl⟩
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi ha)

/-- A relevant homogeneous prime containing `I`, regarded as a point of the projective spectrum
of the quotient. -/
@[expose] noncomputable def projectiveSpectrumPoint
    (p : ProjectiveSpectrum 𝒜) (hIp : I ≤ p.asHomogeneousIdeal.toIdeal) :
    letI := gradedRing 𝒜 I hI
    ProjectiveSpectrum (gradedComponent 𝒜 I) := by
  letI := gradedRing 𝒜 I hI
  let q := gradedRingHom 𝒜 I
  have hsurj : Function.Surjective q := gradedRingHom_surjective 𝒜 I
  refine
    { asHomogeneousIdeal := p.asHomogeneousIdeal.map q
      isPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
      not_irrelevant_le := ?_ }
  · simpa only [q, Ideal.mk_ker] using hIp
  · intro hirr
    apply p.not_irrelevant_le
    rw [HomogeneousIdeal.irrelevant_le]
    intro i hi x hx
    have hqx : q x ∈ (gradedComponent 𝒜 I)₊ :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ hi (q.map_mem hx)
    have hqmap : q x ∈ (p.asHomogeneousIdeal.map q).toIdeal := hirr hqx
    have hxcomap : x ∈ (p.asHomogeneousIdeal.map q).toIdeal.comap q := hqmap
    rw [HomogeneousIdeal.toIdeal_map,
      Ideal.comap_map_of_surjective q hsurj] at hxcomap
    have hker : Ideal.comap q (⊥ : Ideal (A ⧸ I)) = I := by
      change RingHom.ker (Ideal.Quotient.mk I) = I
      exact Ideal.mk_ker
    rwa [hker, sup_eq_left.mpr hIp] at hxcomap

theorem projectiveSpectrumPoint_comap
    (p : ProjectiveSpectrum 𝒜) (hIp : I ≤ p.asHomogeneousIdeal.toIdeal) :
    letI := gradedRing 𝒜 I hI
    ProjectiveSpectrum.comapFun (gradedRingHom 𝒜 I)
        (quotient_irrelevant_le_map 𝒜 I hI)
        (projectiveSpectrumPoint 𝒜 I hI p hIp) = p := by
  let _ := gradedRing 𝒜 I hI
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  change Ideal.comap (gradedRingHom 𝒜 I)
      (Ideal.map (gradedRingHom 𝒜 I) p.asHomogeneousIdeal.toIdeal) = _
  rw [Ideal.comap_map_of_surjective _ (gradedRingHom_surjective 𝒜 I)]
  have hker : Ideal.comap (gradedRingHom 𝒜 I) (⊥ : Ideal (A ⧸ I)) = I := by
    change RingHom.ker (Ideal.Quotient.mk I) = I
    exact Ideal.mk_ker
  rw [hker, sup_eq_left.mpr hIp]

/-- The points in the image of `Proj (A ⧸ I) → Proj A` are exactly the projective zero locus
of `I`. -/
theorem range_projectiveSpectrum_comap :
    letI := gradedRing 𝒜 I hI
    Set.range (ProjectiveSpectrum.comap (gradedRingHom 𝒜 I)
      (quotient_irrelevant_le_map 𝒜 I hI)) =
      ProjectiveSpectrum.zeroLocus 𝒜 (I : Set A) := by
  let _ := gradedRing 𝒜 I hI
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    rw [ProjectiveSpectrum.mem_zeroLocus]
    change I ≤ q.asHomogeneousIdeal.toIdeal.comap (gradedRingHom 𝒜 I)
    exact Ideal.mk_ker.symm.trans_le (Ideal.ker_le_comap _)
  · intro hp
    rw [ProjectiveSpectrum.mem_zeroLocus] at hp
    refine ⟨projectiveSpectrumPoint 𝒜 I hI p hp, ?_⟩
    exact projectiveSpectrumPoint_comap 𝒜 I hI p hp

theorem image_projectiveSpectrum_comap_zeroLocus (s : Set (A ⧸ I)) :
    letI := gradedRing 𝒜 I hI
    ProjectiveSpectrum.comap (gradedRingHom 𝒜 I)
        (quotient_irrelevant_le_map 𝒜 I hI) ''
        ProjectiveSpectrum.zeroLocus (gradedComponent 𝒜 I) s =
      ProjectiveSpectrum.zeroLocus 𝒜 ((gradedRingHom 𝒜 I ⁻¹' s) ∪ (I : Set A)) := by
  let _ := gradedRing 𝒜 I hI
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [ProjectiveSpectrum.mem_zeroLocus] at hq ⊢
    rintro x (hx | hx)
    · exact hq hx
    · change x ∈ q.asHomogeneousIdeal.toIdeal.comap (gradedRingHom 𝒜 I)
      exact Ideal.mk_ker.symm.trans_le (Ideal.ker_le_comap _) hx
  · intro hp
    rw [ProjectiveSpectrum.mem_zeroLocus] at hp
    have hIp : I ≤ p.asHomogeneousIdeal.toIdeal := fun x hx ↦ hp (Or.inr hx)
    let q := projectiveSpectrumPoint 𝒜 I hI p hIp
    refine ⟨q, ?_, projectiveSpectrumPoint_comap 𝒜 I hI p hIp⟩
    rw [ProjectiveSpectrum.mem_zeroLocus]
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact Ideal.mem_map_of_mem _ (hp (Or.inl hy))

theorem projectiveSpectrum_comap_injective :
    letI := gradedRing 𝒜 I hI
    Function.Injective (ProjectiveSpectrum.comap (gradedRingHom 𝒜 I)
      (quotient_irrelevant_le_map 𝒜 I hI)) := by
  let _ := gradedRing 𝒜 I hI
  intro p q hpq
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  apply Ideal.comap_injective_of_surjective (gradedRingHom 𝒜 I)
    (gradedRingHom_surjective 𝒜 I)
  exact congr_arg (fun r ↦ r.asHomogeneousIdeal.toIdeal) hpq

theorem projectiveSpectrum_comap_isClosedMap :
    letI := gradedRing 𝒜 I hI
    IsClosedMap (ProjectiveSpectrum.comap (gradedRingHom 𝒜 I)
      (quotient_irrelevant_le_map 𝒜 I hI)) := by
  let _ := gradedRing 𝒜 I hI
  intro Z hZ
  obtain ⟨s, rfl⟩ :=
    (ProjectiveSpectrum.isClosed_iff_zeroLocus (gradedComponent 𝒜 I) Z).mp hZ
  rw [image_projectiveSpectrum_comap_zeroLocus 𝒜 I hI]
  exact ProjectiveSpectrum.isClosed_zeroLocus 𝒜 _

theorem projectiveSpectrum_comap_isClosedEmbedding :
    letI := gradedRing 𝒜 I hI
    Topology.IsClosedEmbedding (ProjectiveSpectrum.comap (gradedRingHom 𝒜 I)
      (quotient_irrelevant_le_map 𝒜 I hI)) := by
  let _ := gradedRing 𝒜 I hI
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (ProjectiveSpectrum.comap (gradedRingHom 𝒜 I)
      (quotient_irrelevant_le_map 𝒜 I hI)).continuous
    (projectiveSpectrum_comap_injective 𝒜 I hI)
    (projectiveSpectrum_comap_isClosedMap 𝒜 I hI)

theorem projectiveLocalizationMap_surjective :
    letI := gradedRing 𝒜 I hI
    ∀ (p : ProjectiveSpectrum (gradedComponent 𝒜 I)),
      Function.Surjective
        (HomogeneousLocalization.localRingHom (gradedRingHom 𝒜 I)
          (p.asHomogeneousIdeal.toIdeal.comap (gradedRingHom 𝒜 I))
          p.asHomogeneousIdeal.toIdeal rfl) := by
  let _ := gradedRing 𝒜 I hI
  intro p z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rcases c.num.2 with ⟨a, ha, hnum⟩
  rcases c.den.2 with ⟨b, hb, hden⟩
  let c' : HomogeneousLocalization.NumDenSameDeg 𝒜
      (p.asHomogeneousIdeal.toIdeal.comap (gradedRingHom 𝒜 I)).primeCompl :=
    { deg := c.deg
      num := ⟨a, ha⟩
      den := ⟨b, hb⟩
      den_mem := by
        change b ∉ p.asHomogeneousIdeal.toIdeal.comap (gradedRingHom 𝒜 I)
        intro hbmem
        change Ideal.Quotient.mk I b ∈ p.asHomogeneousIdeal.toIdeal at hbmem
        exact c.den_mem (hden ▸ hbmem) }
  refine ⟨HomogeneousLocalization.mk c', ?_⟩
  rw [HomogeneousLocalization.localRingHom]
  erw [HomogeneousLocalization.map_mk]
  congr 1
  exact HomogeneousLocalization.NumDenSameDeg.ext _ rfl hnum hden

end ProjectiveSpectrum

section Proj

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (I : Ideal A) (hI : I.IsHomogeneous 𝒜)

/-- The morphism from the Proj of a homogeneous quotient to the original Proj. -/
@[expose] noncomputable def projMap :
    letI := gradedRing 𝒜 I hI
    AlgebraicGeometry.Proj (gradedComponent 𝒜 I) ⟶ AlgebraicGeometry.Proj 𝒜 := by
  letI := gradedRing 𝒜 I hI
  exact AlgebraicGeometry.Proj.map (gradedRingHom 𝒜 I)
    (quotient_irrelevant_le_map 𝒜 I hI)

/-- The morphism from the Proj of a homogeneous quotient is a closed immersion. -/
instance projMap_isClosedImmersion :
    letI := gradedRing 𝒜 I hI
    AlgebraicGeometry.IsClosedImmersion (projMap 𝒜 I hI) := by
  let _ := gradedRing 𝒜 I hI
  refine
    { isClosedEmbedding := projectiveSpectrum_comap_isClosedEmbedding 𝒜 I hI
      stalkMap_surjective := ?_ }
  intro p
  let p' : ProjectiveSpectrum (gradedComponent 𝒜 I) := p
  let _ : p'.asHomogeneousIdeal.toIdeal.IsPrime := p'.isPrime
  have hleft : Function.Surjective
      (AlgebraicGeometry.Proj.stalkIso 𝒜
        (ProjectiveSpectrum.comap (gradedRingHom 𝒜 I)
          (quotient_irrelevant_le_map 𝒜 I hI) p')).hom :=
    (ConcreteCategory.bijective_of_isIso _).2
  have hlocal := projectiveLocalizationMap_surjective 𝒜 I hI p'
  have hright : Function.Surjective
      (AlgebraicGeometry.Proj.stalkIso (gradedComponent 𝒜 I) p').inv :=
    (ConcreteCategory.bijective_of_isIso _).2
  have hsurj := hright.comp (hlocal.comp hleft)
  change Function.Surjective
    ((AlgebraicGeometry.Proj.stalkIso 𝒜
        (ProjectiveSpectrum.comap (gradedRingHom 𝒜 I)
          (quotient_irrelevant_le_map 𝒜 I hI) p')).hom ≫
      CommRingCat.ofHom
        (HomogeneousLocalization.localRingHom (gradedRingHom 𝒜 I)
          (ProjectiveSpectrum.comap (gradedRingHom 𝒜 I)
            (quotient_irrelevant_le_map 𝒜 I hI) p').asHomogeneousIdeal.toIdeal
          p'.asHomogeneousIdeal.toIdeal rfl) ≫
      (AlgebraicGeometry.Proj.stalkIso (gradedComponent 𝒜 I) p').inv) at hsurj
  rw [AlgebraicGeometry.Proj.localRingHom_comp_stalkIso] at hsurj
  exact hsurj

end Proj

end Ideal.Quotient
