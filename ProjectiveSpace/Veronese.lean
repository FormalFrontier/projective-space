/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GradedRings.Veronese
public import ProjectiveSpace.DegreeScaledMapPoint
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

@[expose] public section

/-!
# Proj of a positive Veronese ring

The maps of affine projective charts are the existing degree-multiplying maps
on homogeneous localizations, specialized to the selected-component inclusion.
The corresponding target-local equivalences give an isomorphism of whole schemes.
Original development: hive-request-e97f548d3626371a173eb011840a7070b24d81bb / 0e231558-4793-4185-8f55-2bad40d363bd.
Destination transfer: hive-request-be35b665bf79040df05d4a877584eddbda7cd6f6 / 936b1c06-477c-4e0b-bd11-71b190d392d5.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Proj.Veronese

open CategoryTheory GradedRing.Veronese HomogeneousLocalization

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The old degree of a form of new degree `j` is `n*j`. -/
theorem inclusion_degree (n : ℕ) (j : ℕ) (a : VeroneseRing 𝒮 n)
    (ha : a ∈ component 𝒮 n j) : inclusion 𝒮 n a ∈ 𝒮 (n * j) :=
  inclusion_mem 𝒮 ha

/-- The chart homomorphism inherited from the degree-scaled inclusion. -/
def chartHom (n : ℕ) (f : VeroneseRing 𝒮 n) :
    Away (component 𝒮 n) f →+* Away 𝒮 (inclusion 𝒮 n f) :=
  Away.mapDegreeMul (component 𝒮 n) 𝒮 (inclusion 𝒮 n) n
    (inclusion_degree 𝒮 n) f

/-- No cancellation by `f` is needed: injectivity descends from the inclusion
through ordinary localization, including zero-divisor and nilpotent charts. -/
theorem chartHom_injective (n : ℕ) (hn : 0 < n) (f : VeroneseRing 𝒮 n) :
    Function.Injective (chartHom 𝒮 n f) := by
  have hloc : Function.Injective
      (IsLocalization.Away.map (Localization.Away f)
        (Localization.Away (inclusion 𝒮 n f)) (inclusion 𝒮 n) f) :=
    (IsLocalization.Away.map_injective_iff
      (Localization.Away (inclusion 𝒮 n f)) (inclusion 𝒮 n) f).2 (by
      intro a ha
      refine ⟨0, ?_⟩
      simpa only [pow_zero, one_mul] using
        inclusion_injective 𝒮 n hn (ha.trans (map_zero (inclusion 𝒮 n)).symm))
  intro x y hxy
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  apply hloc
  have hv := congrArg HomogeneousLocalization.val hxy
  simp only [chartHom, Away.mapDegreeMul, HomogeneousLocalization.val_mapDegreeMul] at hv
  exact hv

/-- Every numerator of old degree `k*(n*j)` lies in new degree `k*j`. -/
theorem chartHom_surjective (n j : ℕ) (f : VeroneseRing 𝒮 n)
    (hf : f ∈ component 𝒮 n j) :
    Function.Surjective (chartHom 𝒮 n f) := by
  intro z
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒮 (inclusion_degree 𝒮 n j f hf) z
  have ha' : a ∈ 𝒮 (n * (k • j)) := by
    simpa only [nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using ha
  obtain ⟨b, hb, hab⟩ := exists_component 𝒮 n (k • j) ⟨a, ha'⟩
  refine ⟨Away.mk (component 𝒮 n) hf k b hb, ?_⟩
  rw [chartHom, Away.mapDegreeMul_mk]
  apply HomogeneousLocalization.val_injective (Submonoid.powers (inclusion 𝒮 n f))
  simp only [Away.val_mk]
  congr 1

/-- The nilpotent-safe canonical equivalence between the corresponding affine charts. -/
def chartEquiv (n : ℕ) (hn : 0 < n) (j : ℕ) (f : VeroneseRing 𝒮 n)
    (hf : f ∈ component 𝒮 n j) :
    Away (component 𝒮 n) f ≃+* Away 𝒮 (inclusion 𝒮 n f) :=
  RingEquiv.ofBijective (chartHom 𝒮 n f)
    ⟨chartHom_injective 𝒮 n hn f, chartHom_surjective 𝒮 n j f hf⟩

/-- Chart maps commute with the ordinary restriction to a product chart. -/
theorem chartHom_awayMap (n : ℕ) {j : ℕ} (f g : VeroneseRing 𝒮 n)
    (hg : g ∈ component 𝒮 n j) :
    (chartHom 𝒮 n (f * g)).comp
      (awayMap (component 𝒮 n) hg (show f * g = f * g by rfl)) =
    (awayMap 𝒮 (inclusion_degree 𝒮 n j g hg) (by simp)).comp
      (chartHom 𝒮 n f) :=
  Away.mapDegreeMul_awayMap (component 𝒮 n) 𝒮
    (inclusion 𝒮 n) n (inclusion_degree 𝒮 n) f g hg

/-- The same overlap restriction square for the affine chart equivalences. -/
theorem chartEquiv_awayMap (n : ℕ) (hn : 0 < n) {j k : ℕ}
    (f g : VeroneseRing 𝒮 n)
    (hf : f ∈ component 𝒮 n k) (hg : g ∈ component 𝒮 n j) :
    (chartEquiv 𝒮 n hn (k + j) (f * g)
      (SetLike.GradedMul.mul_mem hf hg)).toRingHom.comp
        (awayMap (component 𝒮 n) hg (show f * g = f * g by rfl)) =
    (awayMap 𝒮 (inclusion_degree 𝒮 n j g hg) (by simp)).comp
      (chartEquiv 𝒮 n hn k f hf).toRingHom := by
  exact chartHom_awayMap 𝒮 n f g hg

/-- Powers of old positive forms ensure the degree-scaled domain is all of Proj. -/
theorem domain_eq_top (n : ℕ) (_hn : 0 < n) :
    degreeScaledDomain (component 𝒮 n) 𝒮 (inclusion 𝒮 n) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  have hs : ∃ (i : ℕ) (s : S), 0 < i ∧ s ∈ 𝒮 i ∧ s ∉ x.asHomogeneousIdeal := by
    by_contra h
    apply x.not_irrelevant_le
    apply (HomogeneousIdeal.irrelevant_le (𝒜 := 𝒮)).mpr
    intro i hi s hsi
    by_contra hnot
    exact h ⟨i, s, hi, hsi, hnot⟩
  obtain ⟨i, s, hi, hsi, hsnot⟩ := hs
  have hpow : s ^ n ∈ 𝒮 (n * i) := by
    simpa [nsmul_eq_mul, mul_comm i n] using SetLike.pow_mem_graded n hsi
  let b : VeroneseRing 𝒮 n :=
    DirectSum.of (fun k : ℕ => 𝒮 (n * k)) i ⟨s ^ n, hpow⟩
  have hb : b ∈ component 𝒮 n i :=
    (mem_component_iff 𝒮 n i b).mpr ⟨⟨s ^ n, hpow⟩, rfl⟩
  rw [degreeScaledDomain]
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨⟨⟨i, hi⟩, ⟨b, hb⟩⟩, ?_⟩
  change inclusion 𝒮 n b ∉ x.asHomogeneousIdeal
  rw [show inclusion 𝒮 n b = s ^ n from inclusion_of 𝒮 n i ⟨s ^ n, hpow⟩]
  exact fun h => hsnot (x.isPrime.mem_of_pow_mem n h)

/-- The canonical identification of the domain open with the whole source scheme. -/
def domainIso (n : ℕ) (hn : 0 < n) :
    (degreeScaledDomain (component 𝒮 n) 𝒮 (inclusion 𝒮 n)).toScheme ≅ Proj 𝒮 :=
  (Proj 𝒮).isoOfEq (domain_eq_top 𝒮 n hn) ≪≫ (Proj 𝒮).topIso

/-- The canonical whole-space morphism has the published degree-scaled map as its
forward arrow, rather than a reconstructed point map. -/
def forward (n : ℕ) (hn : 0 < n) : Proj 𝒮 ⟶ Proj (component 𝒮 n) :=
  (domainIso 𝒮 n hn).inv ≫
    degreeScaledMap (component 𝒮 n) 𝒮 (inclusion 𝒮 n) n hn (inclusion_degree 𝒮 n)

theorem domainIso_hom (n : ℕ) (hn : 0 < n) :
    (domainIso 𝒮 n hn).hom =
      (degreeScaledDomain (component 𝒮 n) 𝒮 (inclusion 𝒮 n)).ι := by
  change ((Proj 𝒮).isoOfEq (domain_eq_top 𝒮 n hn)).hom ≫
    ((⊤ : (Proj 𝒮).Opens).ι) = _
  exact Scheme.isoOfEq_hom_ι (Proj 𝒮) (domain_eq_top 𝒮 n hn)

theorem domainIso_inv_ι (n : ℕ) (hn : 0 < n) :
    (domainIso 𝒮 n hn).inv ≫
      (degreeScaledDomain (component 𝒮 n) 𝒮 (inclusion 𝒮 n)).ι = 𝟙 (Proj 𝒮) := by
  rw [← domainIso_hom 𝒮 n hn, Iso.inv_hom_id]

/-- The whole map contracts ordinary homogeneous prime ideals for every ring element,
including inhomogeneous elements and elements of degree zero. -/
theorem forward_pointIdeal (n : ℕ) (hn : 0 < n) (p : Proj 𝒮) :
    ((forward 𝒮 n hn) p).asHomogeneousIdeal.toIdeal =
      Ideal.comap (inclusion 𝒮 n) (p.asHomogeneousIdeal.toIdeal) := by
  have h := degreeScaledMap_pointIdeal (component 𝒮 n) 𝒮
    (inclusion 𝒮 n) n hn (inclusion_degree 𝒮 n) ((domainIso 𝒮 n hn).inv p)
  have hp : (degreeScaledDomain (component 𝒮 n) 𝒮 (inclusion 𝒮 n)).ι
      ((domainIso 𝒮 n hn).inv p) = p := by
    have hcomp := congrArg (fun (g : Proj 𝒮 ⟶ Proj 𝒮) => g p)
      (domainIso_inv_ι 𝒮 n hn)
    exact hcomp
  rw [hp] at h
  exact h

theorem forward_mem_pointIdeal (n : ℕ) (hn : 0 < n) (p : Proj 𝒮)
    (a : VeroneseRing 𝒮 n) :
    a ∈ ((forward 𝒮 n hn) p).asHomogeneousIdeal.toIdeal ↔
      inclusion 𝒮 n a ∈ p.asHomogeneousIdeal.toIdeal := by
  rw [forward_pointIdeal]
  rfl

/-- Inverse images of positive distinguished opens under the whole map. -/
theorem forward_preimage_basicOpen (n : ℕ) (hn : 0 < n) (j : ℕ)
    (hj : 0 < j) (f : VeroneseRing 𝒮 n) (hf : f ∈ component 𝒮 n j) :
    forward 𝒮 n hn ⁻¹ᵁ basicOpen (component 𝒮 n) f =
      basicOpen 𝒮 (inclusion 𝒮 n f) := by
  rw [forward, Scheme.Hom.comp_preimage]
  rw [degreeScaledMap_preimage_basicOpen (component 𝒮 n) 𝒮
    (inclusion 𝒮 n) n hn (inclusion_degree 𝒮 n) f hf hj]
  rw [← Scheme.Hom.comp_preimage, domainIso_inv_ι]
  rfl

/-- The map on degree-zero coefficient rings is the canonical degree-zero equivalence. -/
theorem degreeZeroRingHom_eq (n : ℕ) (hn : 0 < n) :
    degreeZeroRingHom (component 𝒮 n) 𝒮 (inclusion 𝒮 n) n
        (inclusion_degree 𝒮 n) = (zeroRingEquiv 𝒮 n hn).toRingHom := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  rfl

/-- The whole-arrow coefficient triangle, with no auxiliary base-ring hypothesis. -/
theorem forward_toSpecZero (n : ℕ) (hn : 0 < n) :
    forward 𝒮 n hn ≫ toSpecZero (component 𝒮 n) =
      toSpecZero 𝒮 ≫
        Spec.map (CommRingCat.ofHom (zeroRingEquiv 𝒮 n hn).toRingHom) := by
  calc
    _ = (domainIso 𝒮 n hn).inv ≫
        (degreeScaledMap (component 𝒮 n) 𝒮 (inclusion 𝒮 n) n hn
          (inclusion_degree 𝒮 n) ≫ toSpecZero (component 𝒮 n)) := by
            simp only [forward, Category.assoc]
    _ = (domainIso 𝒮 n hn).inv ≫
        (degreeScaledDomain (component 𝒮 n) 𝒮 (inclusion 𝒮 n)).ι ≫
          toSpecZero 𝒮 ≫ Spec.map
            (CommRingCat.ofHom (degreeZeroRingHom (component 𝒮 n) 𝒮
              (inclusion 𝒮 n) n (inclusion_degree 𝒮 n))) := by
                rw [degreeScaledMap_toSpecZero]
    _ = _ := by
      rw [degreeZeroRingHom_eq 𝒮 n hn]
      simp only [← Category.assoc, domainIso_inv_ι, Category.id_comp]

theorem chartCover_comp_domainIso (n : ℕ) (hn : 0 < n)
    (i : Σ j : PNat, component 𝒮 n j) :
    (basicOpen 𝒮 (inclusion 𝒮 n (i.2 : VeroneseRing 𝒮 n))).ι ≫
      (domainIso 𝒮 n hn).inv =
        (chartCover (component 𝒮 n) 𝒮 (inclusion 𝒮 n)).f i := by
  change (basicOpen 𝒮 (inclusion 𝒮 n (i.2 : VeroneseRing 𝒮 n))).ι ≫
      (domainIso 𝒮 n hn).inv =
        (Proj 𝒮).homOfLE (le_iSup
          (chartOpen (component 𝒮 n) 𝒮 (inclusion 𝒮 n)) i)
  rw [← cancel_mono (domainIso 𝒮 n hn).hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, domainIso_hom]
  exact (Scheme.homOfLE_ι (Proj 𝒮)
    (le_iSup (chartOpen (component 𝒮 n) 𝒮 (inclusion 𝒮 n)) i)).symm

theorem iSup_basicOpen_eq_top (n : ℕ) :
    ⨆ i : Σ j : PNat, component 𝒮 n j,
      basicOpen (component 𝒮 n) (i.2 : VeroneseRing 𝒮 n) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (𝒜 := component 𝒮 n)).mpr
  intro j hj x hx
  exact Ideal.subset_span ⟨⟨⟨j, hj⟩, ⟨x, hx⟩⟩, rfl⟩

theorem forward_restrict_chart (n : ℕ) (hn : 0 < n) (j : ℕ) (hj : 0 < j)
    (f : VeroneseRing 𝒮 n) (hf : f ∈ component 𝒮 n j) :
    ((Proj 𝒮).isoOfEq (forward_preimage_basicOpen 𝒮 n hn j hj f hf)).inv ≫
      (forward 𝒮 n hn ∣_ basicOpen (component 𝒮 n) f) =
        (basicOpenIsoSpec 𝒮 (inclusion 𝒮 n f) (inclusion_degree 𝒮 n j f hf)
          (Nat.mul_pos hn hj)).hom ≫
          Spec.map (CommRingCat.ofHom (chartHom 𝒮 n f)) ≫
            (basicOpenIsoSpec (component 𝒮 n) f hf hj).inv := by
  apply (cancel_mono (basicOpen (component 𝒮 n) f).ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    Scheme.isoOfEq_inv_ι]
  simp only [Category.assoc, basicOpenIsoSpec_inv_ι]
  let idx : Σ degree : PNat, component 𝒮 n degree := ⟨⟨j, hj⟩, ⟨f, hf⟩⟩
  have hchart := degreeScaledMap_chartSpec (component 𝒮 n) 𝒮
    (inclusion 𝒮 n) n hn (inclusion_degree 𝒮 n) idx
  rw [← chartCover_comp_domainIso 𝒮 n hn idx] at hchart
  dsimp only [idx] at hchart
  simp only [Category.assoc] at hchart
  have h := (Iso.inv_comp_eq _).mp hchart
  convert h using 1
  · simp only [forward]
  · simp only [chartHom]
    congr 1

/-- The canonical degree-scaled arrow is a scheme isomorphism: its restrictions
to the target's distinguished affine cover are maps of spectra of ring equivalences. -/
theorem isIso_forward (n : ℕ) (hn : 0 < n) : IsIso (forward 𝒮 n hn) := by
  let U : (Σ j : PNat, component 𝒮 n j) → (Proj (component 𝒮 n)).Opens :=
    fun i => basicOpen (component 𝒮 n) (i.2 : VeroneseRing 𝒮 n)
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := .isomorphisms _) U
    (iSup_basicOpen_eq_top 𝒮 n)
  rintro ⟨⟨j, hj⟩, ⟨f, hf⟩⟩
  change f ∈ component 𝒮 n j at hf
  have hmap : IsIso (Spec.map (CommRingCat.ofHom (chartHom 𝒮 n f))) := by
    have hr : (chartEquiv 𝒮 n hn j f hf).toRingHom = chartHom 𝒮 n f := by
      apply RingHom.ext
      intro x
      rfl
    rw [← hr]
    change IsIso (Spec.map (chartEquiv 𝒮 n hn j f hf).toCommRingCatIso.hom)
    infer_instance
  let e := (Proj 𝒮).isoOfEq (forward_preimage_basicOpen 𝒮 n hn j hj f hf)
  apply (isIso_comp_left_iff e.inv _).mp
  rw [forward_restrict_chart 𝒮 n hn j hj f hf]
  infer_instance

/-- The canonical whole-scheme Veronese isomorphism. -/
def schemeIso (n : ℕ) (hn : 0 < n) : Proj 𝒮 ≅ Proj (component 𝒮 n) :=
  @asIso _ _ _ _ (forward 𝒮 n hn) (isIso_forward 𝒮 n hn)

@[simp] theorem schemeIso_hom (n : ℕ) (hn : 0 < n) :
    (schemeIso 𝒮 n hn).hom = forward 𝒮 n hn := rfl

/-- Fractions are mapped by the published degree-scaled localization morphism. -/
theorem chartEquiv_mk (n : ℕ) (hn : 0 < n) (j : ℕ) (f : VeroneseRing 𝒮 n)
    (hf : f ∈ component 𝒮 n j) (k : ℕ) (a : VeroneseRing 𝒮 n)
    (ha : a ∈ component 𝒮 n (k • j)) :
    chartEquiv 𝒮 n hn j f hf (Away.mk (component 𝒮 n) hf k a ha) =
      Away.mk 𝒮 (inclusion_degree 𝒮 n j f hf) k (inclusion 𝒮 n a)
        (by simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          inclusion_degree 𝒮 n (k • j) a ha) :=
  Away.mapDegreeMul_mk (component 𝒮 n) 𝒮 (inclusion 𝒮 n) n
    (inclusion_degree 𝒮 n) f hf k a ha

end AlgebraicGeometry.Proj.Veronese
