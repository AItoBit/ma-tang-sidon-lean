module

public import SidonPaper.ExtremalBasics

@[expose] public section


namespace SidonPaper

/-- The affine image used throughout Section 3. -/
noncomputable def affineImage (A : Finset ℝ) (q t : ℝ) : Finset ℝ := by
  classical
  exact A.image (fun x => q * x + t)

theorem affine_injective {q t : ℝ} (hq : 0 < q) :
    Function.Injective (fun x : ℝ => q * x + t) := by
  intro x y he
  nlinarith

theorem affineImage_coe (A : Finset ℝ) (q t : ℝ) :
    (affineImage A q t : Set ℝ) = (fun x => q * x + t) '' (A : Set ℝ) := by
  classical
  simp [affineImage]

theorem affineImage_card (A : Finset ℝ) {q t : ℝ} (hq : 0 < q) :
    (affineImage A q t).card = A.card := by
  classical
  exact Finset.card_image_of_injective A (affine_injective hq)

/-- The equality of maximum Sidon subset sizes in Lemmas 3.2 and 3.5. -/
theorem h_affineImage (A : Finset ℝ) {q t : ℝ} (hq : 0 < q) :
    h (affineImage A q t) = h A := by
  classical
  apply Nat.le_antisymm
  · unfold h
    apply Finset.sup_le_iff.mpr
    intro B hB
    obtain ⟨hBsub, hBsidon⟩ := Finset.mem_filter.mp hB
    obtain ⟨C, hCA, hCB⟩ := Finset.subset_image_iff.mp (Finset.mem_powerset.mp hBsub)
    have hBC : B = affineImage C q t := hCB.symm
    have hCsidon : IsSidon (C : Set ℝ) := by
      apply (sidon_affine_iff (C : Set ℝ) hq).mp
      rw [← affineImage_coe, ← hBC]
      exact hBsidon
    rw [hBC, affineImage_card C hq]
    apply Finset.le_sup
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hCA, hCsidon⟩
  · unfold h
    apply Finset.sup_le_iff.mpr
    intro B hB
    obtain ⟨hBsub, hBsidon⟩ := Finset.mem_filter.mp hB
    have hBA : B ⊆ A := Finset.mem_powerset.mp hBsub
    have hsub : affineImage B q t ⊆ affineImage A q t :=
      Finset.image_subset_image hBA
    have hsid : IsSidon (affineImage B q t : Set ℝ) := by
      rw [affineImage_coe]
      exact (sidon_affine_iff (B : Set ℝ) hq).mpr hBsidon
    have hh := card_le_h hsub hsid
    rw [affineImage_card B hq] at hh
    exact hh

/-- The predicate part of Lemma 3.2, in finite-set notation. -/
theorem weakSidon_affineImage_iff (A : Finset ℝ) {q t : ℝ} (hq : 0 < q) :
    IsWeakSidon (affineImage A q t : Set ℝ) ↔ IsWeakSidon (A : Set ℝ) := by
  rw [affineImage_coe]
  exact weakSidon_affine_iff _ hq

/-- Every positive difference is scaled by the same positive q. -/
theorem differences_affineImage (A : Finset ℝ) {q t : ℝ} (hq : 0 < q) :
    differences (affineImage A q t) = (differences A).image (fun x => q * x) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp ha
    obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp hb
    have hab : a < b := by nlinarith [hlt]
    apply Finset.mem_image.mpr
    refine ⟨b - a, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩, hab⟩, rfl⟩
    · nlinarith [hea, heb]
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    apply Finset.mem_image.mpr
    refine ⟨(q * p.1 + t, q * p.2 + t), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_image.mpr ⟨p.1, ha, rfl⟩
      · exact Finset.mem_image.mpr ⟨p.2, hb, rfl⟩
      · nlinarith
    · ring

/-- Difference-cardinality invariance underlying Lemma 3.5. -/
theorem differences_affineImage_card (A : Finset ℝ) {q t : ℝ} (hq : 0 < q) :
    (differences (affineImage A q t)).card = (differences A).card := by
  classical
  rw [differences_affineImage A hq]
  apply Finset.card_image_of_injective
  intro x y he
  nlinarith

/-- The (4,5) predicate is invariant under affine changes with positive slope. -/
theorem fourFive_affineImage_iff (A : Finset ℝ) {q t : ℝ} (hq : 0 < q) :
    IsFourFive (affineImage A q t) ↔ IsFourFive A := by
  classical
  constructor
  · intro h B hBA hBcard
    have hsub : affineImage B q t ⊆ affineImage A q t := Finset.image_subset_image hBA
    have hcard : (affineImage B q t).card = 4 := by rw [affineImage_card B hq, hBcard]
    have hb := h (affineImage B q t) hsub hcard
    rw [differences_affineImage_card B hq] at hb
    exact hb
  · intro h B hBA hBcard
    obtain ⟨C, hCA, hCB⟩ := Finset.subset_image_iff.mp hBA
    have hBC : B = affineImage C q t := hCB.symm
    have hCcard : C.card = 4 := by rw [← affineImage_card C hq, ← hBC, hBcard]
    rw [hBC, differences_affineImage_card C hq]
    exact h C hCA hCcard

#print axioms h_affineImage
#print axioms fourFive_affineImage_iff
end SidonPaper
