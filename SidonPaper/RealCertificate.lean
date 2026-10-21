module

public import SidonPaper.IntegerBridge
public import SidonPaper.FiniteCertificate
public import SidonPaper.ExtremalBasics

@[expose] public section


namespace SidonPaper

noncomputable def realImage (S : Finset ℤ) : Finset ℝ := by
  classical
  exact S.image (fun z : ℤ => (z : ℝ))

theorem realImage_card (S : Finset ℤ) : (realImage S).card = S.card := by
  classical
  exact Finset.card_image_of_injective S Int.cast_injective

theorem realImage_coe (S : Finset ℤ) :
    (realImage S : Set ℝ) = ((↑) : ℤ → ℝ) '' (S : Set ℤ) := by
  classical
  simp [realImage]

theorem differences_realImage (S : Finset ℤ) :
    differences (realImage S) = realImage (Certificate.positiveDifferences S) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp ha
    obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp hb
    have hcast : (a : ℝ) < (b : ℝ) := by rw [hea, heb]; exact hlt
    have hab : a < b := Int.cast_lt.mp hcast
    apply Finset.mem_image.mpr
    refine ⟨b - a, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩, hab⟩, rfl⟩
    · simp only [Int.cast_sub, hea, heb]
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    apply Finset.mem_image.mpr
    refine ⟨((p.1 : ℝ), (p.2 : ℝ)), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, Int.cast_lt.mpr hlt⟩
      · exact Finset.mem_image.mpr ⟨p.1, ha, rfl⟩
      · exact Finset.mem_image.mpr ⟨p.2, hb, rfl⟩
    · simp only [Int.cast_sub]

theorem fourFive_realImage {S : Finset ℤ} (hS : Certificate.FourFiveByCount S) :
    IsFourFive (realImage S) := by
  classical
  intro B hB hcard
  obtain ⟨C, hCS, hCB⟩ := Finset.subset_image_iff.mp hB
  have hC : C.card = 4 := by
    rw [← realImage_card C]
    change (C.image (fun z : ℤ => (z : ℝ))).card = 4
    rw [hCB, hcard]
  have hdiff := hS C (Finset.mem_powersetCard.mpr ⟨hCS, hC⟩)
  have hBC : B = realImage C := hCB.symm
  rw [hBC, differences_realImage, realImage_card]
  exact hdiff

/-- Full real-valued version of the finite example in Lemma 5.1. -/
theorem lemma_5_1 :
    (realImage Certificate.base).card = 14 ∧
    IsFourFive (realImage Certificate.base) ∧ h (realImage Certificate.base) = 8 := by
  classical
  refine ⟨?_, fourFive_realImage Certificate.base_fourFive_by_count, ?_⟩
  · rw [realImage_card, Certificate.base_card]
  · apply Nat.le_antisymm
    · unfold h
      apply Finset.sup_le_iff.mpr
      intro B hB
      obtain ⟨hBsub, hBSidon⟩ := Finset.mem_filter.mp hB
      obtain ⟨C, hCbase, hCB⟩ :=
        Finset.subset_image_iff.mp (Finset.mem_powerset.mp hBsub)
      have hBC : B = realImage C := hCB.symm
      have hCsidon : Certificate.SidonByPairs C := by
        apply (sidon_intCast_iff C).mp
        rw [← realImage_coe, ← hBC]
        exact hBSidon
      rw [hBC, realImage_card]
      exact Certificate.base_sidon_card_le_eight hCbase
        ((Certificate.sidonByCount_iff C).mpr hCsidon)
    · have hwsub : realImage Certificate.witness ⊆ realImage Certificate.base :=
        Finset.image_subset_image Certificate.witness_subset
      have hwsidon : IsSidon (realImage Certificate.witness : Set ℝ) := by
        rw [realImage_coe]
        exact witness_sidon_real
      have hb := card_le_h hwsub hwsidon
      simpa only [realImage_card, Certificate.witness_card] using hb

end SidonPaper
