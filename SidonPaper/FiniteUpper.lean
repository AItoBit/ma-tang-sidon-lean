module

public import SidonPaper.FiniteDefinitions

@[expose] public section

namespace SidonPaper.Certificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- An explicit finite list of twelve arithmetic progressions in the base set.
Only the fact that each listed triple is an AP is needed for the upper bound;
we do not claim here that this is a complete list.
-/
def HasListedAP (S : Finset ℤ) : Prop :=
  (0 ∈ S ∧ 136 ∈ S ∧ 272 ∈ S) ∨
  (0 ∈ S ∧ 200 ∈ S ∧ 400 ∈ S) ∨
  (0 ∈ S ∧ 298 ∈ S ∧ 596 ∈ S) ∨
  (0 ∈ S ∧ 528 ∈ S ∧ 1056 ∈ S) ∨
  (136 ∈ S ∧ 596 ∈ S ∧ 1056 ∈ S) ∨
  (200 ∈ S ∧ 243 ∈ S ∧ 286 ∈ S) ∨
  (200 ∈ S ∧ 249 ∈ S ∧ 298 ∈ S) ∨
  (243 ∈ S ∧ 246 ∈ S ∧ 249 ∈ S) ∨
  (246 ∈ S ∧ 272 ∈ S ∧ 298 ∈ S) ∨
  (246 ∈ S ∧ 323 ∈ S ∧ 400 ∈ S) ∨
  (249 ∈ S ∧ 286 ∈ S ∧ 323 ∈ S) ∨
  (272 ∈ S ∧ 400 ∈ S ∧ 528 ∈ S)

instance (S : Finset ℤ) : Decidable (HasListedAP S) := by
  unfold HasListedAP
  infer_instance

 theorem progression_not_sidon {S : Finset ℤ} {a b c : ℤ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a < b) (hbc : b < c) (heq : a + c = b + b) :
    ¬ SidonByPairs S := by
  intro h
  have hab' := (h a ha c hc b hb b hb (le_of_lt (lt_trans hab hbc)) le_rfl heq).1
  exact (ne_of_lt hab) hab'

 theorem hasListedAP_not_sidon {S : Finset ℤ} (h : HasListedAP S) :
    ¬ SidonByPairs S := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)
  · exact progression_not_sidon h.1 h.2.1 h.2.2 (by decide) (by decide) (by decide)

/-- Every nine-point subset contains at least one explicitly certified AP. -/
 theorem base_nine_hasListedAP :
    ∀ S ∈ base.powersetCard 9, HasListedAP S := by
  have h : ((base.powersetCard 9).filter HasListedAP).card =
      (base.powersetCard 9).card := by decide +kernel
  exact Finset.card_filter_eq_iff.mp h

/-- None of the 2002 nine-element subsets has injective unordered-pair sums.
Together with hereditariness of the Sidon property this excludes all sizes > 8.
-/
 theorem base_no_sidon_nine :
    ∀ S ∈ base.powersetCard 9, ¬ SidonByCount S := by
  intro S hS hSidon
  exact hasListedAP_not_sidon (base_nine_hasListedAP S hS)
    ((sidonByCount_iff S).mp hSidon)

/-- Integer form of the upper-bound assertion in Lemma 5.1. -/
 theorem base_sidon_card_le_eight {S : Finset ℤ} (hS : S ⊆ base)
    (hSidon : SidonByCount S) : S.card ≤ 8 := by
  by_contra hnot
  have h9 : 9 ≤ S.card := by omega
  obtain ⟨T, hTS, hcard⟩ := Finset.exists_subset_card_eq h9
  exact base_no_sidon_nine T
    (Finset.mem_powersetCard.mpr ⟨hTS.trans hS, hcard⟩)
    (sidonByCount_mono hTS hSidon)


#print axioms base_sidon_card_le_eight
end SidonPaper.Certificate
