module

public import SidonPaper.FiniteWitness
public import SidonPaper.FiniteFourFive
public import SidonPaper.FiniteUpper

@[expose] public section

namespace SidonPaper.Certificate
/-- Exact integer certificate for the local condition and maximum Sidon size. -/
 theorem lemma_5_1_integer_certificate :
    base.card = 14 ∧ FourFiveByCount base ∧
    (∃ S : Finset ℤ, S ⊆ base ∧ S.card = 8 ∧ SidonByPairs S) ∧
    (∀ S : Finset ℤ, S ⊆ base → SidonByPairs S → S.card ≤ 8) := by
  refine ⟨base_card, base_fourFive_by_count, ?_, ?_⟩
  · exact ⟨witness, witness_subset, witness_card,
      (sidonByCount_iff witness).mp witness_sidon_by_count⟩
  · intro S hS hSidon
    exact base_sidon_card_le_eight hS ((sidonByCount_iff S).mpr hSidon)

#print axioms lemma_5_1_integer_certificate

end SidonPaper.Certificate
