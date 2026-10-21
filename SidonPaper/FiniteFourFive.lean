module

public import SidonPaper.FiniteDefinitions

@[expose] public section

namespace SidonPaper.Certificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- All 1001 four-element subsets satisfy the local difference condition. -/
 theorem base_fourFive_by_count : FourFiveByCount base := by
  have h : ((base.powersetCard 4).filter
      (fun B => 5 ≤ (positiveDifferences B).card)).card =
      (base.powersetCard 4).card := by decide +kernel
  exact Finset.card_filter_eq_iff.mp h

#check base_fourFive_by_count


#print axioms base_fourFive_by_count
end SidonPaper.Certificate
