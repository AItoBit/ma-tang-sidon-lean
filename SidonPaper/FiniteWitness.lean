module

public import SidonPaper.FiniteDefinitions

@[expose] public section

namespace SidonPaper.Certificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
 theorem base_card : base.card = 14 := by decide +kernel
 theorem witness_card : witness.card = 8 := by decide +kernel
 theorem witness_subset : witness ⊆ base := by decide +kernel
 theorem witness_sidon_by_count : SidonByCount witness := by decide +kernel

#check witness_sidon_by_count


#print axioms witness_sidon_by_count
end SidonPaper.Certificate
