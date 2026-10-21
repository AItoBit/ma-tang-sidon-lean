module

public import SidonPaper.RealCertificate

@[expose] public section


namespace SidonPaper

/-- The upper bound in Theorem 1.6, obtained directly from the optimal universal
constant definition and the verified fourteen-point example. -/
theorem cStar_le_four_sevenths : cStar ≤ (4 / 7 : ℝ) := by
  unfold cStar
  apply csSup_le
  · refine ⟨0, ?_⟩
    intro A hpos hfour
    simp only [zero_mul]
    exact Nat.cast_nonneg _
  · intro c hc
    have hbound := hc (realImage Certificate.base)
      (by rw [lemma_5_1.1]; norm_num) lemma_5_1.2.1
    rw [lemma_5_1.1, lemma_5_1.2.2] at hbound
    norm_num at hbound ⊢
    linarith

end SidonPaper
