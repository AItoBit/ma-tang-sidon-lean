module

public import SidonPaper.Targets

@[expose] public section


namespace SidonPaper

/-- Every Sidon subset is bounded by the finite maximum defining h. -/
theorem card_le_h {A B : Finset ℝ} (hBA : B ⊆ A) (hB : IsSidon (B : Set ℝ)) :
    B.card ≤ h A := by
  classical
  unfold h
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBA, hB⟩)

/-- The largest Sidon subset has at most as many points as the original set. -/
theorem h_le_card (A : Finset ℝ) : h A ≤ A.card := by
  classical
  unfold h
  apply Finset.sup_le_iff.mpr
  intro B hB
  exact Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1)

/-- Monotonicity of the largest Sidon subset size. -/
theorem h_mono {A B : Finset ℝ} (hAB : A ⊆ B) : h A ≤ h B := by
  classical
  unfold h
  apply Finset.sup_le_iff.mpr
  intro S hS
  have hs := Finset.mem_filter.mp hS
  apply Finset.le_sup
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hs.1).trans hAB), hs.2⟩

end SidonPaper
