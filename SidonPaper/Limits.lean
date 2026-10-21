module

public import Mathlib.Analysis.Subadditive

@[expose] public section


/-! The corrected real-valued form of Lemma 3.1, specialized to the
nonnegative sequences used in the paper. This does not establish that
`f` or `g` is subadditive. -/
namespace SidonPaper
open Filter Set

/-- Fekete's lemma for the nonnegative setting needed in this paper.
Unlike the printed unrestricted real-valued statement, this cannot diverge
to negative infinity. Subadditivity here includes index zero. -/
theorem fekete_nonnegative {u : ℕ → ℝ} (hs : Subadditive u)
    (hn : ∀ n, 0 ≤ u n) :
    Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop
      (nhds (sInf ((fun n : ℕ => u n / (n : ℝ)) '' Ici 1))) := by
  have hbdd : BddBelow (range (fun n : ℕ => u n / (n : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro r ⟨n, rfl⟩
    exact div_nonneg (hn n) (Nat.cast_nonneg n)
  simpa only [Subadditive.lim] using hs.tendsto_lim hbdd

end SidonPaper
