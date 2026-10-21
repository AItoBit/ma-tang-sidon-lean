module

public import SidonPaper.ConstructionIndependence
public import SidonPaper.Attainment

@[expose] public section


/-! The complete upper-bound chain in Theorem 1.3. -/
namespace SidonPaper

/-- The upper bound in Theorem 1.3, with the source's ceiling encoded by
natural division `(n+2)/2`. This also holds at the harmless index zero. -/
theorem g_upper (n : ℕ) : g n ≤ (n+2)/2 := by
  classical
  let A := natRealImage (construction (n/2))
  have hcardA : A.card = 2*(n/2)+1 := by
    rw [natRealImage_card, construction_card]
  have hle : n ≤ A.card := by rw [hcardA]; omega
  obtain ⟨B, hBA, hBn⟩ := Finset.exists_subset_card_eq hle
  have hweakA : IsWeakSidon (A : Set ℝ) := by
    rw [natRealImage_coe]
    exact construction_weakSidon_real (n/2)
  have hweakB : IsWeakSidon (B : Set ℝ) := by
    apply hweakA.mono
    intro x hx
    exact hBA hx
  calc
    g n = g B.card := by rw [hBn]
    _ ≤ h B := g_le_h hweakB
    _ ≤ h A := h_mono hBA
    _ = n/2+1 := construction_h (n/2)
    _ = (n+2)/2 := by omega

end SidonPaper
