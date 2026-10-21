module

public import SidonPaper.Targets
public import Mathlib.Data.Finset.Max
public import Lean.Elab.Tactic.Omega

@[expose] public section


namespace SidonPaper

/-- Lemma 2.4: in a weak Sidon set every AP has a different midpoint,
and neither extreme point can be a midpoint. -/
theorem apEdges_card_le {A : Finset ℝ} (hw : IsWeakSidon (A : Set ℝ))
    (hcard : 2 ≤ A.card) : (apEdges A).card ≤ A.card - 2 := by
  classical
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  let lo := A.min' hne
  let hi := A.max' hne
  have hlo : lo ∈ A := A.min'_mem hne
  have hhi : hi ∈ A := A.max'_mem hne
  have hlohi : lo < hi := A.min'_lt_max'_of_card (by omega)
  have hinj : Set.InjOn (fun p : ℝ × ℝ × ℝ => p.2.1) (apEdges A) := by
    intro p hp q hq hm
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    have hpA := Finset.mem_product.mp hp'.1
    have hqA := Finset.mem_product.mp hq'.1
    have hpBC := Finset.mem_product.mp hpA.2
    have hqBC := Finset.mem_product.mp hqA.2
    have he := hw hpA.1 hpBC.2 hqA.1 hqBC.2
      (lt_trans hp'.2.1 hp'.2.2.1) (lt_trans hq'.2.1 hq'.2.2.1)
      (by linarith [hp'.2.2.2, hq'.2.2.2])
    exact Prod.ext he.1 (Prod.ext hm he.2)
  have hsub : (apEdges A).image (fun p => p.2.1) ⊆ (A.erase lo).erase hi := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have hp' := Finset.mem_filter.mp hp
    have hpA := Finset.mem_product.mp hp'.1
    have hpBC := Finset.mem_product.mp hpA.2
    have hlow : lo ≤ p.1 := A.min'_le _ hpA.1
    have hhigh : p.2.2 ≤ hi := A.le_max' _ hpBC.2
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hpBC.1⟩⟩ <;>
      linarith [hp'.2.1, hp'.2.2.1]
  have hic : hi ∈ A.erase lo := Finset.mem_erase.mpr ⟨ne_of_gt hlohi, hhi⟩
  calc
    (apEdges A).card = ((apEdges A).image (fun p => p.2.1)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((A.erase lo).erase hi).card := Finset.card_le_card hsub
    _ = A.card - 2 := by
      rw [Finset.card_erase_of_mem hic, Finset.card_erase_of_mem hlo]
      omega

end SidonPaper
