module

public import SidonPaper.Targets
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

@[expose] public section


namespace SidonPaper

/-- Unordered-pair form of the Sidon property. -/
theorem IsSidon.eq_or_swap {A : Set ℝ} (h : IsSidon A)
    {a b c d : ℝ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hs : a + b = c + d) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases le_total a b with hab | hba
  · rcases le_total c d with hcd | hdc
    · exact Or.inl (h ha hb hc hd hab hcd hs)
    · have he := h ha hb hd hc hab hdc (by linarith)
      exact Or.inr he
  · rcases le_total c d with hcd | hdc
    · have he := h hb ha hc hd hba hcd (by linarith)
      exact Or.inr ⟨he.2, he.1⟩
    · have he := h hb ha hd hc hba hdc (by linarith)
      exact Or.inl ⟨he.2, he.1⟩

/-- Every positive difference of a Sidon set comes from a unique ordered pair. -/
theorem IsSidon.difference_injective {A : Finset ℝ} (h : IsSidon (A : Set ℝ)) :
    Set.InjOn (fun p : ℝ × ℝ => p.2 - p.1)
      ((A.product A).filter (fun p => p.1 < p.2)) := by
  intro p hp q hq heq
  obtain ⟨hpA,hpLt⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqA,hqLt⟩ := Finset.mem_filter.mp hq
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hpA
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hqA
  rcases h.eq_or_swap ha hd hc hb (by linarith) with he | he
  · exact Prod.ext he.1 he.2.symm
  · linarith [he.1]

/-- Strengthening of Proposition 2.1: all unordered positive differences are distinct. -/
theorem IsSidon.differences_card {A : Finset ℝ} (h : IsSidon (A : Set ℝ)) :
    (differences A).card = A.card.choose 2 := by
  classical
  unfold differences
  rw [Finset.card_image_iff.mpr h.difference_injective]
  exact Finset.card_product_filter_lt

/-- Proposition 2.1. -/
theorem IsSidon.fourFive {A : Finset ℝ} (h : IsSidon (A : Set ℝ)) : IsFourFive A := by
  intro B hBA hBcard
  have hBS : IsSidon (B : Set ℝ) := h.mono (by exact hBA)
  rw [hBS.differences_card, hBcard]
  decide

private theorem card_four_le (a b c d : ℝ) : ({a,b,c,d} : Finset ℝ).card ≤ 4 := by
  classical
  simp only [Finset.card_insert_eq_ite, Finset.card_singleton]
  split_ifs <;> omega

/-- A four-point equal-sum configuration has at most four positive differences. -/
theorem equal_sum_differences_le {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hs : a + d = b + c) :
    (differences {a,b,c,d}).card ≤ 4 := by
  classical
  have hsub : differences {a,b,c,d} ⊆ {b-a,c-a,d-a,c-b} := by
    intro z hz
    obtain ⟨⟨x,y⟩, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
    have he1 : d - b = c - a := by linarith
    have he2 : d - c = b - a := by linarith
    rcases hx with hx | hx | hx | hx <;>
      rcases hy with hy | hy | hy | hy <;>
      subst x <;> subst y <;>
      simp_all [Prod.fst, Prod.snd]
    all_goals linarith
  exact (Finset.card_le_card hsub).trans (card_four_le _ _ _ _)

/-- Proposition 2.2. -/
theorem IsFourFive.weakSidon {A : Finset ℝ} (h : IsFourFive A) :
    IsWeakSidon (A : Set ℝ) := by
  classical
  intro a b c d ha hb hc hd hab hcd hs
  by_cases hac : a = c
  · exact ⟨hac, by linarith⟩
  have hbad (a b c d : ℝ) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
      (hab : a < b) (hcd : c < d) (hac : a < c) (hs : a+b=c+d) : False := by
    have hdb : d < b := by linarith
    have hsub : ({a,c,d,b} : Finset ℝ) ⊆ A := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hcard : ({a,c,d,b} : Finset ℝ).card = 4 := by
      simp [ne_of_lt hac, ne_of_lt hcd, ne_of_lt hdb, ne_of_lt (lt_trans hac hcd),
        ne_of_lt (lt_trans hac (lt_trans hcd hdb)), ne_of_lt (lt_trans hcd hdb),
        ne_of_gt hac, ne_of_gt hcd, ne_of_gt hdb,
        ne_of_gt (lt_trans hac hcd), ne_of_gt (lt_trans hac (lt_trans hcd hdb)),
        ne_of_gt (lt_trans hcd hdb)]
    have hlarge := h _ hsub hcard
    have hsmall := equal_sum_differences_le hac hcd hdb hs
    omega
  rcases lt_or_gt_of_ne hac with hac | hca
  · exact False.elim (hbad a b c d ha hb hc hd hab hcd hac hs)
  · exact False.elim (hbad c d a b hc hd ha hb hcd hab hca hs.symm)

end SidonPaper
