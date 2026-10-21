module

public import SidonPaper.ExtremalBasics
public import SidonPaper.Relations
public import SidonPaper.Gluing
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section


namespace SidonPaper

/-- A finite real Sidon set can always be extended by one point. -/
theorem exists_sidon_insert (A : Finset ℝ) (hA : IsSidon (A : Set ℝ)) :
    ∃ x : ℝ, x ∉ A ∧ IsSidon ((insert x A : Finset ℝ) : Set ℝ) := by
  classical
  let halves : Finset ℝ := (A.product A).image (fun p => (p.1 + p.2) / 2)
  let triples : Finset ℝ := (A.product (A.product A)).image
    (fun p => p.2.1 + p.2.2 - p.1)
  obtain ⟨x, hx⟩ := Finset.exists_notMem (A ∪ halves ∪ triples)
  have hxA : x ∉ A := by intro h; exact hx (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hxhalf {a b : ℝ} (ha : a ∈ A) (hb : b ∈ A) : x + x ≠ a + b := by
    intro he
    apply hx
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, by dsimp; linarith⟩
  have hxtriple {a b c : ℝ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
      x + a ≠ b + c := by
    intro he
    apply hx
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(a,b,c), Finset.mem_product.mpr ⟨ha, Finset.mem_product.mpr ⟨hb,hc⟩⟩,
      by dsimp; linarith⟩
  refine ⟨x, hxA, ?_⟩
  intro a b c d ha hb hc hd hab hcd hs
  simp only [Finset.mem_coe, Finset.mem_insert] at ha hb hc hd
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hc with hc | hc <;> rcases hd with hd | hd
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith
  · exact False.elim (hxhalf hc hd (by linarith))
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith
  · exact False.elim (hxtriple hb hc hd (by linarith))
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith
  · exact False.elim (hxtriple ha hc hd (by linarith))
  · exact False.elim (hxhalf ha hb (by linarith))
  · exact False.elim (hxtriple hd ha hb (by linarith))
  · exact False.elim (hxtriple hc ha hb (by linarith))
  · exact hA ha hb hc hd hab hcd hs

/-- Admissible Sidon sets exist at every finite cardinality. -/
theorem exists_sidon_card (n : ℕ) :
    ∃ A : Finset ℝ, A.card = n ∧ IsSidon (A : Set ℝ) := by
  classical
  induction n with
  | zero =>
      refine ⟨∅, rfl, ?_⟩
      intro a b c d ha
      simp at ha
  | succ n ih =>
      obtain ⟨A, hcard, hA⟩ := ih
      obtain ⟨x, hx, hnew⟩ := exists_sidon_insert A hA
      exact ⟨insert x A, by rw [Finset.card_insert_of_notMem hx, hcard], hnew⟩

/-- The family defining g(n) is nonempty, including n=0. -/
theorem g_admissible_nonempty (n : ℕ) :
    {k : ℕ | ∃ A : Finset ℝ, A.card = n ∧ IsWeakSidon (A : Set ℝ) ∧ h A = k}.Nonempty := by
  obtain ⟨A, hcard, hA⟩ := exists_sidon_card n
  exact ⟨h A, A, hcard, hA.weak, rfl⟩

/-- The natural infimum defining g is attained by an admissible weak Sidon set. -/
theorem g_attained (n : ℕ) :
    ∃ A : Finset ℝ, A.card = n ∧ IsWeakSidon (A : Set ℝ) ∧ h A = g n := by
  exact Nat.sInf_mem (g_admissible_nonempty n)

/-- The family defining f(n) is nonempty, including n=0. -/
theorem f_admissible_nonempty (n : ℕ) :
    {k : ℕ | ∃ A : Finset ℝ, A.card = n ∧ IsFourFive A ∧ h A = k}.Nonempty := by
  obtain ⟨A, hcard, hA⟩ := exists_sidon_card n
  exact ⟨h A, A, hcard, hA.fourFive, rfl⟩

/-- The natural infimum defining f is attained by an admissible (4,5)-set. -/
theorem f_attained (n : ℕ) :
    ∃ A : Finset ℝ, A.card = n ∧ IsFourFive A ∧ h A = f n := by
  exact Nat.sInf_mem (f_admissible_nonempty n)

theorem g_le_h {A : Finset ℝ} (hw : IsWeakSidon (A : Set ℝ)) : g A.card ≤ h A := by
  exact Nat.sInf_le ⟨A, rfl, hw, rfl⟩

theorem f_le_h {A : Finset ℝ} (hw : IsFourFive A) : f A.card ≤ h A := by
  exact Nat.sInf_le ⟨A, rfl, hw, rfl⟩

/-- Proposition 3.4, with the harmless index-zero cases also included. -/
theorem g_subadditive (m n : ℕ) : g (m+n) ≤ g m + g n := by
  classical
  obtain ⟨A, hAc, hA, hAg⟩ := g_attained m
  obtain ⟨B, hBc, hB, hBg⟩ := g_attained n
  obtain ⟨q,t,hq,hC,hCc,hCh⟩ := weakSidon_affine_gluing A B hA hB
  have hh := g_le_h hC
  rw [hCc, hAc, hBc] at hh
  rw [hAg, hBg] at hCh
  exact hh.trans hCh

/-- The maximum defining h is achieved by an actual Sidon subset. -/
theorem h_attained (A : Finset ℝ) :
    ∃ B : Finset ℝ, B ⊆ A ∧ IsSidon (B : Set ℝ) ∧ B.card = h A := by
  classical
  let T := A.powerset.filter (fun B : Finset ℝ => IsSidon (B : Set ℝ))
  have hemp : (∅ : Finset ℝ) ∈ T := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩
    intro a b c d ha
    simp at ha
  obtain ⟨B,hB,heq⟩ := Finset.exists_mem_eq_sup T ⟨∅,hemp⟩ Finset.card
  obtain ⟨hBA,hBS⟩ := Finset.mem_filter.mp hB
  exact ⟨B, Finset.mem_powerset.mp hBA, hBS, heq.symm⟩

theorem h_empty : h (∅ : Finset ℝ) = 0 := by
  have hh := h_le_card (∅ : Finset ℝ)
  simpa using Nat.eq_zero_of_le_zero hh

theorem g_le_card_index (n : ℕ) : g n ≤ n := by
  obtain ⟨A,hcard,hA⟩ := exists_sidon_card n
  have hh := (g_le_h hA.weak).trans (h_le_card A)
  simpa only [hcard] using hh

theorem f_le_card_index (n : ℕ) : f n ≤ n := by
  obtain ⟨A,hcard,hA⟩ := exists_sidon_card n
  have hh := (f_le_h hA.fourFive).trans (h_le_card A)
  simpa only [hcard] using hh

theorem g_zero : g 0 = 0 := Nat.eq_zero_of_le_zero (g_le_card_index 0)
theorem f_zero : f 0 = 0 := Nat.eq_zero_of_le_zero (f_le_card_index 0)

/-- The optimal universal constant equals the infimum of the finite extremal ratios.
This is the equality assertion of Theorem 1.5, independently of convergence. -/
theorem cStar_eq_inf_f_ratio :
    cStar = sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = (f n : ℝ) / (n : ℝ)} := by
  let D : Set ℝ := {r | ∃ n : ℕ, 1 ≤ n ∧ r = (f n : ℝ) / (n : ℝ)}
  let F : Set ℝ := {c | ∀ A : Finset ℝ, 0 < A.card → IsFourFive A →
    c * (A.card : ℝ) ≤ (h A : ℝ)}
  have hDne : D.Nonempty := ⟨(f 1 : ℝ) / (1 : ℝ), 1, by omega, by simp⟩
  have hDlb : BddBelow D := by
    refine ⟨0, ?_⟩
    rintro r ⟨n,hn,rfl⟩
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hFne : F.Nonempty := by
    refine ⟨0, ?_⟩
    intro A hpos hfour
    simp only [zero_mul]
    exact Nat.cast_nonneg _
  have hupper : ∀ c ∈ F, c ≤ sInf D := by
    intro c hc
    apply le_csInf hDne
    rintro r ⟨n,hn,rfl⟩
    obtain ⟨A,hcard,hfour,hh⟩ := f_attained n
    have hpos : 0 < A.card := by omega
    have hcA := hc A hpos hfour
    rw [hcard,hh] at hcA
    exact (le_div_iff₀ (Nat.cast_pos.mpr (show 0 < n by omega))).mpr hcA
  have hI : sInf D ∈ F := by
    intro A hpos hfour
    have hl : sInf D ≤ (f A.card : ℝ) / (A.card : ℝ) :=
      csInf_le hDlb ⟨A.card, by omega, rfl⟩
    have hm := (le_div_iff₀ (Nat.cast_pos.mpr hpos)).mp hl
    have hf : (f A.card : ℝ) ≤ (h A : ℝ) := Nat.cast_le.mpr (f_le_h hfour)
    exact hm.trans hf
  change sSup F = sInf D
  exact le_antisymm (csSup_le hFne hupper) (le_csSup ⟨sInf D,hupper⟩ hI)

end SidonPaper
