module

public import SidonPaper.Basic
public import Mathlib.Order.Fin.Basic
public import SidonPaper.Relations

@[expose] public section


/-! The five-edge F7 configuration in Ma–Tang, Lemma 5.2.
The orientation proof below is a finite 243-case algebraic proof. Each leaf
is verified by linarith and injectivity; the generation computation is not
trusted and supplies no axioms. In fact weak Sidon suffices for avoidance.
-/
namespace SidonPaper

def IsUnorderedAP (a b c : ℝ) : Prop :=
  b + c = 2 * a ∨ a + c = 2 * b ∨ a + b = 2 * c

theorem weakSidon_unordered {A : Set ℝ} (hw : IsWeakSidon A)
    {a b c d : ℝ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hcd : c ≠ d) (hs : a + b = c + d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases lt_or_gt_of_ne hab with hab | hab
  · rcases lt_or_gt_of_ne hcd with hcd | hcd
    · exact Or.inl (hw ha hb hc hd hab hcd hs)
    · exact Or.inr (hw ha hb hd hc hab hcd (by linarith only [hs]))
  · rcases lt_or_gt_of_ne hcd with hcd | hcd
    · obtain ⟨hbc, had⟩ := hw hb ha hc hd hab hcd (by linarith only [hs])
      exact Or.inr ⟨had, hbc⟩
    · obtain ⟨hbd, hac⟩ := hw hb ha hd hc hab hcd (by linarith only [hs])
      exact Or.inl ⟨hac, hbd⟩

theorem weakSidon_index_pair {A : Set ℝ} (hw : IsWeakSidon A)
    (v : Fin 7 → ℝ) (hv : ∀ i, v i ∈ A) (hinj : Function.Injective v)
    {i j k l : Fin 7} (hij : i < j) (hkl : k < l)
    (hs : v i + v j = v k + v l) : i = k ∧ j = l := by
  have hneq (a b : Fin 7) (hab : a ≠ b) : v a ≠ v b := fun h => hab (hinj h)
  rcases weakSidon_unordered hw (hv i) (hv j) (hv k) (hv l)
    (hneq i j (ne_of_lt hij)) (hneq k l (ne_of_lt hkl)) hs with h | h
  · exact ⟨hinj h.1, hinj h.2⟩
  · have hi := hinj h.1
    have hj := hinj h.2
    have hlk : l < k := by simpa only [hi, hj] using hij
    exact False.elim ((not_lt_of_ge hkl.le) hlk)

set_option maxHeartbeats 0

/-- No injective seven-point configuration has the five AP edges of F7.
This proves the geometric content of Lemma 5.2 for all weak Sidon sets. -/
theorem weakSidon_no_F7_configuration {A : Set ℝ} (hw : IsWeakSidon A)
    (v : Fin 7 → ℝ) (hv : ∀ i, v i ∈ A) (hinj : Function.Injective v)
    (h0 : IsUnorderedAP (v 0) (v 1) (v 2))
    (h1 : IsUnorderedAP (v 0) (v 3) (v 4))
    (h2 : IsUnorderedAP (v 0) (v 5) (v 6))
    (h3 : IsUnorderedAP (v 1) (v 3) (v 5))
    (h4 : IsUnorderedAP (v 2) (v 4) (v 6)) : False := by
  unfold IsUnorderedAP at h0 h1 h2 h3 h4
  rcases h0 with h0 | h0 | h0
  · rcases h1 with h1 | h1 | h1
    · rcases h2 with h2 | h2 | h2
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 + v 2 = v 3 + v 4 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (1 : Fin 7) < 2) (by decide : (3 : Fin 7) < 4) he
            exact (by decide : (1 : Fin 7) ≠ 3) hp.1
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 + v 2 = v 3 + v 4 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (1 : Fin 7) < 2) (by decide : (3 : Fin 7) < 4) he
            exact (by decide : (1 : Fin 7) ≠ 3) hp.1
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 + v 2 = v 3 + v 4 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (1 : Fin 7) < 2) (by decide : (3 : Fin 7) < 4) he
            exact (by decide : (1 : Fin 7) ≠ 3) hp.1
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 2 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 4 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (4 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 6) (hinj he)
          · have he : v 3 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (3 : Fin 7) ≠ 6) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
    · rcases h2 with h2 | h2 | h2
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 2 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 3 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (3 : Fin 7) ≠ 6) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 1 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 4) (hinj he)
          · have he : v 1 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 6) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 1 = v 2 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (2 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 2) hp.1
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
          · have he : v 0 + v 4 = v 1 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 4) (by decide : (1 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 1) hp.1
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 + v 3 = v 4 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 3) (by decide : (4 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 4) hp.1
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
    · rcases h2 with h2 | h2 | h2
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 4) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 4 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (4 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 1 = v 2 + v 4 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (2 : Fin 7) < 4) he
            exact (by decide : (0 : Fin 7) ≠ 2) hp.1
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 + v 4 = v 3 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 4) (by decide : (3 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 3) hp.1
        · rcases h4 with h4 | h4 | h4
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
          · have he : v 0 + v 3 = v 2 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 3) (by decide : (2 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 2) hp.1
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 2 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 2 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
  · rcases h1 with h1 | h1 | h1
    · rcases h2 with h2 | h2 | h2
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 4) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 6) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 2 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 3 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (3 : Fin 7) ≠ 6) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
          · have he : v 0 + v 2 = v 3 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 2) (by decide : (3 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 3) hp.1
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 + v 1 = v 2 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (2 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 2) hp.1
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 1 = v 2 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (2 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 2) hp.1
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
    · rcases h2 with h2 | h2 | h2
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 2 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 5) (hinj he)
          · have he : v 4 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (4 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 2 = v 3 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 2) (by decide : (3 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 3) hp.1
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 + v 4 = v 1 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 4) (by decide : (1 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 1) hp.1
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 + v 6 = v 1 + v 3 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 6) (by decide : (1 : Fin 7) < 3) he
            exact (by decide : (0 : Fin 7) ≠ 1) hp.1
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 3 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (3 : Fin 7) ≠ 6) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 6) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 2 = v 5 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 2) (by decide : (5 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 5) hp.1
          · have he : v 0 + v 1 = v 3 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (3 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 3) hp.1
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
    · rcases h2 with h2 | h2 | h2
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
          · have he : v 0 + v 2 = v 3 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 2) (by decide : (3 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 3) hp.1
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 1 = v 2 + v 4 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (2 : Fin 7) < 4) he
            exact (by decide : (0 : Fin 7) ≠ 2) hp.1
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 + v 1 = v 2 + v 4 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (2 : Fin 7) < 4) he
            exact (by decide : (0 : Fin 7) ≠ 2) hp.1
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 3 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (3 : Fin 7) ≠ 6) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 2 = v 3 + v 4 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 2) (by decide : (3 : Fin 7) < 4) he
            exact (by decide : (0 : Fin 7) ≠ 3) hp.1
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 + v 1 = v 4 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (4 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 4) hp.1
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 4) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 3 = v 1 + v 2 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 3) (by decide : (1 : Fin 7) < 2) he
            exact (by decide : (0 : Fin 7) ≠ 1) hp.1
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 1 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 4) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 3 = v 2 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 3) (by decide : (2 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 2) hp.1
          · have he : v 1 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 6) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
  · rcases h1 with h1 | h1 | h1
    · rcases h2 with h2 | h2 | h2
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 2 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 3) (hinj he)
          · have he : v 2 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 + v 2 = v 1 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 2) (by decide : (1 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 1) hp.1
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 + v 2 = v 1 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 2) (by decide : (1 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 1) hp.1
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 1 = v 4 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (4 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 4) hp.1
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 4) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 4 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (4 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
    · rcases h2 with h2 | h2 | h2
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 + v 2 = v 1 + v 3 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 2) (by decide : (1 : Fin 7) < 3) he
            exact (by decide : (0 : Fin 7) ≠ 1) hp.1
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 1 = v 4 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (4 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 4) hp.1
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
          · have he : v 2 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (2 : Fin 7) ≠ 4) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 + v 2 = v 1 + v 3 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 2) (by decide : (1 : Fin 7) < 3) he
            exact (by decide : (0 : Fin 7) ≠ 1) hp.1
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 + v 4 = v 1 + v 2 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 4) (by decide : (1 : Fin 7) < 2) he
            exact (by decide : (0 : Fin 7) ≠ 1) hp.1
          · have he : v 0 + v 3 = v 2 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 3) (by decide : (2 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 2) hp.1
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 1 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 6) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 4) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 + v 1 = v 3 + v 4 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (3 : Fin 7) < 4) he
            exact (by decide : (0 : Fin 7) ≠ 3) hp.1
          · have he : v 1 = v 4 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 4) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 3 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (3 : Fin 7) ≠ 6) (hinj he)
          · have he : v 0 + v 1 = v 4 + v 5 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (4 : Fin 7) < 5) he
            exact (by decide : (0 : Fin 7) ≠ 4) hp.1
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
    · rcases h2 with h2 | h2 | h2
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 1 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 6) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 3 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (3 : Fin 7) ≠ 6) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 1 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 6) (hinj he)
          · have he : v 0 + v 1 = v 5 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (5 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 5) hp.1
        · rcases h4 with h4 | h4 | h4
          · have he : v 3 = v 6 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (3 : Fin 7) ≠ 6) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
          · have he : v 0 + v 1 = v 3 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (3 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 3) hp.1
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 = v 1 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 1) (hinj he)
          · have he : v 0 = v 5 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (0 : Fin 7) ≠ 5) (hinj he)
      · rcases h3 with h3 | h3 | h3
        · rcases h4 with h4 | h4 | h4
          · have he : v 0 + v 1 = v 4 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 1) (by decide : (4 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 4) hp.1
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 + v 3 = v 2 + v 6 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 3) (by decide : (2 : Fin 7) < 6) he
            exact (by decide : (0 : Fin 7) ≠ 2) hp.1
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
        · rcases h4 with h4 | h4 | h4
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 1 = v 3 := by linarith only [h0, h1, h2, h3, h4]
            exact (by decide : (1 : Fin 7) ≠ 3) (hinj he)
          · have he : v 0 + v 5 = v 2 + v 4 := by linarith only [h0, h1, h2, h3, h4]
            have hp := weakSidon_index_pair hw v hv hinj (by decide : (0 : Fin 7) < 5) (by decide : (2 : Fin 7) < 4) he
            exact (by decide : (0 : Fin 7) ≠ 2) hp.1

/-- Lemma 5.2 in the paper's (4,5)-set setting. -/
theorem fourFive_no_F7_configuration {A : Finset ℝ} (hA : IsFourFive A)
    (v : Fin 7 → ℝ) (hv : ∀ i, v i ∈ A) (hinj : Function.Injective v)
    (h0 : IsUnorderedAP (v 0) (v 1) (v 2))
    (h1 : IsUnorderedAP (v 0) (v 3) (v 4))
    (h2 : IsUnorderedAP (v 0) (v 5) (v 6))
    (h3 : IsUnorderedAP (v 1) (v 3) (v 5))
    (h4 : IsUnorderedAP (v 2) (v 4) (v 6)) : False :=
  weakSidon_no_F7_configuration hA.weakSidon v hv hinj h0 h1 h2 h3 h4

end SidonPaper
