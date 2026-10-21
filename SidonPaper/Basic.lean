module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section


/-!
Partial formalization of Ma–Tang, arXiv:2602.23282v2.
This module develops the elementary additive foundation; it does not prove
Theorems 1.2, 1.3, 1.5 or 1.6.
-/
namespace SidonPaper

/-- Uniqueness of sums of nondecreasing pairs, including repeated summands. -/
def IsSidon (A : Set ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- Uniqueness of sums of strictly increasing pairs. -/
def IsWeakSidon (A : Set ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a < b → c < d → a + b = c + d → a = c ∧ b = d

/-- No nonconstant three-term arithmetic progression. -/
def IsAPFree (A : Set ℝ) : Prop :=
  ∀ ⦃a b c : ℝ⦄, a ∈ A → b ∈ A → c ∈ A →
    a < b → b < c → a + c ≠ b + b

theorem IsSidon.weak {A : Set ℝ} (h : IsSidon A) : IsWeakSidon A := by
  intro a b c d ha hb hc hd hab hcd hs
  exact h ha hb hc hd hab.le hcd.le hs

theorem IsSidon.mono {A B : Set ℝ} (h : IsSidon A) (hBA : B ⊆ A) :
    IsSidon B := by
  intro a b c d ha hb hc hd hab hcd hs
  exact h (hBA ha) (hBA hb) (hBA hc) (hBA hd) hab hcd hs

theorem IsWeakSidon.mono {A B : Set ℝ} (h : IsWeakSidon A) (hBA : B ⊆ A) :
    IsWeakSidon B := by
  intro a b c d ha hb hc hd hab hcd hs
  exact h (hBA ha) (hBA hb) (hBA hc) (hBA hd) hab hcd hs

theorem IsSidon.apFree {A : Set ℝ} (h : IsSidon A) : IsAPFree A := by
  intro a b c ha hb hc hab hbc hs
  have he := h ha hc hb hb (by linarith) le_rfl hs
  linarith [he.1]

/-- The substantive equivalence in Lemma 2.3; no finiteness is needed. -/
theorem sidon_iff_apFree {A : Set ℝ} (hw : IsWeakSidon A) :
    IsSidon A ↔ IsAPFree A := by
  constructor
  · exact IsSidon.apFree
  · intro hf a b c d ha hb hc hd hab hcd hs
    rcases lt_or_eq_of_le hab with hab | hab
    · rcases lt_or_eq_of_le hcd with hcd | hcd
      · exact hw ha hb hc hd hab hcd hs
      · subst d
        have hac : a < c := by linarith
        have hcb : c < b := by linarith
        exact False.elim (hf ha hc hb hac hcb hs)
    · subst b
      rcases lt_or_eq_of_le hcd with hcd | hcd
      · have hca : c < a := by linarith
        have had : a < d := by linarith
        exact False.elim (hf hc ha hd hca had hs.symm)
      · subst d
        constructor <;> linarith

/-- Subset version of Lemma 2.3. -/
theorem sidon_subset_iff_apFree {A S : Set ℝ} (hw : IsWeakSidon A) (hSA : S ⊆ A) :
    IsSidon S ↔ IsAPFree S :=
  sidon_iff_apFree (hw.mono hSA)

/-- Injectivity of the midpoint assignment, the first part of Lemma 2.4.
The ordered endpoints uniquely specify the AP edge. -/
theorem ap_endpoints_unique {A : Set ℝ} (hw : IsWeakSidon A)
    {a b c d x : ℝ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a < b) (hcd : c < d) (hax : a + b = x + x)
    (hcx : c + d = x + x) : a = c ∧ b = d := by
  exact hw ha hb hc hd hab hcd (hax.trans hcx.symm)

/-- A midpoint lies strictly between its ordered endpoints. -/
theorem ap_midpoint_between {a b x : ℝ} (hab : a < b) (h : a + b = x + x) :
    a < x ∧ x < b := by
  constructor <;> linarith

/-- Affine invariance of the Sidon predicate in Lemmas 3.2 and 3.5. -/
theorem sidon_affine_iff (A : Set ℝ) {q t : ℝ} (hq : 0 < q) :
    IsSidon ((fun x => q * x + t) '' A) ↔ IsSidon A := by
  constructor
  · intro h a b c d ha hb hc hd hab hcd hs
    have he := h ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      (by nlinarith) (by nlinarith) (by nlinarith [hs])
    constructor <;> nlinarith [he.1, he.2]
  · intro h x y u v hx hy hu hv hxy huv hs
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    rcases hu with ⟨c, hc, rfl⟩
    rcases hv with ⟨d, hd, rfl⟩
    have he := h ha hb hc hd (by nlinarith) (by nlinarith) (by nlinarith [hs])
    rcases he with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Affine invariance of the weak Sidon predicate in Lemma 3.2. -/
theorem weakSidon_affine_iff (A : Set ℝ) {q t : ℝ} (hq : 0 < q) :
    IsWeakSidon ((fun x => q * x + t) '' A) ↔ IsWeakSidon A := by
  constructor
  · intro h a b c d ha hb hc hd hab hcd hs
    have he := h ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      (by nlinarith) (by nlinarith) (by nlinarith [hs])
    constructor <;> nlinarith [he.1, he.2]
  · intro h x y u v hx hy hu hv hxy huv hs
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    rcases hu with ⟨c, hc, rfl⟩
    rcases hv with ⟨d, hd, rfl⟩
    have he := h ha hb hc hd (by nlinarith) (by nlinarith) (by nlinarith [hs])
    rcases he with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

end SidonPaper
