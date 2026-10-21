module

public import SidonPaper.AffineExtremal
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort

@[expose] public section


namespace SidonPaper

/-- Maximum Sidon subset size is subadditive under finite unions. -/
theorem h_union_le (A B : Finset ℝ) : h (A ∪ B) ≤ h A + h B := by
  classical
  unfold h
  apply Finset.sup_le_iff.mpr
  intro S hS
  obtain ⟨hSsub, hSidon⟩ := Finset.mem_filter.mp hS
  have hSU : S ⊆ A ∪ B := Finset.mem_powerset.mp hSsub
  have hSA : S ∩ A ⊆ A := Finset.inter_subset_right
  have hSB : S \ A ⊆ B := by
    intro x hx
    obtain ⟨hxS, hxA⟩ := Finset.mem_sdiff.mp hx
    exact (Finset.mem_union.mp (hSU hxS)).resolve_left hxA
  have hAS : (S ∩ A : Finset ℝ) ⊆ S := Finset.inter_subset_left
  have hBS : S \ A ⊆ S := Finset.sdiff_subset
  have ha := card_le_h hSA (hSidon.mono (by exact hAS))
  have hb := card_le_h hSB (hSidon.mono (by exact hBS))
  have hcard := Finset.card_inter_add_card_sdiff S A
  unfold h at ha hb
  omega

/-- A generic separated-block criterion for a weak Sidon union. -/
theorem weakSidon_union_of_separated {A B : Finset ℝ}
    (hA : IsWeakSidon (A : Set ℝ)) (hB : IsWeakSidon (B : Set ℝ))
    (horder : ∀ a ∈ A, ∀ b ∈ B, a < b)
    (hfirst : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ B, a + b < c + d)
    (hlast : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B, a + b < c + d)
    (hmixed : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ A, ∀ d ∈ B,
      a + b = c + d → a = c ∧ b = d) : IsWeakSidon (A ∪ B : Finset ℝ) := by
  classical
  have hclass {x y : ℝ} (hx : x ∈ A ∪ B) (hy : y ∈ A ∪ B) (hxy : x < y) :
      (x ∈ A ∧ y ∈ A) ∨ (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ B) := by
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact Or.inl ⟨hx, hy⟩
      · exact Or.inr (Or.inl ⟨hx, hy⟩)
    · rcases Finset.mem_union.mp hy with hy | hy
      · have hh := horder y hy x hx
        linarith
      · exact Or.inr (Or.inr ⟨hx, hy⟩)
  intro a b c d ha hb hc hd hab hcd heq
  rcases hclass ha hb hab with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    rcases hclass hc hd hcd with ⟨hc,hd⟩ | ⟨hc,hd⟩ | ⟨hc,hd⟩
  · exact hA ha hb hc hd hab hcd heq
  · have hh := hfirst a ha b hb c hc d hd
    linarith
  · have h1 := horder a ha c hc
    have h2 := horder b hb d hd
    linarith
  · have hh := hfirst c hc d hd a ha b hb
    linarith
  · exact hmixed a ha b hb c hc d hd heq
  · have hh := hlast a ha b hb c hc d hd
    linarith
  · have h1 := horder c hc a ha
    have h2 := horder d hd b hb
    linarith
  · have hh := hlast c hc d hd a ha b hb
    linarith
  · exact hB ha hb hc hd hab hcd heq

/-- Choose a positive slope with no collisions between mixed sums or mixed differences. -/
theorem exists_positive_mixed_injective (A B : Finset ℝ) :
    ∃ q : ℝ, 0 < q ∧ ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ A, ∀ d ∈ B,
      a + q*b = c + q*d → a = c ∧ b = d := by
  classical
  let R := ((A.product A).product (B.product B)).image
    (fun p => (p.1.2 - p.1.1) / (p.2.1 - p.2.2))
  obtain ⟨q, hq, hqR⟩ := (Set.Ioi_infinite (0 : ℝ)).exists_notMem_finset R
  refine ⟨q, hq, ?_⟩
  intro a ha b hb c hc d hd heq
  by_cases hbd : b = d
  · subst d
    exact ⟨by linarith, rfl⟩
  · have hden : b-d ≠ 0 := sub_ne_zero.mpr hbd
    have hratio : (c-a)/(b-d) = q := (div_eq_iff hden).mpr (by nlinarith)
    have hmem : (c-a)/(b-d) ∈ R := by
      apply Finset.mem_image.mpr
      exact ⟨((a,c),(b,d)), Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha,hc⟩, Finset.mem_product.mpr ⟨hb,hd⟩⟩, rfl⟩
    rw [hratio] at hmem
    exact False.elim (hqR hmem)

/-- Every finite real set lies in a symmetric bounded interval with positive radius. -/
theorem finite_symmetric_bound (C : Finset ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ C, -L ≤ x ∧ x ≤ L := by
  obtain ⟨m, hm⟩ := C.finite_toSet.bddBelow
  obtain ⟨M, hM⟩ := C.finite_toSet.bddAbove
  refine ⟨|m| + |M| + 1, by positivity, ?_⟩
  intro x hx
  have hmx : m ≤ x := hm hx
  have hxM : x ≤ M := hM hx
  constructor <;> linarith [neg_abs_le m, le_abs_self M, abs_nonneg m, abs_nonneg M]

/-- Lemma 3.3: generic positive rescaling and sufficiently large translation
produce a weak Sidon union, including the cases of empty input sets. -/
theorem weakSidon_affine_gluing (A B : Finset ℝ)
    (hA : IsWeakSidon (A : Set ℝ)) (hB : IsWeakSidon (B : Set ℝ)) :
    ∃ q t : ℝ, 0 < q ∧ IsWeakSidon (A ∪ affineImage B q t : Finset ℝ) ∧
      (A ∪ affineImage B q t).card = A.card + B.card ∧
      h (A ∪ affineImage B q t) ≤ h A + h B := by
  classical
  obtain ⟨q, hq, hinj⟩ := exists_positive_mixed_injective A B
  obtain ⟨L, hL, hbound⟩ := finite_symmetric_bound (A ∪ affineImage B q 0)
  let t := 5 * L
  have hleft : ∀ x ∈ A, -L ≤ x ∧ x ≤ L := by
    intro x hx
    exact hbound x (Finset.mem_union_left _ hx)
  have hright : ∀ x ∈ affineImage B q t, t-L ≤ x ∧ x ≤ t+L := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    have hqb : q*b ∈ affineImage B q 0 := by
      exact Finset.mem_image.mpr ⟨b,hb, by simp⟩
    have hh := hbound (q*b) (Finset.mem_union_right _ hqb)
    constructor <;> linarith
  have horder : ∀ a ∈ A, ∀ b ∈ affineImage B q t, a < b := by
    intro a ha b hb
    have hla := hleft a ha
    have hrb := hright b hb
    dsimp [t] at hrb
    linarith
  have hfirst : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ affineImage B q t,
      a+b < c+d := by
    intro a ha b hb c hc d hd
    have hla := hleft a ha
    have hlb := hleft b hb
    have hlc := hleft c hc
    have hrd := hright d hd
    dsimp [t] at hrd
    linarith
  have hlast : ∀ a ∈ A, ∀ b ∈ affineImage B q t,
      ∀ c ∈ affineImage B q t, ∀ d ∈ affineImage B q t, a+b < c+d := by
    intro a ha b hb c hc d hd
    have hla := hleft a ha
    have hrb := hright b hb
    have hrc := hright c hc
    have hrd := hright d hd
    dsimp [t] at hrb hrc hrd
    linarith
  have hmixed : ∀ a ∈ A, ∀ b ∈ affineImage B q t,
      ∀ c ∈ A, ∀ d ∈ affineImage B q t, a+b=c+d → a=c ∧ b=d := by
    intro a ha b hb c hc d hd heq
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨d0, hd0, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨rfl,rfl⟩ := hinj a ha b0 hb0 c hc d0 hd0 (by linarith)
    exact ⟨rfl,rfl⟩
  have hdisj : Disjoint A (affineImage B q t) := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    have hh := horder x hxA x hxB
    exact (lt_irrefl x) hh
  refine ⟨q,t,hq,?_,?_,?_⟩
  · exact weakSidon_union_of_separated hA
      ((weakSidon_affineImage_iff B hq).mpr hB) horder hfirst hlast hmixed
  · rw [Finset.card_union_of_disjoint hdisj, affineImage_card B hq]
  · simpa only [h_affineImage B hq] using h_union_le A (affineImage B q t)

/-- An ordered pair contributes its positive difference. -/
theorem mem_differences {S : Finset ℝ} {a b : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) : b-a ∈ differences S := by
  classical
  exact Finset.mem_image.mpr ⟨(a,b),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩, hab⟩, rfl⟩

private theorem card_five_chain {a b c d e : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) :
    ({a,b,c,d,e} : Finset ℝ).card = 5 := by
  classical
  have hac := lt_trans hab hbc
  have had := lt_trans hac hcd
  have hae := lt_trans had hde
  have hbd := lt_trans hbc hcd
  have hbe := lt_trans hbd hde
  have hce := lt_trans hcd hde
  simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt hcd, ne_of_lt hde,
    ne_of_lt hac, ne_of_lt had, ne_of_lt hae, ne_of_lt hbd, ne_of_lt hbe,
    ne_of_lt hce]

/-- Five explicitly ordered differences certify the (4,5) lower bound. -/
theorem five_le_differences_of_chain {S : Finset ℝ} {a b c d e : ℝ}
    (ha : a ∈ differences S) (hb : b ∈ differences S)
    (hc : c ∈ differences S) (hd : d ∈ differences S) (he : e ∈ differences S)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) :
    5 ≤ (differences S).card := by
  classical
  have hsub : ({a,b,c,d,e} : Finset ℝ) ⊆ differences S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  rw [← card_five_chain hab hbc hcd hde]
  exact Finset.card_le_card hsub

/-- Three vertices in the left block and one in the right supply three large
mixed differences and two small internal differences. -/
theorem differences_three_left {A B S : Finset ℝ}
    (hgap : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ A, ∀ d ∈ A, d-c < b-a)
    {a b c d : ℝ} (ha : a ∈ A) (_hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ B)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hab : a<b) (hbc : b<c) (hcd : c<d) : 5 ≤ (differences S).card := by
  have hac : a<c := lt_trans hab hbc
  have had : a<d := lt_trans hac hcd
  have hbd : b<d := lt_trans hbc hcd
  exact five_le_differences_of_chain
    (mem_differences haS hbS hab) (mem_differences haS hcS hac)
    (mem_differences hcS hdS hcd) (mem_differences hbS hdS hbd)
    (mem_differences haS hdS had) (by linarith) (hgap c hc d hd a ha c hc)
    (by linarith) (by linarith)

/-- One vertex in the left block and three in the right. -/
theorem differences_three_right {A B S : Finset ℝ}
    (hgap : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B, d-c < b-a)
    {a b c d : ℝ} (ha : a ∈ A) (hb : b ∈ B) (_hc : c ∈ B) (hd : d ∈ B)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hab : a<b) (hbc : b<c) (hcd : c<d) : 5 ≤ (differences S).card := by
  have hac : a<c := lt_trans hab hbc
  have had : a<d := lt_trans hac hcd
  have hbd : b<d := lt_trans hbc hcd
  exact five_le_differences_of_chain
    (mem_differences hbS hcS hbc) (mem_differences hbS hdS hbd)
    (mem_differences haS hbS hab) (mem_differences haS hcS hac)
    (mem_differences haS hdS had) (by linarith) (hgap a ha b hb b hb d hd)
    (by linarith) (by linarith)

/-- Two vertices in each block yield four distinct mixed differences and one
strictly smaller internal difference. -/
theorem differences_two_each {A B S : Finset ℝ}
    (hgap : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ A, ∀ d ∈ A, d-c < b-a)
    (hinj : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ A, ∀ d ∈ B,
      b-a=d-c → a=c ∧ b=d)
    {a b c d : ℝ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ B) (hd : d ∈ B)
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hab : a<b) (hbc : b<c) (hcd : c<d) : 5 ≤ (differences S).card := by
  have hac : a<c := lt_trans hab hbc
  have had : a<d := lt_trans hac hcd
  have hbd : b<d := lt_trans hbc hcd
  have hneq : c-a ≠ d-b := by
    intro he
    have hh := hinj a ha c hc b hb d hd he
    linarith [hh.1]
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · exact five_le_differences_of_chain
      (mem_differences haS hbS hab) (mem_differences hbS hcS hbc)
      (mem_differences haS hcS hac) (mem_differences hbS hdS hbd)
      (mem_differences haS hdS had) (hgap b hb c hc a ha b hb)
      (by linarith) hlt (by linarith)
  · exact five_le_differences_of_chain
      (mem_differences haS hbS hab) (mem_differences hbS hcS hbc)
      (mem_differences hbS hdS hbd) (mem_differences haS hcS hac)
      (mem_differences haS hdS had) (hgap b hb c hc a ha b hb)
      (by linarith) hgt (by linarith)

/-- Local difference conditions are preserved when ordered blocks have
injective mixed differences, all larger than internal differences. -/
theorem fourFive_union_of_separated {A B : Finset ℝ}
    (hA : IsFourFive A) (hB : IsFourFive B)
    (horder : ∀ a ∈ A, ∀ b ∈ B, a < b)
    (hgapA : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ A, ∀ d ∈ A, d-c < b-a)
    (hgapB : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B, d-c < b-a)
    (hinj : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ A, ∀ d ∈ B,
      b-a=d-c → a=c ∧ b=d) : IsFourFive (A ∪ B) := by
  classical
  intro S hSU hcard
  let e := S.orderEmbOfFin hcard
  have hm (i : Fin 4) : e i ∈ S := S.orderEmbOfFin_mem hcard i
  have h01 : e 0 < e 1 := e.strictMono (by decide)
  have h12 : e 1 < e 2 := e.strictMono (by decide)
  have h23 : e 2 < e 3 := e.strictMono (by decide)
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  have hrepr : S = {e 0,e 1,e 2,e 3} := by
    calc
      S = Finset.univ.image e := (S.image_orderEmbOfFin_univ hcard).symm
      _ = {e 0,e 1,e 2,e 3} := by rw [hu]; simp
  have hsubA (h0 : e 0 ∈ A) (h1 : e 1 ∈ A) (h2 : e 2 ∈ A) (h3 : e 3 ∈ A) : S ⊆ A := by
    intro x hx
    rw [hrepr] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hsubB (h0 : e 0 ∈ B) (h1 : e 1 ∈ B) (h2 : e 2 ∈ B) (h3 : e 3 ∈ B) : S ⊆ B := by
    intro x hx
    rw [hrepr] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h0 := Finset.mem_union.mp (hSU (hm 0))
  have h1 := Finset.mem_union.mp (hSU (hm 1))
  have h2 := Finset.mem_union.mp (hSU (hm 2))
  have h3 := Finset.mem_union.mp (hSU (hm 3))
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  all_goals first
    | exact hA S (hsubA ‹e 0 ∈ A› ‹e 1 ∈ A› ‹e 2 ∈ A› ‹e 3 ∈ A›) hcard
    | exact hB S (hsubB ‹e 0 ∈ B› ‹e 1 ∈ B› ‹e 2 ∈ B› ‹e 3 ∈ B›) hcard
    | exact differences_three_left hgapA ‹e 0 ∈ A› ‹e 1 ∈ A› ‹e 2 ∈ A› ‹e 3 ∈ B›
        (hm 0) (hm 1) (hm 2) (hm 3) h01 h12 h23
    | exact differences_three_right hgapB ‹e 0 ∈ A› ‹e 1 ∈ B› ‹e 2 ∈ B› ‹e 3 ∈ B›
        (hm 0) (hm 1) (hm 2) (hm 3) h01 h12 h23
    | exact differences_two_each hgapA hinj ‹e 0 ∈ A› ‹e 1 ∈ A› ‹e 2 ∈ B› ‹e 3 ∈ B›
        (hm 0) (hm 1) (hm 2) (hm 3) h01 h12 h23
    | (exfalso; have hh := horder (e 1) ‹e 1 ∈ A› (e 0) ‹e 0 ∈ B›; linarith)
    | (exfalso; have hh := horder (e 2) ‹e 2 ∈ A› (e 0) ‹e 0 ∈ B›; linarith)
    | (exfalso; have hh := horder (e 3) ‹e 3 ∈ A› (e 0) ‹e 0 ∈ B›; linarith)
    | (exfalso; have hh := horder (e 2) ‹e 2 ∈ A› (e 1) ‹e 1 ∈ B›; linarith)
    | (exfalso; have hh := horder (e 3) ‹e 3 ∈ A› (e 1) ‹e 1 ∈ B›; linarith)
    | (exfalso; have hh := horder (e 3) ‹e 3 ∈ A› (e 2) ‹e 2 ∈ B›; linarith)

/-- Lemma 3.6: separated affine gluing of finite (4,5)-sets. -/
theorem fourFive_affine_gluing (A B : Finset ℝ) (hA : IsFourFive A) (hB : IsFourFive B) :
    ∃ q t : ℝ, 0 < q ∧ IsFourFive (A ∪ affineImage B q t) ∧
      (A ∪ affineImage B q t).card = A.card + B.card ∧
      h (A ∪ affineImage B q t) ≤ h A + h B := by
  classical
  obtain ⟨q, hq, hinj⟩ := exists_positive_mixed_injective A B
  obtain ⟨L, hL, hbound⟩ := finite_symmetric_bound (A ∪ affineImage B q 0)
  let t := 5 * L
  have hleft : ∀ x ∈ A, -L ≤ x ∧ x ≤ L := by
    intro x hx
    exact hbound x (Finset.mem_union_left _ hx)
  have hright : ∀ x ∈ affineImage B q t, t-L ≤ x ∧ x ≤ t+L := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    have hqb : q*b ∈ affineImage B q 0 := by
      exact Finset.mem_image.mpr ⟨b,hb, by simp⟩
    have hh := hbound (q*b) (Finset.mem_union_right _ hqb)
    constructor <;> linarith
  have horder : ∀ a ∈ A, ∀ b ∈ affineImage B q t, a < b := by
    intro a ha b hb
    have hla := hleft a ha
    have hrb := hright b hb
    dsimp [t] at hrb
    linarith
  have hgapA : ∀ a ∈ A, ∀ b ∈ affineImage B q t,
      ∀ c ∈ A, ∀ d ∈ A, d-c < b-a := by
    intro a ha b hb c hc d hd
    have hla := hleft a ha
    have hrb := hright b hb
    have hlc := hleft c hc
    have hld := hleft d hd
    dsimp [t] at hrb
    linarith
  have hgapB : ∀ a ∈ A, ∀ b ∈ affineImage B q t,
      ∀ c ∈ affineImage B q t, ∀ d ∈ affineImage B q t, d-c < b-a := by
    intro a ha b hb c hc d hd
    have hla := hleft a ha
    have hrb := hright b hb
    have hrc := hright c hc
    have hrd := hright d hd
    dsimp [t] at hrb hrc hrd
    linarith
  have hmixed : ∀ a ∈ A, ∀ b ∈ affineImage B q t,
      ∀ c ∈ A, ∀ d ∈ affineImage B q t, b-a=d-c → a=c ∧ b=d := by
    intro a ha b hb c hc d hd heq
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨d0, hd0, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨rfl,rfl⟩ := hinj a ha d0 hd0 c hc b0 hb0 (by linarith)
    exact ⟨rfl,rfl⟩
  have hdisj : Disjoint A (affineImage B q t) := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    have hh := horder x hxA x hxB
    exact (lt_irrefl x) hh
  refine ⟨q,t,hq,?_,?_,?_⟩
  · exact fourFive_union_of_separated hA
      ((fourFive_affineImage_iff B hq).mpr hB) horder hgapA hgapB hmixed
  · rw [Finset.card_union_of_disjoint hdisj, affineImage_card B hq]
  · simpa only [h_affineImage B hq] using h_union_le A (affineImage B q t)

#print axioms weakSidon_affine_gluing
#print axioms fourFive_affine_gluing
end SidonPaper
