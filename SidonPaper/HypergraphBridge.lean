module

public import SidonPaper.Targets
public import SidonPaper.F7Free
public import SidonPaper.APBounds
public import SidonPaper.APLinearity
public import Lean.Elab.Tactic.Omega

@[expose] public section


namespace SidonPaper

/-- Finite hypergraphs with nonempty edges, including isolated vertices. -/
structure FiniteHypergraph (α : Type*) where
  vertices : Finset α
  edges : Finset (Finset α)
  edge_subset : ∀ e ∈ edges, e ⊆ vertices
  edge_nonempty : ∀ e ∈ edges, e.Nonempty

namespace FiniteHypergraph
variable {α : Type*} (H : FiniteHypergraph α)

def Independent (S : Finset α) : Prop := ∀ e ∈ H.edges, ¬ e ⊆ S

def Transversal (T : Finset α) : Prop := ∀ e ∈ H.edges, ∃ x ∈ e, x ∈ T

noncomputable def alpha : ℕ := by
  classical
  exact (H.vertices.powerset.filter (fun S : Finset α => H.Independent S)).sup Finset.card

noncomputable def tau : ℕ :=
  sInf {n : ℕ | ∃ T : Finset α, T ⊆ H.vertices ∧ H.Transversal T ∧ T.card = n}

theorem independent_empty : H.Independent ∅ := by
  intro e he hsub
  obtain ⟨x, hx⟩ := H.edge_nonempty e he
  have := hsub hx
  simp at this

theorem transversal_vertices : H.Transversal H.vertices := by
  intro e he
  obtain ⟨x, hx⟩ := H.edge_nonempty e he
  exact ⟨x, hx, H.edge_subset e he hx⟩

theorem independent_complement_iff [DecidableEq α] (S : Finset α) :
    H.Independent S ↔ H.Transversal (H.vertices \ S) := by
  constructor
  · intro hi e he
    obtain ⟨x, hx, hxS⟩ := Finset.not_subset.mp (hi e he)
    exact ⟨x, hx, Finset.mem_sdiff.mpr ⟨H.edge_subset e he hx, hxS⟩⟩
  · intro ht e he hes
    obtain ⟨x, hx, hxT⟩ := ht e he
    exact (Finset.mem_sdiff.mp hxT).2 (hes hx)

theorem transversal_complement_independent [DecidableEq α] {T : Finset α}
    (ht : H.Transversal T) : H.Independent (H.vertices \ T) := by
  intro e he hes
  obtain ⟨x, hx, hxT⟩ := ht e he
  exact (Finset.mem_sdiff.mp (hes hx)).2 hxT

theorem card_le_alpha {S : Finset α} (hS : S ⊆ H.vertices) (hi : H.Independent S) :
    S.card ≤ H.alpha := by
  classical
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hi⟩)

theorem alpha_attained : ∃ S : Finset α, S ⊆ H.vertices ∧ H.Independent S ∧ S.card = H.alpha := by
  classical
  let F := H.vertices.powerset.filter (fun S : Finset α => H.Independent S)
  have he : (∅ : Finset α) ∈ F := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), H.independent_empty⟩
  obtain ⟨S, hS, hcard⟩ := Finset.exists_mem_eq_sup F ⟨∅, he⟩ Finset.card
  have hs := Finset.mem_filter.mp hS
  exact ⟨S, Finset.mem_powerset.mp hs.1, hs.2, hcard.symm⟩

theorem tau_attained : ∃ T : Finset α, T ⊆ H.vertices ∧ H.Transversal T ∧ T.card = H.tau := by
  have hn : {n : ℕ | ∃ T : Finset α, T ⊆ H.vertices ∧ H.Transversal T ∧ T.card = n}.Nonempty :=
    ⟨H.vertices.card, H.vertices, Finset.Subset.refl _, H.transversal_vertices, rfl⟩
  exact Nat.sInf_mem hn

theorem tau_le_card {T : Finset α} (hT : T ⊆ H.vertices) (ht : H.Transversal T) :
    H.tau ≤ T.card := by
  exact Nat.sInf_le ⟨T, hT, ht, rfl⟩

/-- Independence number and transversal number are complementary. -/
theorem alpha_add_tau : H.alpha + H.tau = H.vertices.card := by
  classical
  obtain ⟨S, hS, hi, hcardS⟩ := H.alpha_attained
  obtain ⟨T, hT, ht, hcardT⟩ := H.tau_attained
  have hsmall := H.tau_le_card (Finset.sdiff_subset) ((H.independent_complement_iff S).mp hi)
  have hlarge := H.card_le_alpha (Finset.sdiff_subset) (H.transversal_complement_independent ht)
  have hs := Finset.card_sdiff_add_card_eq_card hS
  have htcard := Finset.card_sdiff_add_card_eq_card hT
  omega

end FiniteHypergraph

/-- Forget the canonical ordering of an AP edge. -/
noncomputable def edgeVertices (p : ℝ × ℝ × ℝ) : Finset ℝ := by
  classical
  exact {p.1, p.2.1, p.2.2}

noncomputable def apHyperedges (A : Finset ℝ) : Finset (Finset ℝ) := by
  classical
  exact (apEdges A).image edgeVertices

theorem edgeVertices_subset {A : Finset ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ apEdges A) : edgeVertices p ⊆ A := by
  classical
  have hp' := Finset.mem_filter.mp hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp'.1
  obtain ⟨hb, hc⟩ := Finset.mem_product.mp hb
  intro x hx
  simp only [edgeVertices, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

theorem edgeVertices_card {A : Finset ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∈ apEdges A) : (edgeVertices p).card = 3 := by
  classical
  have hp' := (Finset.mem_filter.mp hp).2
  simp [edgeVertices, ne_of_lt hp'.1, ne_of_lt hp'.2.1,
    ne_of_lt (lt_trans hp'.1 hp'.2.1)]

/-- The AP hypergraph as a finite hypergraph of actual three-element edges. -/
noncomputable def apHypergraph (A : Finset ℝ) : FiniteHypergraph ℝ where
  vertices := A
  edges := apHyperedges A
  edge_subset := by
    classical
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact edgeVertices_subset hp
  edge_nonempty := by
    classical
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    apply Finset.card_pos.mp
    rw [edgeVertices_card hp]
    decide

theorem apHypergraph_three_uniform (A : Finset ℝ) :
    ∀ e ∈ (apHypergraph A).edges, e.card = 3 := by
  classical
  intro e he
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
  exact edgeVertices_card hp

/-- Canonical increasing AP triples give distinct three-element hyperedges. -/
theorem edgeVertices_injective_on (A : Finset ℝ) :
    Set.InjOn edgeVertices (apEdges A) := by
  classical
  intro p hp q hq he
  have hpO := (Finset.mem_filter.mp hp).2
  have hqO := (Finset.mem_filter.mp hq).2
  have hp1in : p.1 ∈ edgeVertices q := by rw [← he]; simp [edgeVertices]
  have hq1in : q.1 ∈ edgeVertices p := by rw [he]; simp [edgeVertices]
  have hp3in : p.2.2 ∈ edgeVertices q := by rw [← he]; simp [edgeVertices]
  have hq3in : q.2.2 ∈ edgeVertices p := by rw [he]; simp [edgeVertices]
  have hp2in : p.2.1 ∈ edgeVertices q := by rw [← he]; simp [edgeVertices]
  simp only [edgeVertices, Finset.mem_insert, Finset.mem_singleton] at hp1in hq1in hp3in hq3in hp2in
  have hle : p.1 ≤ q.1 := by
    rcases hq1in with h | h | h <;> linarith [hpO.1, hpO.2.1]
  have hge : q.1 ≤ p.1 := by
    rcases hp1in with h | h | h <;> linarith [hqO.1, hqO.2.1]
  have hlo : p.1 = q.1 := le_antisymm hle hge
  have hle3 : p.2.2 ≤ q.2.2 := by
    rcases hp3in with h | h | h <;> linarith [hqO.1, hqO.2.1]
  have hge3 : q.2.2 ≤ p.2.2 := by
    rcases hq3in with h | h | h <;> linarith [hpO.1, hpO.2.1]
  have hhi : p.2.2 = q.2.2 := le_antisymm hle3 hge3
  apply Prod.ext hlo
  apply Prod.ext ?_ hhi
  rcases hp2in with h | h | h <;> linarith [hpO.1, hpO.2.1]

theorem apHyperedges_card (A : Finset ℝ) :
    (apHyperedges A).card = (apEdges A).card := by
  classical
  exact Finset.card_image_iff.mpr (edgeVertices_injective_on A)

/-- Lemma 2.4 in the actual finite-three-set hypergraph representation. -/
theorem apHypergraph_edges_card_le {A : Finset ℝ} (hw : IsWeakSidon (A : Set ℝ))
    (hcard : 2 ≤ A.card) : (apHypergraph A).edges.card ≤ A.card - 2 := by
  change (apHyperedges A).card ≤ _
  rw [apHyperedges_card]
  exact apEdges_card_le hw hcard

/-- AP-free subsets are exactly independent sets in the AP hypergraph. -/
theorem apFree_iff_independent {A S : Finset ℝ} (hSA : S ⊆ A) :
    IsAPFree (S : Set ℝ) ↔ (apHypergraph A).Independent S := by
  classical
  constructor
  · intro hf e he hsub
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hpO := (Finset.mem_filter.mp hp).2
    have ha : p.1 ∈ S := hsub (by simp [edgeVertices])
    have hb : p.2.1 ∈ S := hsub (by simp [edgeVertices])
    have hc : p.2.2 ∈ S := hsub (by simp [edgeVertices])
    exact hf ha hb hc hpO.1 hpO.2.1 hpO.2.2
  · intro hi a b c ha hb hc hab hbc hs
    have hp : (a,b,c) ∈ apEdges A := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨hSA ha, Finset.mem_product.mpr ⟨hSA hb, hSA hc⟩⟩,
        hab, hbc, hs⟩
    have he : edgeVertices (a,b,c) ∈ (apHypergraph A).edges :=
      Finset.mem_image.mpr ⟨(a,b,c), hp, rfl⟩
    apply hi _ he
    intro x hx
    simp only [edgeVertices, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption

/-- Independence number in the finite hypergraph model agrees with the
AP-free maximum already used in Lemma 2.3. -/
theorem apHypergraph_alpha (A : Finset ℝ) :
    (apHypergraph A).alpha = apIndependenceNumber A := by
  classical
  unfold FiniteHypergraph.alpha apIndependenceNumber
  congr 1
  apply Finset.filter_congr
  intro S hS
  exact (apFree_iff_independent (Finset.mem_powerset.mp hS)).symm

/-- The extremal Sidon size is the hypergraph independence number. -/
theorem h_eq_hypergraph_alpha {A : Finset ℝ} (hw : IsWeakSidon (A : Set ℝ)) :
    h A = (apHypergraph A).alpha := by
  rw [apHypergraph_alpha]
  exact h_eq_apIndependenceNumber hw

/-- The complement identity needed by both lower-bound arguments. -/
theorem h_add_hypergraph_tau {A : Finset ℝ} (hw : IsWeakSidon (A : Set ℝ)) :
    h A + (apHypergraph A).tau = A.card := by
  rw [h_eq_hypergraph_alpha hw]
  exact (apHypergraph A).alpha_add_tau

namespace FiniteHypergraph
variable {α : Type*}

def ThreeUniform (H : FiniteHypergraph α) : Prop := ∀ e ∈ H.edges, e.card = 3

def Linear [DecidableEq α] (H : FiniteHypergraph α) : Prop :=
  ∀ e ∈ H.edges, ∀ f ∈ H.edges, e ≠ f → (e ∩ f).card ≤ 1

/-- Non-induced containment of the five-edge seven-vertex F7 configuration. -/
def ContainsF7 [DecidableEq α] (H : FiniteHypergraph α) : Prop :=
  ∃ v : Fin 7 → α, Function.Injective v ∧ (∀ i, v i ∈ H.vertices) ∧
    {v 0,v 1,v 2} ∈ H.edges ∧ {v 0,v 3,v 4} ∈ H.edges ∧
    {v 0,v 5,v 6} ∈ H.edges ∧ {v 1,v 3,v 5} ∈ H.edges ∧
    {v 2,v 4,v 6} ∈ H.edges

end FiniteHypergraph

theorem apHypergraph_uniform (A : Finset ℝ) : (apHypergraph A).ThreeUniform :=
  apHypergraph_three_uniform A

/-- The AP hypergraph of a (4,5)-set is linear (Lemma 2.5). -/
theorem apHypergraph_linear {A : Finset ℝ} (hA : IsFourFive A) :
    (apHypergraph A).Linear := by
  classical
  intro e he f hf hef
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
  have hpq : p ≠ q := fun h => hef (congrArg edgeVertices h)
  exact apEdges_linear hA hp hq hpq

/-- An unordered enumeration of any AP hyperedge satisfies one midpoint equation. -/
theorem unorderedAP_of_apHyperedge {A : Finset ℝ} {a b c : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (he : ({a,b,c} : Finset ℝ) ∈ (apHypergraph A).edges) :
    IsUnorderedAP a b c := by
  classical
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp he
  have hpO := (Finset.mem_filter.mp hp).2
  have ha : a ∈ edgeVertices p := by rw [he]; simp
  have hb : b ∈ edgeVertices p := by rw [he]; simp
  have hc : c ∈ edgeVertices p := by rw [he]; simp
  simp only [edgeVertices, Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    simp_all only [ne_eq, not_true_eq_false]
  all_goals first
    | exact Or.inl (by linarith only [hpO.2.2])
    | exact Or.inr (Or.inl (by linarith only [hpO.2.2]))
    | exact Or.inr (Or.inr (by linarith only [hpO.2.2]))

/-- Lemma 5.2 as literal F7-subhypergraph avoidance. -/
theorem apHypergraph_F7_free {A : Finset ℝ} (hw : IsWeakSidon (A : Set ℝ)) :
    ¬ (apHypergraph A).ContainsF7 := by
  classical
  rintro ⟨v, hinj, hv, h0, h1, h2, h3, h4⟩
  have hd (i j : Fin 7) (hij : i ≠ j) : v i ≠ v j := fun h => hij (hinj h)
  apply weakSidon_no_F7_configuration hw v hv hinj
  · exact unorderedAP_of_apHyperedge (hd 0 1 (by decide))
      (hd 0 2 (by decide)) (hd 1 2 (by decide)) h0
  · exact unorderedAP_of_apHyperedge (hd 0 3 (by decide))
      (hd 0 4 (by decide)) (hd 3 4 (by decide)) h1
  · exact unorderedAP_of_apHyperedge (hd 0 5 (by decide))
      (hd 0 6 (by decide)) (hd 5 6 (by decide)) h2
  · exact unorderedAP_of_apHyperedge (hd 1 3 (by decide))
      (hd 1 5 (by decide)) (hd 3 5 (by decide)) h3
  · exact unorderedAP_of_apHyperedge (hd 2 4 (by decide))
      (hd 2 6 (by decide)) (hd 4 6 (by decide)) h4

theorem fourFive_apHypergraph_F7_free {A : Finset ℝ} (hA : IsFourFive A) :
    ¬ (apHypergraph A).ContainsF7 := apHypergraph_F7_free hA.weakSidon

end SidonPaper
