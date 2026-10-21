module

public import SidonPaper.TransversalReduction
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

@[expose] public section


namespace SidonPaper.FiniteHypergraph
variable {α : Type*} [DecidableEq α]

/-- Select one vertex from every edge. This elementary bound includes isolated
vertices and the empty edge family. -/
theorem tau_le_edges (H : FiniteHypergraph α) : H.tau ≤ H.edges.card := by
  classical
  let pick : H.edges → α := fun e => Classical.choose (H.edge_nonempty e.1 e.2)
  have hmem (e : H.edges) : pick e ∈ e.1 := Classical.choose_spec (H.edge_nonempty e.1 e.2)
  let T := H.edges.attach.image pick
  have hsub : T ⊆ H.vertices := by
    intro x hx
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    exact H.edge_subset e.1 e.2 (hmem e)
  have ht : H.Transversal T := by
    intro e he
    exact ⟨pick ⟨e,he⟩,hmem ⟨e,he⟩,
      Finset.mem_image.mpr ⟨⟨e,he⟩,Finset.mem_attach _ _,rfl⟩⟩
  have hcard : T.card ≤ H.edges.card := by
    exact (Finset.card_image_le).trans_eq (Finset.card_attach)
  exact (H.tau_le_card hsub ht).trans hcard

/-- Pay for selected vertices and cover the remaining untouched edges optimally. -/
theorem tau_le_delete_add_card (H : FiniteHypergraph α) {P : Finset α}
    (hP : P ⊆ H.vertices) : H.tau ≤ (H.deleteVertices P).tau + P.card := by
  classical
  obtain ⟨T,hTsub,hT,hTc⟩ := (H.deleteVertices P).tau_attained
  have hcover : ∀ e ∈ H.removedEdges P, ∃ x ∈ e, x ∈ P := by
    intro e he
    exact Finset.not_disjoint_iff.mp (Finset.mem_filter.mp he).2
  have hsub : T ∪ P ⊆ H.vertices := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact (Finset.mem_sdiff.mp (hTsub hx)).1
    · exact hP hx
  have hbound := H.tau_le_card hsub (transversal_deleteVertices_extend hT hcover)
  have hc := Finset.card_union_le T P
  omega

/-- The matching-to-transversal counting step: if selected vertices hit exactly
twice as many distinct edges, their selection saves one vertex per pair. -/
theorem tau_add_card_le_edges_of_double_coverage (H : FiniteHypergraph α)
    {P : Finset α} (hP : P ⊆ H.vertices)
    (hdouble : (H.removedEdges P).card = 2 * P.card) :
    H.tau + P.card ≤ H.edges.card := by
  have ht := H.tau_le_delete_add_card hP
  have he := (H.deleteVertices P).tau_le_edges
  have hc := H.deleteVertices_edge_accounting P
  omega

/-- Double counting incidences in the finite hypergraph model. -/
theorem sum_card_edges_eq_sum_degree (H : FiniteHypergraph α) :
    (∑ e ∈ H.edges, e.card) = ∑ x ∈ H.vertices, H.degree x := by
  classical
  calc
    (∑ e ∈ H.edges, e.card) =
        ∑ e ∈ H.edges, (H.vertices.bipartiteAbove (fun e x => x ∈ e) e).card := by
      apply Finset.sum_congr rfl
      intro e he
      congr 1
      ext x
      simp only [Finset.bipartiteAbove,Finset.mem_filter]
      exact ⟨fun hxe => ⟨H.edge_subset e he hxe,hxe⟩,fun hx => hx.2⟩
    _ = ∑ x ∈ H.vertices, (H.edges.bipartiteBelow (fun e x => x ∈ e) x).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ = ∑ x ∈ H.vertices, H.degree x := rfl

/-- A two-regular three-uniform hypergraph satisfies3m=2n, including the emptycase. -/
theorem three_edges_eq_two_vertices {H : FiniteHypergraph α} (h3 : H.ThreeUniform)
    (h2 : ∀ x ∈ H.vertices, H.degree x = 2) :
    3 * H.edges.card = 2 * H.vertices.card := by
  have hc := H.sum_card_edges_eq_sum_degree
  have he : (∑ e ∈ H.edges, e.card) = 3 * H.edges.card := by
    calc
      _ = ∑ e ∈ H.edges, 3 := Finset.sum_congr rfl h3
      _ = _ := by simp [Nat.mul_comm]
  have hv : (∑ x ∈ H.vertices, H.degree x) = 2 * H.vertices.card := by
    calc
      _ = ∑ x ∈ H.vertices, 2 := Finset.sum_congr rfl h2
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- Convert a sufficiently large packing of incident pairs into the exact
transversal inequality for the two-regular three-uniform case. -/
theorem transversal_four_of_double_coverage {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) (h2 : ∀ x ∈ H.vertices, H.degree x = 2)
    {P : Finset α} (hP : P ⊆ H.vertices)
    (hdouble : (H.removedEdges P).card = 2 * P.card)
    (hsize : H.vertices.card ≤ 4 * P.card) :
    4 * H.tau ≤ H.vertices.card + H.edges.card := by
  have ht := H.tau_add_card_le_edges_of_double_coverage hP hdouble
  have hc := three_edges_eq_two_vertices h3 h2
  omega

end SidonPaper.FiniteHypergraph
