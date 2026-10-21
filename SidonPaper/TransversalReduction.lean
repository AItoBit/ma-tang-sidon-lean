module

public import SidonPaper.HypergraphBridge
public import Lean.Elab.Tactic.Omega

@[expose] public section


namespace SidonPaper.FiniteHypergraph
variable {α : Type*} [DecidableEq α]

/-- Edges incident with a specified vertex. -/
def incidentEdges (H : FiniteHypergraph α) (x : α) : Finset (Finset α) :=
  H.edges.filter (fun e => x ∈ e)

def degree (H : FiniteHypergraph α) (x : α) : ℕ := (H.incidentEdges x).card

/-- Edges removed when deleting a set of vertices. -/
def removedEdges (H : FiniteHypergraph α) (S : Finset α) : Finset (Finset α) :=
  H.edges.filter (fun e => ¬ Disjoint e S)

/-- Delete vertices and every edge touching them, without shrinking retained edges. -/
def deleteVertices (H : FiniteHypergraph α) (S : Finset α) : FiniteHypergraph α where
  vertices := H.vertices \ S
  edges := H.edges.filter (fun e => Disjoint e S)
  edge_subset := by
    intro e he x hx
    obtain ⟨he,hd⟩ := Finset.mem_filter.mp he
    exact Finset.mem_sdiff.mpr ⟨H.edge_subset e he hx,
      fun hxs => Finset.disjoint_left.mp hd hx hxs⟩
  edge_nonempty := by
    intro e he
    exact H.edge_nonempty e (Finset.mem_filter.mp he).1

@[simp] theorem deleteVertices_vertices (H : FiniteHypergraph α) (S : Finset α) :
    (H.deleteVertices S).vertices = H.vertices \ S := rfl

@[simp] theorem deleteVertices_edges (H : FiniteHypergraph α) (S : Finset α) :
    (H.deleteVertices S).edges = H.edges.filter (fun e => Disjoint e S) := rfl

theorem deleteVertices_uniform {H : FiniteHypergraph α} (hH : H.ThreeUniform) (S : Finset α) :
    (H.deleteVertices S).ThreeUniform := by
  intro e he
  exact hH e (Finset.mem_filter.mp he).1

theorem deleteVertices_edge_accounting (H : FiniteHypergraph α) (S : Finset α) :
    (H.deleteVertices S).edges.card + (H.removedEdges S).card = H.edges.card := by
  exact Finset.card_filter_add_card_filter_not (s := H.edges) (p := fun e => Disjoint e S)

theorem deleteVertices_vertex_accounting (H : FiniteHypergraph α) {S : Finset α}
    (hS : S ⊆ H.vertices) : (H.deleteVertices S).vertices.card + S.card = H.vertices.card := by
  exact Finset.card_sdiff_add_card_eq_card hS

/-- Extend a transversal of the deletion by vertices hitting all deleted edges. -/
theorem transversal_deleteVertices_extend {H : FiniteHypergraph α}
    {S P T : Finset α} (hT : (H.deleteVertices S).Transversal T)
    (hP : ∀ e ∈ H.removedEdges S, ∃ x ∈ e, x ∈ P) :
    H.Transversal (T ∪ P) := by
  intro e he
  by_cases hd : Disjoint e S
  · obtain ⟨x,hxe,hxT⟩ := hT e (Finset.mem_filter.mpr ⟨he,hd⟩)
    exact ⟨x,hxe,Finset.mem_union_left _ hxT⟩
  · obtain ⟨x,hxe,hxP⟩ := hP e (Finset.mem_filter.mpr ⟨he,hd⟩)
    exact ⟨x,hxe,Finset.mem_union_right _ hxP⟩

/-- Cardinality reduction used in the induction proof of Theorem4.6.
The retained hypergraph's inequality is an induction hypothesis, not a new axiom. -/
theorem transversal_four_lift {H : FiniteHypergraph α} {S P : Finset α}
    (hS : S ⊆ H.vertices) (hPsub : P ⊆ H.vertices)
    (hP : ∀ e ∈ H.removedEdges S, ∃ x ∈ e, x ∈ P)
    (hpay : 4 * P.card ≤ S.card + (H.removedEdges S).card)
    (hdel : 4 * (H.deleteVertices S).tau ≤
      (H.deleteVertices S).vertices.card + (H.deleteVertices S).edges.card) :
    4 * H.tau ≤ H.vertices.card + H.edges.card := by
  obtain ⟨T,hTsub,hT,hTc⟩ := (H.deleteVertices S).tau_attained
  have hsub : T ∪ P ⊆ H.vertices := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact (Finset.mem_sdiff.mp (hTsub hx)).1
    · exact hPsub hx
  have htau := H.tau_le_card hsub (transversal_deleteVertices_extend hT hP)
  have hu := Finset.card_union_le T P
  have hv := deleteVertices_vertex_accounting H hS
  have he := deleteVertices_edge_accounting H S
  omega

@[simp] theorem removedEdges_singleton (H : FiniteHypergraph α) (x : α) :
    H.removedEdges {x} = H.incidentEdges x := by
  ext e
  simp [removedEdges,incidentEdges]

/-- The high-degree induction step of Theorem4.6. -/
theorem transversal_four_high_degree {H : FiniteHypergraph α} {x : α}
    (hx : x ∈ H.vertices) (hdeg : 3 ≤ H.degree x)
    (hdel : 4 * (H.deleteVertices {x}).tau ≤
      (H.deleteVertices {x}).vertices.card + (H.deleteVertices {x}).edges.card) :
    4 * H.tau ≤ H.vertices.card + H.edges.card := by
  apply transversal_four_lift (S := {x}) (P := {x})
  · simpa using hx
  · simpa using hx
  · intro e he
    have hxE := (Finset.mem_filter.mp (show e ∈ H.incidentEdges x by simpa using he)).2
    exact ⟨x,hxE,by simp⟩
  · simp only [Finset.card_singleton,removedEdges_singleton]
    change 4 * 1 ≤ 1 + H.degree x
    omega
  · exact hdel

/-- Any counterexample with a high-degree vertex yields a strictly smaller
counterexample by deleting that vertex. -/
theorem high_degree_counterexample_reduction {H : FiniteHypergraph α} {x : α}
    (hx : x ∈ H.vertices) (hdeg : 3 ≤ H.degree x)
    (hbad : H.vertices.card + H.edges.card < 4 * H.tau) :
    (H.deleteVertices {x}).vertices.card < H.vertices.card ∧
    (H.deleteVertices {x}).vertices.card + (H.deleteVertices {x}).edges.card <
      4 * (H.deleteVertices {x}).tau := by
  constructor
  · have hv := deleteVertices_vertex_accounting H (S := {x}) (by simpa using hx)
    simp only [Finset.card_singleton] at hv
    omega
  · by_contra hnot
    have hb := transversal_four_high_degree hx hdeg (by omega)
    omega

/-- A degree-one vertex is incident with exactly its specified edge. -/
theorem edge_eq_of_degree_one {H : FiniteHypergraph α} {x : α} {e f : Finset α}
    (hx : H.degree x = 1) (he : e ∈ H.edges) (hxe : x ∈ e)
    (hf : f ∈ H.edges) (hxf : x ∈ f) : f = e := by
  obtain ⟨g,hg⟩ := Finset.card_eq_one.mp hx
  have he' : e ∈ H.incidentEdges x := Finset.mem_filter.mpr ⟨he,hxe⟩
  have hf' : f ∈ H.incidentEdges x := Finset.mem_filter.mpr ⟨hf,hxf⟩
  rw [hg] at he' hf'
  have heq : e = g := by simpa using he'
  have hfq : f = g := by simpa using hf'
  exact hfq.trans heq.symm

/-- If b has degree one in an edge containing a, deleting a,b kills
exactly the edges already incident with a. -/
theorem removedEdges_pair_of_degree_one {H : FiniteHypergraph α} {a b : α}
    {e : Finset α} (he : e ∈ H.edges) (ha : a ∈ e) (hb : b ∈ e)
    (hdeg : H.degree b = 1) : H.removedEdges {a,b} = H.incidentEdges a := by
  ext f
  constructor
  · intro hf
    have hfmem : f ∈ H.edges ∧ ¬ Disjoint f {a,b} := Finset.mem_filter.mp hf
    obtain ⟨hfE,hnd⟩ := hfmem
    obtain ⟨x,hxf,hxs⟩ := Finset.not_disjoint_iff.mp hnd
    simp only [Finset.mem_insert,Finset.mem_singleton] at hxs
    rcases hxs with hxa|hxb
    · subst x
      exact Finset.mem_filter.mpr ⟨hfE,hxf⟩
    · subst x
      have hfe := edge_eq_of_degree_one hdeg he hb hfE hxf
      exact Finset.mem_filter.mpr ⟨hfE,hfe.symm ▸ ha⟩
  · intro hf
    obtain ⟨hf,haF⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨hf,Finset.not_disjoint_iff.mpr ⟨a,haF,by simp⟩⟩

/-- Mixed degree-two/degree-one reduction in the short proof of4.6. -/
theorem transversal_four_mixed_edge {H : FiniteHypergraph α} {a b : α} {e : Finset α}
    (he : e ∈ H.edges) (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b)
    (hda : 2 ≤ H.degree a) (hdb : H.degree b = 1)
    (hdel : 4 * (H.deleteVertices {a,b}).tau ≤
      (H.deleteVertices {a,b}).vertices.card + (H.deleteVertices {a,b}).edges.card) :
    4 * H.tau ≤ H.vertices.card + H.edges.card := by
  apply transversal_four_lift (S := {a,b}) (P := {a})
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact H.edge_subset e he ha
    · exact H.edge_subset e he hb
  · simpa using H.edge_subset e he ha
  · intro f hf
    rw [removedEdges_pair_of_degree_one he ha hb hdb] at hf
    exact ⟨a,(Finset.mem_filter.mp hf).2,by simp⟩
  · rw [removedEdges_pair_of_degree_one he ha hb hdb]
    simp only [Finset.card_singleton,Finset.card_insert_of_notMem
      (show a ∉ ({b}:Finset α) by simpa using hab),Finset.card_singleton]
    change 4 * 1 ≤ 1 + 1 + H.degree a
    omega
  · exact hdel

/-- Deleting an edge all of whose vertices have degree one kills only that edge. -/
theorem removedEdges_isolated_edge {H : FiniteHypergraph α} {e : Finset α}
    (he : e ∈ H.edges) (hdeg : ∀ x ∈ e, H.degree x = 1) :
    H.removedEdges e = {e} := by
  ext f
  constructor
  · intro hf
    obtain ⟨hf,hnd⟩ := Finset.mem_filter.mp hf
    obtain ⟨x,hxf,hxe⟩ := Finset.not_disjoint_iff.mp hnd
    exact Finset.mem_singleton.mpr (edge_eq_of_degree_one (hdeg x hxe) he hxe hf hxf)
  · intro hf
    have hfe := Finset.mem_singleton.mp hf
    subst f
    obtain ⟨x,hxe⟩ := H.edge_nonempty e he
    exact Finset.mem_filter.mpr ⟨he,Finset.not_disjoint_iff.mpr ⟨x,hxe,hxe⟩⟩

/-- Isolated three-edge reduction in the short proof of4.6. -/
theorem transversal_four_isolated_edge {H : FiniteHypergraph α} (h3 : H.ThreeUniform)
    {e : Finset α} (he : e ∈ H.edges) (hdeg : ∀ x ∈ e, H.degree x = 1)
    (hdel : 4 * (H.deleteVertices e).tau ≤
      (H.deleteVertices e).vertices.card + (H.deleteVertices e).edges.card) :
    4 * H.tau ≤ H.vertices.card + H.edges.card := by
  obtain ⟨a,ha⟩ := H.edge_nonempty e he
  apply transversal_four_lift (S := e) (P := {a}) (H.edge_subset e he)
  · simpa using H.edge_subset e he ha
  · intro f hf
    rw [removedEdges_isolated_edge he hdeg] at hf
    have hfe := Finset.mem_singleton.mp hf
    exact ⟨a,hfe.symm ▸ ha,by simp⟩
  · rw [removedEdges_isolated_edge he hdeg,h3 e he]
    simp
  · exact hdel

theorem tau_eq_zero_of_edges_empty {H : FiniteHypergraph α} (he : H.edges = ∅) :
    H.tau = 0 := by
  have ht : H.Transversal ∅ := by
    intro e hmem
    simp [he] at hmem
  exact Nat.eq_zero_of_le_zero (H.tau_le_card (Finset.empty_subset _) ht)

/-- Removing an isolated vertex costs no transversal vertex. -/
theorem transversal_four_isolated_vertex {H : FiniteHypergraph α} {x : α}
    (hx : x ∈ H.vertices) (hdeg : H.degree x = 0)
    (hdel : 4 * (H.deleteVertices {x}).tau ≤
      (H.deleteVertices {x}).vertices.card + (H.deleteVertices {x}).edges.card) :
    4 * H.tau ≤ H.vertices.card + H.edges.card := by
  apply transversal_four_lift (S := {x}) (P := ∅)
  · simpa using hx
  · exact Finset.empty_subset _
  · have he : H.removedEdges {x} = ∅ := by
      rw [removedEdges_singleton]
      exact Finset.card_eq_zero.mp hdeg
    simp [he]
  · simp
  · exact hdel

/-- Any failure of Theorem4.6 has a finite three-uniform TWO-REGULAR
counterexample. This is an unconditional reduction, not an assumed bound. -/
theorem counterexample_has_deletion_minimal_two_regular {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) (hbad : H.vertices.card + H.edges.card < 4 * H.tau) :
    ∃ K : FiniteHypergraph α, K.ThreeUniform ∧
      (∀ x ∈ K.vertices, K.degree x = 2) ∧
      K.vertices.card + K.edges.card < 4 * K.tau ∧
      (∀ S : Finset α, S ⊆ K.vertices → S.Nonempty →
        4 * (K.deleteVertices S).tau ≤
          (K.deleteVertices S).vertices.card + (K.deleteVertices S).edges.card) ∧
      K.vertices.card ≤ H.vertices.card := by
  classical
  let P : ℕ → Prop := fun n => ∃ K : FiniteHypergraph α,
    K.ThreeUniform ∧ K.vertices.card + K.edges.card < 4 * K.tau ∧ K.vertices.card = n
  have hex : ∃ n, P n := ⟨H.vertices.card,H,h3,hbad,rfl⟩
  obtain ⟨K,hK3,hKbad,hKsize⟩ := Nat.find_spec hex
  have hminimal {S : Finset α} (hS : S ⊆ K.vertices) (hSne : S.Nonempty) :
      4 * (K.deleteVertices S).tau ≤
        (K.deleteVertices S).vertices.card + (K.deleteVertices S).edges.card := by
    by_contra hn
    have hv := deleteVertices_vertex_accounting K hS
    have hpos := Finset.card_pos.mpr hSne
    have hlt : (K.deleteVertices S).vertices.card < Nat.find hex := by omega
    exact Nat.find_min hex hlt
      ⟨K.deleteVertices S,deleteVertices_uniform hK3 S,by omega,rfl⟩
  have hlow (x : α) (hx : x ∈ K.vertices) : 1 ≤ K.degree x := by
    by_contra hn
    have hzero : K.degree x = 0 := by omega
    have hdel := hminimal (S := {x}) (by simpa using hx) (by simp)
    have hh := transversal_four_isolated_vertex hx hzero hdel
    omega
  have hhigh (x : α) (hx : x ∈ K.vertices) : K.degree x ≤ 2 := by
    by_contra hn
    have hdel := hminimal (S := {x}) (by simpa using hx) (by simp)
    have hh := transversal_four_high_degree hx (by omega) hdel
    omega
  have hreg (x : α) (hx : x ∈ K.vertices) : K.degree x = 2 := by
    have hxlo := hlow x hx
    have hxhi := hhigh x hx
    by_contra hn
    have hxone : K.degree x = 1 := by omega
    obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < (K.incidentEdges x).card by change 0 < K.degree x; omega)
    obtain ⟨he,hxe⟩ := Finset.mem_filter.mp he
    by_cases ha : ∃ a ∈ e, 2 ≤ K.degree a
    · obtain ⟨a,hae,hda⟩ := ha
      have hax : a ≠ x := by intro h; subst a; omega
      have hsub : ({a,x}:Finset α) ⊆ K.vertices := by
        intro z hz
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz
        rcases hz with rfl|rfl
        · exact K.edge_subset e he hae
        · exact hx
      have hdel := hminimal hsub (by simp)
      have hh := transversal_four_mixed_edge he hae hxe hax hda hxone hdel
      omega
    · have hd : ∀ a ∈ e, K.degree a = 1 := by
        intro a hae
        have hl := hlow a (K.edge_subset e he hae)
        have hu : ¬ 2 ≤ K.degree a := fun h => ha ⟨a,hae,h⟩
        omega
      have hdel := hminimal (K.edge_subset e he) (K.edge_nonempty e he)
      have hh := transversal_four_isolated_edge hK3 he hd hdel
      omega
  exact ⟨K,hK3,hreg,hKbad,(fun S hs hne => hminimal hs hne),by
    have hh := Nat.find_min' hex (show P H.vertices.card from ⟨H,h3,hbad,rfl⟩)
    omega⟩

/-- Any failed three-uniform inequality has a two-regular counterexample. -/
theorem counterexample_has_two_regular {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) (hbad : H.vertices.card + H.edges.card < 4 * H.tau) :
    ∃ K : FiniteHypergraph α, K.ThreeUniform ∧
      (∀ x ∈ K.vertices, K.degree x = 2) ∧
      K.vertices.card + K.edges.card < 4 * K.tau ∧
      K.vertices.card ≤ H.vertices.card := by
  obtain ⟨K,hK3,hreg,hbad,hm,hc⟩ := counterexample_has_deletion_minimal_two_regular h3 hbad
  exact ⟨K,hK3,hreg,hbad,hc⟩

theorem incidentEdges_eq_pair {H : FiniteHypergraph α} {x : α} {e f : Finset α}
    (hdeg : H.degree x = 2) (he : e ∈ H.edges) (hf : f ∈ H.edges)
    (hxe : x ∈ e) (hxf : x ∈ f) (hef : e ≠ f) :
    H.incidentEdges x = {e,f} := by
  have hsub : ({e,f}:Finset (Finset α)) ⊆ H.incidentEdges x := by
    intro g hg
    simp only [Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with rfl|rfl
    · exact Finset.mem_filter.mpr ⟨he,hxe⟩
    · exact Finset.mem_filter.mpr ⟨hf,hxf⟩
  have hc : ({e,f}:Finset (Finset α)).card=2 := by simp [hef]
  exact (Finset.eq_of_subset_of_card_le hsub (by change H.degree x ≤ _; omega)).symm

/-- The two-edge/two-common-vertices reduction handles all nonsimple dual edges. -/
theorem transversal_four_double_intersection {H : FiniteHypergraph α}
    {e f : Finset α} {a b : α}
    (he : e ∈ H.edges) (hf : f ∈ H.edges) (hef : e ≠ f)
    (hae : a ∈ e) (haf : a ∈ f) (hbe : b ∈ e) (hbf : b ∈ f) (hab : a ≠ b)
    (hda : H.degree a = 2) (hdb : H.degree b = 2)
    (hdel : 4 * (H.deleteVertices {a,b}).tau ≤
      (H.deleteVertices {a,b}).vertices.card + (H.deleteVertices {a,b}).edges.card) :
    4 * H.tau ≤ H.vertices.card + H.edges.card := by
  have haInc := incidentEdges_eq_pair hda he hf hae haf hef
  have hbInc := incidentEdges_eq_pair hdb he hf hbe hbf hef
  have hrem : H.removedEdges {a,b} = {e,f} := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgE,hnd⟩ := Finset.mem_filter.mp hg
      obtain ⟨x,hxg,hxs⟩ := Finset.not_disjoint_iff.mp hnd
      simp only [Finset.mem_insert,Finset.mem_singleton] at hxs
      rcases hxs with hxa|hxb
      · subst x
        rw [← haInc]
        exact Finset.mem_filter.mpr ⟨hgE,hxg⟩
      · subst x
        rw [← hbInc]
        exact Finset.mem_filter.mpr ⟨hgE,hxg⟩
    · intro hg
      have hgInc : g ∈ H.incidentEdges a := by rwa [haInc]
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hgInc).1,
        Finset.not_disjoint_iff.mpr ⟨a,(Finset.mem_filter.mp hgInc).2,by simp⟩⟩
  apply transversal_four_lift (S := {a,b}) (P := {a})
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact H.edge_subset e he hae
    · exact H.edge_subset e he hbe
  · simpa using H.edge_subset e he hae
  · intro g hg
    rw [hrem,← haInc] at hg
    exact ⟨a,(Finset.mem_filter.mp hg).2,by simp⟩
  · rw [hrem]
    simp [hab,hef]
  · exact hdel

/-- A counterexample to4.6 would yield a linear two-regular counterexample. -/
theorem counterexample_has_deletion_minimal_linear_two_regular {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) (hbad : H.vertices.card + H.edges.card < 4 * H.tau) :
    ∃ K : FiniteHypergraph α, K.ThreeUniform ∧ K.Linear ∧
      (∀ x ∈ K.vertices, K.degree x = 2) ∧
      K.vertices.card + K.edges.card < 4 * K.tau ∧
      (∀ S : Finset α, S ⊆ K.vertices → S.Nonempty →
        4 * (K.deleteVertices S).tau ≤
          (K.deleteVertices S).vertices.card + (K.deleteVertices S).edges.card) ∧
      K.vertices.card ≤ H.vertices.card := by
  classical
  obtain ⟨K,hK3,hreg,hKbad,hmin,hcard⟩ :=
    counterexample_has_deletion_minimal_two_regular h3 hbad
  have hlin : K.Linear := by
    intro e he f hf hef
    by_contra hn
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp
      (show 1 < (e ∩ f).card by omega)
    obtain ⟨hae,haf⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbe,hbf⟩ := Finset.mem_inter.mp hb
    have hsub : ({a,b}:Finset α) ⊆ K.vertices := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact K.edge_subset e he hae
      · exact K.edge_subset e he hbe
    have hbnd := transversal_four_double_intersection he hf hef hae haf hbe hbf hab
      (hreg a (K.edge_subset e he hae)) (hreg b (K.edge_subset e he hbe))
      (hmin _ hsub (by simp))
    omega
  exact ⟨K,hK3,hlin,hreg,hKbad,hmin,hcard⟩

/-- Linear two-regular form of the counterexample reduction. -/
theorem counterexample_has_linear_two_regular {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) (hbad : H.vertices.card + H.edges.card < 4 * H.tau) :
    ∃ K : FiniteHypergraph α, K.ThreeUniform ∧ K.Linear ∧
      (∀ x ∈ K.vertices, K.degree x = 2) ∧
      K.vertices.card + K.edges.card < 4 * K.tau ∧
      K.vertices.card ≤ H.vertices.card := by
  obtain ⟨K,hK3,hlin,hreg,hbad,hm,hc⟩ :=
    counterexample_has_deletion_minimal_linear_two_regular h3 hbad
  exact ⟨K,hK3,hlin,hreg,hbad,hc⟩

end SidonPaper.FiniteHypergraph
