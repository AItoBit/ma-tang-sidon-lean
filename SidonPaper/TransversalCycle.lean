module

public import SidonPaper.TransversalReduction
public import Mathlib.Combinatorics.SimpleGraph.Girth

@[expose] public section


namespace SidonPaper.FiniteHypergraph
variable {α : Type*} [DecidableEq α]

/-- The simple dual incidence graph: vertices are hyperedges and adjacency means
that two distinct hyperedges meet. For a linear hypergraph its graph edges have
unique labels in the original vertex set. -/
def dualGraph (H : FiniteHypergraph α) : SimpleGraph ↥H.edges where
  Adj e f := e ≠ f ∧ (e.val ∩ f.val).Nonempty
  symm := ⟨fun e f h => ⟨h.1.symm, by simpa [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨fun e h => h.1 rfl⟩

/-- A degree-two point of an edge lies on a different hyperedge. -/
theorem exists_other_incident_edge {H : FiniteHypergraph α} {e : Finset α} {x : α}
    (he : e∈H.edges) (hx : x∈e) (hd : H.degree x=2) :
    ∃ f∈H.edges, x∈f ∧ e≠f := by
  have hei : e∈H.incidentEdges x := Finset.mem_filter.mpr ⟨he,hx⟩
  have hc := Finset.card_erase_of_mem hei
  have hpos : 0 < ((H.incidentEdges x).erase e).card := by
    change (H.incidentEdges x).card=2 at hd
    omega
  obtain ⟨f,hf⟩ := Finset.card_pos.mp hpos
  obtain ⟨hne,hfi⟩ := Finset.mem_erase.mp hf
  obtain ⟨hf,hxf⟩ := Finset.mem_filter.mp hfi
  exact ⟨f,hf,hxf,hne.symm⟩

/-- Every edge of a linear 3-uniform 2-regular hypergraph has two distinct
neighbors in the simple dual graph. -/
theorem dualGraph_two_neighbors {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) (hl : H.Linear)
    (h2 : ∀ x∈H.vertices,H.degree x=2) (e : ↥H.edges) :
    ∃ f g : ↥H.edges, (H.dualGraph).Adj e f ∧ (H.dualGraph).Adj e g ∧ f≠g := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1<e.val.card by rw[h3 e.val e.property]; omega)
  obtain ⟨f,hf,haf,hef⟩ := exists_other_incident_edge e.property ha
    (h2 a (H.edge_subset e.val e.property ha))
  obtain ⟨g,hg,hbg,heg⟩ := exists_other_incident_edge e.property hb
    (h2 b (H.edge_subset e.val e.property hb))
  have hfg : f≠g := by
    intro hfg
    subst g
    have hcard := hl e.val e.property f hf hef
    have htwo : 1 < (e.val∩f).card := Finset.one_lt_card.mpr
      ⟨a,Finset.mem_inter.mpr ⟨ha,haf⟩,b,Finset.mem_inter.mpr ⟨hb,hbg⟩,hab⟩
    omega
  refine ⟨⟨f,hf⟩,⟨g,hg⟩,?_,?_,?_⟩
  · exact ⟨fun h => hef (congrArg Subtype.val h),a,Finset.mem_inter.mpr ⟨ha,haf⟩⟩
  · exact ⟨fun h => heg (congrArg Subtype.val h),b,Finset.mem_inter.mpr ⟨hb,hbg⟩⟩
  · exact fun h => hfg (congrArg Subtype.val h)

private theorem cyclic_of_two_neighbors {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V)
    (hN : ∀ x,∃ y z,G.Adj x y ∧ G.Adj x z ∧ y≠z) : ¬G.IsAcyclic := by
  classical
  intro hacyc
  obtain ⟨u,v,p,hp,hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hall : ∀ w,G.Adj u w → w=p.snd := by
    intro w hw
    have hwmem : w∈p.support := by
      by_contra hn
      have hpath := hp.cons (h:=hw.symm) hn
      have hlen := hmax w v (p.cons hw.symm) hpath
      simp only [SimpleGraph.Walk.length_cons] at hlen
      omega
    exact hacyc.eq_snd_of_adj_start hp hw hwmem
  obtain ⟨y,z,hy,hz,hne⟩ := hN u
  exact hne ((hall y hy).trans (hall z hz).symm)

/-- There is a globally shortest cycle in the simple dual graph of every
nonempty finite linear 3-uniform 2-regular hypergraph. -/
theorem dualGraph_shortest_cycle {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) (hl : H.Linear)
    (h2 : ∀ x∈H.vertices,H.degree x=2) (hne : H.edges.Nonempty) :
    ∃ (a : ↥H.edges) (w : H.dualGraph.Walk a a),
      w.IsCycle ∧ H.dualGraph.egirth=w.length := by
  classical
  letI : Nonempty ↥H.edges := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  exact SimpleGraph.exists_egirth_eq_length.mpr
    (cyclic_of_two_neighbors H.dualGraph (dualGraph_two_neighbors h3 hl h2))

/-- The incidence dual viewed as a finite graph whose edges are two-element
sets of original hyperedges. The degree-two assumption excludes isolated labels. -/
def dualIncidence (H : FiniteHypergraph α)
    (h2 : ∀ x∈H.vertices,H.degree x=2) : FiniteHypergraph (Finset α) where
  vertices := H.edges
  edges := H.vertices.image H.incidentEdges
  edge_subset := by
    intro p hp e he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp he).1
  edge_nonempty := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.card_pos.mp (by change 0<H.degree x; rw[h2 x hx]; omega)

/-- In the linear two-regular case, different original vertices yield distinct
pairs of incident hyperedges. -/
theorem incidentEdges_injective_on {H : FiniteHypergraph α}
    (hl : H.Linear) (h2 : ∀ x∈H.vertices,H.degree x=2) :
    Set.InjOn H.incidentEdges H.vertices := by
  intro x hx y hy heq
  by_contra hxy
  have hcard : (H.incidentEdges x).card=2 := h2 x hx
  obtain ⟨e,he,f,hf,hef⟩ := Finset.one_lt_card.mp (show 1<(H.incidentEdges x).card by omega)
  have hey : e∈H.incidentEdges y := by rw[←heq]; exact he
  have hfy : f∈H.incidentEdges y := by rw[←heq]; exact hf
  obtain ⟨heH,hxe⟩ := Finset.mem_filter.mp he
  obtain ⟨hfH,hxf⟩ := Finset.mem_filter.mp hf
  have hye := (Finset.mem_filter.mp hey).2
  have hyf := (Finset.mem_filter.mp hfy).2
  have hsmall := hl e heH f hfH hef
  have hlarge : 1<(e∩f).card := Finset.one_lt_card.mpr
    ⟨x,Finset.mem_inter.mpr ⟨hxe,hxf⟩,y,Finset.mem_inter.mpr ⟨hye,hyf⟩,hxy⟩
  omega

@[simp] theorem dualIncidence_vertices (H : FiniteHypergraph α)
    (h2 : ∀ x∈H.vertices,H.degree x=2) : (H.dualIncidence h2).vertices=H.edges := rfl

@[simp] theorem dualIncidence_edges (H : FiniteHypergraph α)
    (h2 : ∀ x∈H.vertices,H.degree x=2) :
    (H.dualIncidence h2).edges=H.vertices.image H.incidentEdges := rfl

theorem dualIncidence_edges_card {H : FiniteHypergraph α}
    (hl : H.Linear) (h2 : ∀ x∈H.vertices,H.degree x=2) :
    (H.dualIncidence h2).edges.card=H.vertices.card := by
  exact Finset.card_image_iff.mpr (incidentEdges_injective_on hl h2)

theorem dualIncidence_two_uniform {H : FiniteHypergraph α}
    (h2 : ∀ x∈H.vertices,H.degree x=2) :
    ∀ e∈(H.dualIncidence h2).edges,e.card=2 := by
  intro e he
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
  exact h2 x hx

/-- The dual edges incident with an original hyperedge are precisely the labels
arising from the vertices of that hyperedge. -/
theorem dualIncidence_incidentEdges {H : FiniteHypergraph α}
    (h2 : ∀ x∈H.vertices,H.degree x=2) {e : Finset α} (he : e∈H.edges) :
    (H.dualIncidence h2).incidentEdges e=e.image H.incidentEdges := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp,hep⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨x,(Finset.mem_filter.mp hep).2,rfl⟩
  · intro hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨x,H.edge_subset e he hx,rfl⟩,
       Finset.mem_filter.mpr ⟨he,hx⟩⟩

theorem dualIncidence_degree_three {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) (hl : H.Linear)
    (h2 : ∀ x∈H.vertices,H.degree x=2) {e : Finset α} (he : e∈H.edges) :
    (H.dualIncidence h2).degree e=3 := by
  unfold degree
  rw[dualIncidence_incidentEdges h2 he]
  rw[Finset.card_image_iff.mpr ((incidentEdges_injective_on hl h2).mono (H.edge_subset e he))]
  exact h3 e he

end SidonPaper.FiniteHypergraph
