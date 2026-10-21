module

public import SidonPaper.TransversalCycle
public import SidonPaper.TransversalLowDegree
public import SidonPaper.TransversalPacking

@[expose] public section


namespace SidonPaper.FiniteHypergraph
variable {α : Type*} [DecidableEq α]

/-- The edges touched by a vertex selection are the union of its incidence sets. -/
theorem removedEdges_eq_biUnion (H : FiniteHypergraph α) (P : Finset α) :
    H.removedEdges P=P.biUnion H.incidentEdges := by
  ext e
  constructor
  · intro he
    obtain ⟨he,hd⟩ := Finset.mem_filter.mp he
    obtain ⟨x,hxe,hxP⟩ := Finset.not_disjoint_iff.mp hd
    exact Finset.mem_biUnion.mpr ⟨x,hxP,Finset.mem_filter.mpr ⟨he,hxe⟩⟩
  · intro he
    obtain ⟨x,hxP,hxe⟩ := Finset.mem_biUnion.mp he
    obtain ⟨he,hxe⟩ := Finset.mem_filter.mp hxe
    exact Finset.mem_filter.mpr ⟨he,Finset.not_disjoint_iff.mpr ⟨x,hxe,hxP⟩⟩

/-- A matching of the incidence dual pulls back to equally many original
vertices whose incident edge pairs are disjoint. -/
theorem dualMatching_pullback {H : FiniteHypergraph α}
    (hl : H.Linear) (h2 : ∀ x∈H.vertices,H.degree x=2)
    {M : Finset (Finset (Finset α))} (hM : (H.dualIncidence h2).EdgeMatching M) :
    ∃ P : Finset α, P⊆H.vertices ∧ P.image H.incidentEdges=M ∧
      P.card=M.card ∧ (H.removedEdges P).card=2*P.card := by
  classical
  obtain ⟨P,hP,hPM⟩ := Finset.subset_image_iff.mp hM.1
  have hcard : P.card=M.card := by
    rw[←hPM]
    exact (Finset.card_image_iff.mpr ((incidentEdges_injective_on hl h2).mono hP)).symm
  have heq : H.removedEdges P=M.biUnion id := by
    rw[removedEdges_eq_biUnion,←hPM]
    exact (Finset.image_biUnion (s:=P) (t:=id) (f:=H.incidentEdges)).symm
  refine ⟨P,hP,hPM,hcard,?_⟩
  calc
    (H.removedEdges P).card=(M.biUnion id).card := congrArg Finset.card heq
    _=∑ e∈M,e.card := Finset.card_biUnion (by
      intro e he f hf hne
      exact hM.2 e he f hf hne)
    _=∑ e∈M,2 := Finset.sum_congr rfl (fun e he => dualIncidence_two_uniform h2 e (hM.1 he))
    _=2*P.card := by simp [hcard,Nat.mul_comm]

/-- The generic graph matching estimate supplies the exact hypergraph bound
in the linear two-regular case, once a matching with the needed size is given. -/
theorem transversal_four_of_dual_matching {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) (hl : H.Linear) (h2 : ∀ x∈H.vertices,H.degree x=2)
    {M : Finset (Finset (Finset α))} (hM : (H.dualIncidence h2).EdgeMatching M)
    (hsize : (H.dualIncidence h2).edges.card≤4*M.card) :
    4*H.tau≤H.vertices.card+H.edges.card := by
  obtain ⟨P,hP,hPM,hcard,hdouble⟩ := dualMatching_pullback hl h2 hM
  apply transversal_four_of_double_coverage h3 h2 hP hdouble
  rw[hcard,←dualIncidence_edges_card hl h2]
  exact hsize

end SidonPaper.FiniteHypergraph
