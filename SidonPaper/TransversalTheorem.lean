module

public import SidonPaper.TransversalDualPacking

@[expose] public section


namespace SidonPaper.FiniteHypergraph
variable {α : Type*} [DecidableEq α]

/-- The remaining linear two-regular case of the Chvátal–McDiarmid bound,
proved by maximum matching in its simple incidence dual. -/
theorem transversal_four_linear_two_regular {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) (hl : H.Linear)
    (h2 : ∀ x ∈ H.vertices, H.degree x = 2) :
    4 * H.tau ≤ H.vertices.card + H.edges.card := by
  obtain ⟨M,hM,hsize⟩ := exists_matching_quarter (H.dualIncidence h2)
    (dualIncidence_two_uniform h2) (by
      intro e he
      exact le_of_eq (dualIncidence_degree_three h3 hl h2 he))
  exact transversal_four_of_dual_matching h3 hl h2 hM hsize

omit [DecidableEq α] in
/-- Source Theorem4.6: the full finite three-uniform transversal bound.
No external combinatorial theorem is assumed. -/
theorem transversal_four {H : FiniteHypergraph α} (h3 : H.ThreeUniform) :
    4 * H.tau ≤ H.vertices.card + H.edges.card := by
  classical
  by_contra hn
  obtain ⟨K,hK3,hKlin,hKreg,hKbad,hKcard⟩ :=
    counterexample_has_linear_two_regular h3 (by omega)
  have hb := transversal_four_linear_two_regular hK3 hKlin hKreg
  omega

end SidonPaper.FiniteHypergraph
