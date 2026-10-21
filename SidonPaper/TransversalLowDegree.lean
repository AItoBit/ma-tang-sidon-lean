module

public import SidonPaper.TransversalReduction
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section


namespace SidonPaper.FiniteHypergraph
variable {α : Type*}

/-- A finite matching represented by its two-element edges. -/
def EdgeMatching (H : FiniteHypergraph α) (M : Finset (Finset α)) : Prop :=
  M ⊆ H.edges ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

def matchingSupport [DecidableEq α] (M : Finset (Finset α)) : Finset α := M.biUnion id

theorem mem_matchingSupport [DecidableEq α] {M : Finset (Finset α)} {x : α} :
    x ∈ matchingSupport M ↔ ∃ e ∈ M, x ∈ e := by
  simp [matchingSupport]

/-- Every finite graph has an edge matching of maximum cardinality. -/
theorem exists_maximum_edgeMatching (H : FiniteHypergraph α) :
    ∃ M : Finset (Finset α), H.EdgeMatching M ∧
      ∀ N : Finset (Finset α), H.EdgeMatching N → N.card ≤ M.card := by
  classical
  let F := H.edges.powerset.filter (fun M => H.EdgeMatching M)
  have he : (∅ : Finset (Finset α)) ∈ F := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
      ⟨Finset.empty_subset _,by simp⟩⟩
  obtain ⟨M,hM,hm⟩ := Finset.exists_mem_eq_sup F ⟨∅,he⟩ Finset.card
  refine ⟨M,(Finset.mem_filter.mp hM).2,?_⟩
  intro N hN
  have hNF : N ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hN.1,hN⟩
  rw [← hm]
  exact Finset.le_sup hNF

/-- A maximum matching has no unused edge disjoint from its support. -/
theorem maximum_matching_hits_edges [DecidableEq α] {H : FiniteHypergraph α} {M : Finset (Finset α)}
    (hM : H.EdgeMatching M)
    (hmax : ∀ N : Finset (Finset α), H.EdgeMatching N → N.card ≤ M.card)
    {e : Finset α} (he : e ∈ H.edges) : ¬ Disjoint e (matchingSupport M) := by
  classical
  intro hdis
  have heM : e ∉ M := by
    intro heM
    obtain ⟨x,hxe⟩ := H.edge_nonempty e he
    exact (Finset.disjoint_left.mp hdis hxe)
      (mem_matchingSupport.mpr ⟨e,heM,hxe⟩)
  have hnew : H.EdgeMatching (insert e M) := by
    constructor
    · exact Finset.insert_subset he hM.1
    · intro f hf g hg hfg
      simp only [Finset.mem_insert] at hf hg
      rcases hf with rfl|hf <;> rcases hg with rfl|hg
      · exact False.elim (hfg rfl)
      · apply Finset.disjoint_left.mpr
        intro x hxe hxg
        exact Finset.disjoint_left.mp hdis hxe
          (mem_matchingSupport.mpr ⟨g,hg,hxg⟩)
      · apply Disjoint.symm
        apply Finset.disjoint_left.mpr
        intro x hxe hxf
        exact Finset.disjoint_left.mp hdis hxe
          (mem_matchingSupport.mpr ⟨f,hf,hxf⟩)
      · exact hM.2 f hf g hg hfg
  have hh := hmax _ hnew
  rw [Finset.card_insert_of_notMem heM] at hh
  omega

/-- The two-edge exchange which excludes an augmenting path of length three. -/
theorem maximum_matching_no_three_augment [DecidableEq α] {H : FiniteHypergraph α}
    {M : Finset (Finset α)} (hM : H.EdgeMatching M)
    (hmax : ∀ N : Finset (Finset α), H.EdgeMatching N → N.card ≤ M.card)
    {u v x y : α} (huv : u ≠ v) (hxy : x ≠ y)
    (heM : ({u,v} : Finset α) ∈ M)
    (hx : x ∉ matchingSupport M) (hy : y ∉ matchingSupport M)
    (hux : ({u,x} : Finset α) ∈ H.edges)
    (hvy : ({v,y} : Finset α) ∈ H.edges) : False := by
  classical
  let e : Finset α := {u,v}
  let f : Finset α := {u,x}
  let g : Finset α := {v,y}
  have huC : u ∈ matchingSupport M := mem_matchingSupport.mpr ⟨e,heM,by simp [e]⟩
  have hvC : v ∈ matchingSupport M := mem_matchingSupport.mpr ⟨e,heM,by simp [e]⟩
  have hxu : x ≠ u := by intro h; exact hx (h.symm ▸ huC)
  have hxv : x ≠ v := by intro h; exact hx (h.symm ▸ hvC)
  have hyu : y ≠ u := by intro h; exact hy (h.symm ▸ huC)
  have hyv : y ≠ v := by intro h; exact hy (h.symm ▸ hvC)
  have hfM : f ∉ M := by
    intro hfM
    exact hx (mem_matchingSupport.mpr ⟨f,hfM,by simp [f]⟩)
  have hgM : g ∉ M := by
    intro hgM
    exact hy (mem_matchingSupport.mpr ⟨g,hgM,by simp [g]⟩)
  have hfg : f ≠ g := by
    intro hh
    have hxg : x ∈ g := hh ▸ (by simp [f] : x ∈ f)
    simp [g,hxv,hxy] at hxg
  have hdfg : Disjoint f g := by
    simp [f,g,Ne.symm huv,hyu,Ne.symm hxv,Ne.symm hxy]
  have hfdis : ∀ k ∈ M.erase e, Disjoint f k := by
    intro k hk
    obtain ⟨hke,hkM⟩ := Finset.mem_erase.mp hk
    have hek := hM.2 e heM k hkM (Ne.symm hke)
    apply Finset.disjoint_left.mpr
    intro z hzf hzk
    simp only [f,Finset.mem_insert,Finset.mem_singleton] at hzf
    rcases hzf with rfl|rfl
    · exact Finset.disjoint_left.mp hek (by simp [e]) hzk
    · exact hx (mem_matchingSupport.mpr ⟨k,hkM,hzk⟩)
  have hgdis : ∀ k ∈ M.erase e, Disjoint g k := by
    intro k hk
    obtain ⟨hke,hkM⟩ := Finset.mem_erase.mp hk
    have hek := hM.2 e heM k hkM (Ne.symm hke)
    apply Finset.disjoint_left.mpr
    intro z hzg hzk
    simp only [g,Finset.mem_insert,Finset.mem_singleton] at hzg
    rcases hzg with rfl|rfl
    · exact Finset.disjoint_left.mp hek (by simp [e]) hzk
    · exact hy (mem_matchingSupport.mpr ⟨k,hkM,hzk⟩)
  have hN : H.EdgeMatching (insert f (insert g (M.erase e))) := by
    constructor
    · exact Finset.insert_subset hux (Finset.insert_subset hvy ((Finset.erase_subset (a:=e) (s:=M)).trans hM.1))
    · intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl|rfl|ha <;> rcases hb with rfl|rfl|hb
      · exact False.elim (hab rfl)
      · exact hdfg
      · exact hfdis _ hb
      · exact hdfg.symm
      · exact False.elim (hab rfl)
      · exact hgdis _ hb
      · exact (hfdis _ ha).symm
      · exact (hgdis _ ha).symm
      · exact hM.2 a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
  have hnewCard := hmax _ hN
  have hgn : g ∉ M.erase e := fun h => hgM (Finset.mem_of_mem_erase h)
  have hfn : f ∉ insert g (M.erase e) := by simp [hfg,hfM]
  rw [Finset.card_insert_of_notMem hfn,Finset.card_insert_of_notMem hgn,
    Finset.card_erase_of_mem heM] at hnewCard
  have hpos : 0 < M.card := Finset.card_pos.mpr ⟨e,heM⟩
  omega

open scoped BigOperators

noncomputable def outsideNeighbors [DecidableEq α] (H : FiniteHypergraph α)
    (M : Finset (Finset α)) (u : α) : Finset α := by
  classical
  exact H.vertices.filter (fun x => x ∉ matchingSupport M ∧ ({u,x}:Finset α) ∈ H.edges)

/-- At a matched vertex of a subcubic graph, at most two neighbours are unmatched. -/
theorem outsideNeighbors_card_le_two [DecidableEq α] {H : FiniteHypergraph α}
    {M : Finset (Finset α)} (hM : H.EdgeMatching M)
    (hdeg : ∀ x ∈ H.vertices, H.degree x ≤ 3)
    {u v : α} (huv : u ≠ v) (heM : ({u,v}:Finset α) ∈ M) :
    (H.outsideNeighbors M u).card ≤ 2 := by
  classical
  have huC : u ∈ matchingSupport M := mem_matchingSupport.mpr ⟨{u,v},heM,by simp⟩
  have huV : u ∈ H.vertices := H.edge_subset _ (hM.1 heM) (by simp)
  have heInc : ({u,v}:Finset α) ∈ H.incidentEdges u :=
    Finset.mem_filter.mpr ⟨hM.1 heM,by simp⟩
  have hcount : (H.outsideNeighbors M u).card ≤
      ((H.incidentEdges u).erase {u,v}).card := by
    apply Finset.card_le_card_of_injOn (fun x => ({u,x}:Finset α))
    · intro x hx
      obtain ⟨hxV,hxC,hxe⟩ := Finset.mem_filter.mp hx
      have hxv : x ≠ v := by
        intro h
        subst x
        exact hxC (mem_matchingSupport.mpr ⟨{u,v},heM,by simp⟩)
      apply Finset.mem_erase.mpr
      refine ⟨?_,Finset.mem_filter.mpr ⟨hxe,by simp⟩⟩
      intro heq
      have : x ∈ ({u,v}:Finset α) := heq ▸ (by simp : x ∈ ({u,x}:Finset α))
      simp only [Finset.mem_insert,Finset.mem_singleton] at this
      rcases this with rfl|rfl
      · exact hxC huC
      · exact hxv rfl
    · intro x hx y hy hxy
      have hxC := (Finset.mem_filter.mp hx).2.1
      have hxu : x ≠ u := by intro heq; subst x; exact hxC huC
      change ({u,x}:Finset α) = {u,y} at hxy
      have hmem : x ∈ ({u,y}:Finset α) := by rw [← hxy]; simp
      simpa [hxu] using hmem
  rw [Finset.card_erase_of_mem heInc] at hcount
  have hd := hdeg u huV
  change (H.incidentEdges u).card ≤ 3 at hd
  omega

/-- At both ends of a matching edge, the total unmatched neighbourhood has at most two entries. -/
theorem outsideNeighbors_pair_card_le_two [DecidableEq α] {H : FiniteHypergraph α}
    {M : Finset (Finset α)} (hM : H.EdgeMatching M)
    (hmax : ∀ N : Finset (Finset α), H.EdgeMatching N → N.card ≤ M.card)
    (hdeg : ∀ x ∈ H.vertices, H.degree x ≤ 3)
    {u v : α} (huv : u ≠ v) (heM : ({u,v}:Finset α) ∈ M) :
    (H.outsideNeighbors M u).card + (H.outsideNeighbors M v).card ≤ 2 := by
  classical
  have hswap : ({v,u}:Finset α) ∈ M := by simpa [Finset.pair_comm] using heM
  by_cases hu : (H.outsideNeighbors M u).Nonempty
  · by_cases hv : (H.outsideNeighbors M v).Nonempty
    · obtain ⟨x,hx⟩ := hu
      obtain ⟨y,hy⟩ := hv
      have hsame : ∀ a ∈ H.outsideNeighbors M u, ∀ b ∈ H.outsideNeighbors M v, a=b := by
        intro a ha b hb
        by_contra hab
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        exact maximum_matching_no_three_augment hM hmax huv hab heM ha'.1 hb'.1 ha'.2 hb'.2
      have huc : (H.outsideNeighbors M u).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact (hsame a ha y hy).trans (hsame b hb y hy).symm
      have hvc : (H.outsideNeighbors M v).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact (hsame x hx a ha).symm.trans (hsame x hx b hb)
      omega
    · have hzero : H.outsideNeighbors M v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hv
      simpa [hzero] using outsideNeighbors_card_le_two hM hdeg huv heM
  · have hzero : H.outsideNeighbors M u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu
    simpa [hzero] using outsideNeighbors_card_le_two hM hdeg (Ne.symm huv) hswap

noncomputable def crossEdges [DecidableEq α] (H : FiniteHypergraph α)
    (M : Finset (Finset α)) (e : Finset α) : Finset (Finset α) := by
  classical
  exact H.edges.filter (fun f => ¬ Disjoint f e ∧ ¬ f ⊆ matchingSupport M)

/-- Every matching edge meets at most two edges that also contain an unmatched vertex. -/
theorem crossEdges_card_le_two [DecidableEq α] {H : FiniteHypergraph α}
    {M : Finset (Finset α)} (hM : H.EdgeMatching M)
    (hmax : ∀ N : Finset (Finset α), H.EdgeMatching N → N.card ≤ M.card)
    (h2 : ∀ e∈H.edges,e.card=2)
    (hdeg : ∀ x ∈ H.vertices,H.degree x ≤ 3)
    {e : Finset α} (heM : e∈M) : (H.crossEdges M e).card ≤ 2 := by
  classical
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp (h2 _ (hM.1 heM))
  have hsub : H.crossEdges M {u,v} ⊆
      ((H.outsideNeighbors M u).image (fun x => ({u,x}:Finset α))) ∪
      ((H.outsideNeighbors M v).image (fun x => ({v,x}:Finset α))) := by
    intro f hf
    obtain ⟨hfE,hfInter,hfN⟩ := Finset.mem_filter.mp hf
    obtain ⟨x,hxf,hxC⟩ := Finset.not_subset.mp hfN
    obtain ⟨z,hzf,hzu⟩ := Finset.not_disjoint_iff.mp hfInter
    have hzu : z=u ∨ z=v := by simpa using hzu
    obtain ⟨a,b,hab,hfab⟩ := Finset.card_eq_two.mp (h2 _ hfE)
    have hxz : x ≠ z := by
      intro h
      have hzC : z ∈ matchingSupport M := mem_matchingSupport.mpr ⟨{u,v},heM,by simpa using hzu⟩
      exact hxC (h.symm ▸ hzC)
    have hfxz : f = {z,x} := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        have hwab : w=a ∨ w=b := by simpa [hfab] using hw
        have hxab : x=a ∨ x=b := by simpa [hfab] using hxf
        have hzab : z=a ∨ z=b := by simpa [hfab] using hzf
        simp only [Finset.mem_insert,Finset.mem_singleton]
        rcases hwab with rfl|rfl <;> rcases hxab with rfl|rfl <;>
          rcases hzab with rfl|rfl <;> simp_all
      · rw [h2 _ hfE]
        simp [Ne.symm hxz]
    have hxV : x ∈ H.vertices := H.edge_subset _ hfE hxf
    rcases hzu with rfl|rfl
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨x,Finset.mem_filter.mpr ⟨hxV,hxC,?_⟩,hfxz.symm⟩
      rwa [← hfxz]
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨x,Finset.mem_filter.mpr ⟨hxV,hxC,?_⟩,hfxz.symm⟩
      rwa [← hfxz]
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_image_le (s:=H.outsideNeighbors M u) (f:=fun x => ({u,x}:Finset α))
  have hv := Finset.card_image_le (s:=H.outsideNeighbors M v) (f:=fun x => ({v,x}:Finset α))
  have hunion := Finset.card_union_le
    ((H.outsideNeighbors M u).image (fun x => ({u,x}:Finset α)))
    ((H.outsideNeighbors M v).image (fun x => ({v,x}:Finset α)))
  have hpair := outsideNeighbors_pair_card_le_two hM hmax hdeg huv heM
  omega

/-- The support of a matching has twice as many vertices as matching edges. -/
theorem matchingSupport_card [DecidableEq α] {H : FiniteHypergraph α}
    {M : Finset (Finset α)} (hM : H.EdgeMatching M)
    (h2 : ∀ e∈H.edges,e.card=2) : (matchingSupport M).card = 2 * M.card := by
  classical
  unfold matchingSupport
  rw [Finset.card_biUnion]
  · change (∑ u∈M,u.card) = 2*M.card
    have he : ∀ e∈M,e.card=2 := fun e he => h2 e (hM.1 he)
    rw [Finset.sum_const_nat he]
    omega
  · intro e he f hf hne
    exact hM.2 e he f hf hne

noncomputable def externalEdges [DecidableEq α] (H : FiniteHypergraph α)
    (M : Finset (Finset α)) : Finset (Finset α) := by
  classical
  exact H.edges.filter (fun e => ¬e ⊆ matchingSupport M)

/-- At most two external edges may be charged to any edge of a maximum matching. -/
theorem externalEdges_card_le [DecidableEq α] {H : FiniteHypergraph α}
    {M : Finset (Finset α)} (hM : H.EdgeMatching M)
    (hmax : ∀ N : Finset (Finset α), H.EdgeMatching N → N.card ≤ M.card)
    (h2 : ∀ e∈H.edges,e.card=2)
    (hdeg : ∀ x∈H.vertices,H.degree x≤3) : (H.externalEdges M).card ≤ 2*M.card := by
  classical
  have hsub : H.externalEdges M ⊆ M.biUnion (H.crossEdges M) := by
    intro f hf
    obtain ⟨hfE,hfN⟩ := Finset.mem_filter.mp hf
    have hh := maximum_matching_hits_edges hM hmax hfE
    obtain ⟨x,hxf,hxC⟩ := Finset.not_disjoint_iff.mp hh
    obtain ⟨e,he,hxe⟩ := mem_matchingSupport.mp hxC
    exact Finset.mem_biUnion.mpr ⟨e,he,Finset.mem_filter.mpr
      ⟨hfE,Finset.not_disjoint_iff.mpr ⟨x,hxf,hxe⟩,hfN⟩⟩
  calc
    (H.externalEdges M).card ≤ (M.biUnion (H.crossEdges M)).card := Finset.card_le_card hsub
    _ ≤ ∑ e∈M,(H.crossEdges M e).card := Finset.card_biUnion_le
    _ ≤ ∑ _∈M,2 := Finset.sum_le_sum (fun e he => crossEdges_card_le_two hM hmax h2 hdeg he)
    _ = 2*M.card := by simp [Nat.mul_comm]

/-- A simple subcubic graph has a matching with at least one quarter of its edges.
This elementary matching argument avoids using an unproved edge-colouring theorem. -/
theorem maximum_matching_quarter [DecidableEq α] {H : FiniteHypergraph α}
    {M : Finset (Finset α)} (hM : H.EdgeMatching M)
    (hmax : ∀ N : Finset (Finset α), H.EdgeMatching N → N.card ≤ M.card)
    (h2 : ∀ e∈H.edges,e.card=2)
    (hdeg : ∀ x∈H.vertices,H.degree x≤3) : H.edges.card ≤ 4*M.card := by
  classical
  let C := matchingSupport M
  have hC : C ⊆ H.vertices := by
    intro x hx
    obtain ⟨e,he,hxe⟩ := mem_matchingSupport.mp hx
    exact H.edge_subset _ (hM.1 he) hxe
  have hCcard : C.card = 2*M.card := matchingSupport_card hM h2
  have hsum : (∑ e∈H.edges,(C∩e).card) ≤ C.card*3 := by
    apply Finset.sum_card_inter_le
    intro x hx
    exact hdeg x (hC hx)
  have hcount (e : Finset α) (he : e∈H.edges) :
      (C∩e).card + (if e ⊆ C then 0 else 1) = 2 := by
    by_cases heC : e ⊆ C
    · have hint : C∩e=e := Finset.inter_eq_right.mpr heC
      simp [heC,hint,h2 _ he]
    · have hsd : 0 < (e\C).card := Finset.card_pos.mpr
        (Finset.sdiff_nonempty.mpr heC)
      have hnd := maximum_matching_hits_edges hM hmax he
      have hi : 0 < (e∩C).card := by
        obtain ⟨x,hxe,hxC⟩ := Finset.not_disjoint_iff.mp hnd
        exact Finset.card_pos.mpr ⟨x,Finset.mem_inter.mpr ⟨hxe,hxC⟩⟩
      have heq := Finset.card_sdiff_add_card_inter e C
      rw [h2 _ he] at heq
      rw [Finset.inter_comm C e]
      simp only [ite_eq_right heC]
      omega
  have hsumEq : (∑ e∈H.edges,(C∩e).card) + (H.externalEdges M).card = 2*H.edges.card := by
    have hext : (H.externalEdges M).card = ∑ e∈H.edges,if e ⊆ C then 0 else 1 := by
      simp only [externalEdges,Finset.card_eq_sum_ones,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> rfl
    rw [hext,← Finset.sum_add_distrib]
    rw [Finset.sum_const_nat hcount]
    omega
  have hext := externalEdges_card_le hM hmax h2 hdeg
  rw [hCcard] at hsum
  omega

theorem exists_matching_quarter [DecidableEq α] (H : FiniteHypergraph α)
    (h2 : ∀ e∈H.edges,e.card=2)
    (hdeg : ∀ x∈H.vertices,H.degree x≤3) :
    ∃ M : Finset (Finset α), H.EdgeMatching M ∧ H.edges.card ≤ 4*M.card := by
  obtain ⟨M,hM,hmax⟩ := exists_maximum_edgeMatching H
  exact ⟨M,hM,maximum_matching_quarter hM hmax h2 hdeg⟩

end SidonPaper.FiniteHypergraph
