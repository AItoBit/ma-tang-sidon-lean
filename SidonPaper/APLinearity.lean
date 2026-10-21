module

public import SidonPaper.Relations

@[expose] public section


namespace SidonPaper

noncomputable def apVertices (p : ℝ × ℝ × ℝ) : Finset ℝ := {p.1,p.2.1,p.2.2}

private theorem cardinal_four {a b c d : ℝ} (hab : a<b) (hbc : b<c) (hcd : c<d) :
    ({a,b,c,d} : Finset ℝ).card = 4 := by
  classical
  simp [ne_of_lt hab,ne_of_lt hbc,ne_of_lt hcd,ne_of_lt (lt_trans hab hbc),
    ne_of_lt (lt_trans hbc hcd),ne_of_lt (lt_trans hab (lt_trans hbc hcd))]

private theorem no_bad_four {A : Finset ℝ} (h : IsFourFive A)
    {a b c d : ℝ} (ha : a∈A) (hb : b∈A) (hc : c∈A) (hd : d∈A)
    (hab : a<b) (hbc : b<c) (hcd : c<d)
    (hsmall : (differences {a,b,c,d}).card ≤ 4) : False := by
  have hsub : ({a,b,c,d} : Finset ℝ) ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> assumption
  have hl := h _ hsub (cardinal_four hab hbc hcd)
  omega

private theorem halfAP_small {a b c d : ℝ} (hab : a<b) (hbc : b<c) (hcd : c<d)
    (h1 : a+d=b+b) (h2 : b+d=c+c) : (differences {a,b,c,d}).card ≤ 4 := by
  classical
  have he1 : d-b=b-a := by linarith
  have he2 : d-c=c-b := by linarith
  have hsub : differences {a,b,c,d} ⊆ {b-a,c-a,d-a,c-b} := by
    intro z hz
    obtain ⟨⟨x,y⟩,hp,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy ⊢
    rcases hx with hx|hx|hx|hx <;> rcases hy with hy|hy|hy|hy <;>
      subst x <;> subst y <;> simp_all
    all_goals linarith
  refine (Finset.card_le_card hsub).trans ?_
  simp only [Finset.card_insert_eq_ite,Finset.card_singleton]
  split_ifs <;> omega

private theorem reflected_halfAP_small {a b c d : ℝ} (hab : a<b) (hbc : b<c) (hcd : c<d)
    (h1 : a+c=b+b) (h2 : a+d=c+c) : (differences {a,b,c,d}).card ≤ 4 := by
  classical
  have he1 : c-b=b-a := by linarith
  have he2 : d-c=c-a := by linarith
  have hsub : differences {a,b,c,d} ⊆ {b-a,c-a,d-a,d-b} := by
    intro z hz
    obtain ⟨⟨x,y⟩,hp,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy ⊢
    rcases hx with hx|hx|hx|hx <;> rcases hy with hy|hy|hy|hy <;>
      subst x <;> subst y <;> simp_all
    all_goals linarith
  refine (Finset.card_le_card hsub).trans ?_
  simp only [Finset.card_insert_eq_ite,Finset.card_singleton]
  split_ifs <;> omega

private theorem pair_positions {a b c u v : ℝ} (hab : a<b) (hbc : b<c)
    (hu : u∈({a,b,c} : Finset ℝ)) (hv : v∈({a,b,c} : Finset ℝ)) (huv : u<v) :
    (u=a ∧ v=b) ∨ (u=a ∧ v=c) ∨ (u=b ∧ v=c) := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with hu|hu|hu <;> rcases hv with hv|hv|hv <;>
    subst u <;> subst v <;> try simp_all
  all_goals linarith

/-- Lemma2.5, in the canonical sorted-triple representation. -/
theorem apEdges_linear {A : Finset ℝ} (h : IsFourFive A)
    {p q : ℝ × ℝ × ℝ} (hp : p∈apEdges A) (hq : q∈apEdges A) (hpq : p≠q) :
    (apVertices p ∩ apVertices q).card ≤ 1 := by
  classical
  by_contra hn
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp (show 1 < (apVertices p ∩ apVertices q).card by omega)
  have hchoose (u v : ℝ) (hu : u ∈ apVertices p ∩ apVertices q)
      (hv : v ∈ apVertices p ∩ apVertices q) (huv : u<v) : False := by
    obtain ⟨a,b,c⟩ := p
    obtain ⟨d,e,f⟩ := q
    obtain ⟨hpA,hab,hbc,hAP⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqA,hde,hef,hAQ⟩ := Finset.mem_filter.mp hq
    obtain ⟨ha,hbcA⟩ := Finset.mem_product.mp hpA
    obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbcA
    obtain ⟨hd,hefA⟩ := Finset.mem_product.mp hqA
    obtain ⟨he,hf⟩ := Finset.mem_product.mp hefA
    simp only [Prod.fst,Prod.snd] at *
    have hposp := pair_positions hab hbc (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hv).1 huv
    have hposq := pair_positions hde hef (Finset.mem_inter.mp hu).2 (Finset.mem_inter.mp hv).2 huv
    rcases hposp with ⟨hua,hvb⟩|⟨hua,hvc⟩|⟨hub,hvc⟩ <;>
      rcases hposq with ⟨hud,hve⟩|⟨hud,hvf⟩|⟨hue,hvf⟩
    · apply hpq
      exact Prod.ext (by linarith) (Prod.ext (by linarith) (by linarith))
    · exact no_bad_four h ha he hb hc (by linarith) (by linarith) hbc
        (reflected_halfAP_small (by linarith) (by linarith) hbc (by linarith) hAP)
    · have hw := h.weakSidon hd hc ha hb (by linarith) hab (by linarith)
      linarith [hw.1]
    · exact no_bad_four h ha hb hc hf hab hbc (by linarith)
        (reflected_halfAP_small hab hbc (by linarith) hAP (by linarith))
    · apply hpq
      exact Prod.ext (by linarith) (Prod.ext (by linarith) (by linarith))
    · exact no_bad_four h hd ha hb hc (by linarith) hab hbc
        (halfAP_small (by linarith) hab hbc (by linarith) hAP)
    · have hw := h.weakSidon ha hf hb hc (by linarith) hbc (by linarith)
      linarith [hw.1]
    · exact no_bad_four h ha hb he hc hab (by linarith) (by linarith)
        (halfAP_small hab (by linarith) (by linarith) hAP (by linarith))
    · apply hpq
      exact Prod.ext (by linarith) (Prod.ext (by linarith) (by linarith))
  rcases lt_or_gt_of_ne huv with huv|hvu
  · exact hchoose u v hu hv huv
  · exact hchoose v u hv hu hvu

end SidonPaper
