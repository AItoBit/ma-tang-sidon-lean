module

public import SidonPaper.Construction
public import SidonPaper.ExtremalBasics

@[expose] public section


namespace SidonPaper

noncomputable def natRealImage (S : Finset ℕ) : Finset ℝ := by
  classical
  exact S.image (fun z : ℕ => (z : ℝ))

theorem natRealImage_card (S : Finset ℕ) : (natRealImage S).card = S.card := by
  classical
  exact Finset.card_image_of_injective S Nat.cast_injective

theorem natRealImage_coe (S : Finset ℕ) :
    (natRealImage S : Set ℝ) = ((↑) : ℕ → ℝ) '' (S : Set ℕ) := by
  classical
  simp [natRealImage]

/-- The two listed AP families alone force the upper independence bound. -/
theorem construction_subset_card_bound {n : ℕ} (T : Finset ℕ)
    (hT : T ⊆ construction n)
    (hfirst : ∀ i, i+1<n → X n i ∈ T → X n (i+1) ∈ T → Y n i ∉ T)
    (hsecond : ∀ i, i<n → X n i ∈ T → Y n i ∈ T → Y n (i+1) ∉ T) :
    T.card ≤ n+1 := by
  classical
  let U := (Finset.range n).filter (fun i => X n i ∈ T)
  let V := (Finset.range (n+1)).filter (fun i => Y n i ∈ T)
  let M := Finset.range (n+1) \ V
  let f : ℕ → ℕ := fun i => if Y n i ∈ T then i+1 else i
  have hmemU {i : ℕ} (hi : i ∈ U) : i<n ∧ X n i ∈ T := by
    simpa only [U, Finset.mem_filter, Finset.mem_range] using hi
  have hmemV {i : ℕ} : i ∈ V ↔ i<n+1 ∧ Y n i ∈ T := by
    simp only [V, Finset.mem_filter, Finset.mem_range]
  have hfmem : ∀ i ∈ U, f i ∈ M := by
    intro i hi
    obtain ⟨hin,hXi⟩ := hmemU hi
    apply Finset.mem_sdiff.mpr
    constructor
    · simp only [Finset.mem_range]
      dsimp [f]
      split_ifs <;> omega
    · intro hv
      obtain ⟨hvn,hvY⟩ := hmemV.mp hv
      dsimp [f] at hvY
      split_ifs at hvY with hy
      · exact hsecond i hin hXi hy hvY
      · exact hy hvY
  have hfinj : Set.InjOn f U := by
    intro i hi j hj he
    obtain ⟨hin,hXi⟩ := hmemU hi
    obtain ⟨hjn,hXj⟩ := hmemU hj
    dsimp [f] at he
    by_cases hyi : Y n i ∈ T <;> by_cases hyj : Y n j ∈ T
    · simp only [ite_eq_left hyi,ite_eq_left hyj] at he
      omega
    · simp only [ite_eq_left hyi,ite_eq_right hyj] at he
      have hij : j=i+1 := by omega
      subst j
      exact False.elim (hfirst i hjn hXi hXj hyi)
    · simp only [ite_eq_right hyi,ite_eq_left hyj] at he
      have hij : i=j+1 := by omega
      subst i
      exact False.elim (hfirst j hin hXj hXi hyj)
    · simpa only [ite_eq_right hyi,ite_eq_right hyj] using he
  have hUM : U.card ≤ M.card := by
    calc
      U.card = (U.image f).card := (Finset.card_image_iff.mpr hfinj).symm
      _ ≤ M.card := Finset.card_le_card (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
        exact hfmem i hi)
  have hVsub : V ⊆ Finset.range (n+1) := Finset.filter_subset _ _
  have hM : M.card + V.card = n+1 := by
    dsimp [M]
    rw [Finset.card_sdiff_add_card_eq_card hVsub, Finset.card_range]
  have hEq : T = U.image (X n) ∪ V.image (Y n) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp (hT hx) with hxX | hxY
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hxX
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨i,Finset.mem_filter.mpr ⟨hi,hx⟩,rfl⟩)
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hxY
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨i,Finset.mem_filter.mpr ⟨hi,hx⟩,rfl⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxX | hxY
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hxX
        exact (hmemU hi).2
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hxY
        exact (hmemV.mp hi).2
  have hcard : T.card ≤ U.card+V.card := by
    rw [hEq]
    calc
      _ ≤ (U.image (X n)).card + (V.image (Y n)).card := Finset.card_union_le _ _
      _ = U.card + V.card := by
        rw [Finset.card_image_of_injective _ (X_injective n),
          Finset.card_image_of_injective _ (Y_injective n)]
  omega

/-- A Sidon subset avoids both listed AP families. -/
theorem construction_sidon_card_bound {n : ℕ} (T : Finset ℕ)
    (hT : T ⊆ construction n) (hS : IsSidon (natRealImage T : Set ℝ)) :
    T.card ≤ n+1 := by
  have hf : IsAPFree (((↑) : ℕ → ℝ) '' (T : Set ℕ)) := by
    rw [← natRealImage_coe]
    exact hS.apFree
  apply construction_subset_card_bound T hT
  · intro i hi hXi hXnext hYi
    have ho := construction_ap_first_order (show i<n by omega)
    have he := construction_ap_first (show i<n by omega)
    apply hf ⟨X n i,hXi,rfl⟩ ⟨X n (i+1),hXnext,rfl⟩ ⟨Y n i,hYi,rfl⟩
    · exact_mod_cast ho.1
    · exact_mod_cast ho.2
    · exact_mod_cast (show X n i + Y n i = X n (i+1)+X n (i+1) by omega)
  · intro i hi hXi hYi hYnext
    have ho := construction_ap_second_order hi
    have he := construction_ap_second hi
    apply hf ⟨X n i,hXi,rfl⟩ ⟨Y n i,hYi,rfl⟩ ⟨Y n (i+1),hYnext,rfl⟩
    · exact_mod_cast ho.1
    · exact_mod_cast ho.2
    · exact_mod_cast (show X n i+Y n (i+1)=Y n i+Y n i by omega)

def constructionYBlock (n : ℕ) : Finset ℕ :=
  (Finset.range (n+1)).image (Y n)

theorem constructionYBlock_subset (n : ℕ) :
    constructionYBlock n ⊆ construction n := by
  exact Finset.subset_union_right

theorem constructionYBlock_card (n : ℕ) : (constructionYBlock n).card = n+1 := by
  unfold constructionYBlock
  rw [Finset.card_image_of_injective _ (Y_injective n), Finset.card_range]

/-- The entire Y block is Sidon, by the exhaustive AP classification. -/
theorem constructionYBlock_sidon (n : ℕ) :
    IsSidon (natRealImage (constructionYBlock n) : Set ℝ) := by
  rw [natRealImage_coe]
  have hsub : (((↑) : ℕ → ℝ) '' (constructionYBlock n : Set ℕ)) ⊆
      (((↑) : ℕ → ℝ) '' (construction n : Set ℕ)) := by
    rintro x ⟨a,ha,rfl⟩
    exact ⟨a,constructionYBlock_subset n ha,rfl⟩
  apply (sidon_iff_apFree ((construction_weakSidon_real n).mono hsub)).mpr
  intro x y z hx hy hz hxy hyz hs
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨m,hm,rfl⟩ := hy
  obtain ⟨b,hb,rfl⟩ := hz
  have ham : a<m := by exact_mod_cast hxy
  have hmb : m<b := by exact_mod_cast hyz
  have he : a+b=m+m := by exact_mod_cast hs
  have hc := construction_ap_classification
    (constructionYBlock_subset n ha) (constructionYBlock_subset n hm)
    (constructionYBlock_subset n hb) ham hmb he
  obtain ⟨j,hj,hja⟩ := Finset.mem_image.mp ha
  rcases hc with ⟨i,hi,hax,hmx,hby⟩ | ⟨i,hi,hax,hmy,hby⟩
  · exact X_ne_Y n i j (hax.symm.trans hja.symm)
  · exact X_ne_Y n i j (hax.symm.trans hja.symm)

/-- Theorem 4.5, including the harmless parameter cases zero and one. -/
theorem construction_h (n : ℕ) :
    h (natRealImage (construction n)) = n+1 := by
  classical
  apply Nat.le_antisymm
  · unfold h
    apply Finset.sup_le_iff.mpr
    intro B hB
    obtain ⟨hBsub,hBSidon⟩ := Finset.mem_filter.mp hB
    obtain ⟨T,hTsub,hTB⟩ :=
      Finset.subset_image_iff.mp (Finset.mem_powerset.mp hBsub)
    have hBT : B = natRealImage T := hTB.symm
    have hs : IsSidon (natRealImage T : Set ℝ) := by rw [← hBT]; exact hBSidon
    rw [hBT,natRealImage_card]
    exact construction_sidon_card_bound T hTsub hs
  · have hsub : natRealImage (constructionYBlock n) ⊆ natRealImage (construction n) :=
      Finset.image_subset_image (constructionYBlock_subset n)
    have hc := card_le_h hsub (constructionYBlock_sidon n)
    simpa only [natRealImage_card,constructionYBlock_card] using hc

end SidonPaper

#print axioms SidonPaper.construction_h
#print axioms SidonPaper.construction_subset_card_bound
