module

public import SidonPaper.Targets
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Order.Interval.Set.Monotone

@[expose] public section


/-! Algebraic and valuation foundations of Section 4.1 of Ma--Tang v2.
The general weak-Sidon uniqueness proof is not asserted by this module. -/
namespace SidonPaper

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

@[simp] theorem val3_X (n i : ℕ) : padicValNat 3 (X n i) = i := by
  exact padicValNat_mul_pow_right (n - i) i (by decide : 3 ≠ 2)

@[simp] theorem val3_Y (n i : ℕ) : padicValNat 3 (Y n i) = i := by
  exact padicValNat_mul_pow_right (n - i + 1) i (by decide : 3 ≠ 2)

theorem X_pos (n i : ℕ) : 0 < X n i := by
  unfold X
  positivity

theorem Y_pos (n i : ℕ) : 0 < Y n i := by
  unfold Y
  positivity

theorem Y_eq_two_X (n i : ℕ) : Y n i = 2 * X n i := by
  simp only [X, Y, pow_succ]
  ring

theorem X_injective (n : ℕ) : Function.Injective (X n) := by
  intro i j hij
  simpa only [val3_X] using congrArg (padicValNat 3) hij

theorem Y_injective (n : ℕ) : Function.Injective (Y n) := by
  intro i j hij
  simpa only [val3_Y] using congrArg (padicValNat 3) hij

theorem X_ne_Y (n i j : ℕ) : X n i ≠ Y n j := by
  intro h
  have hij : i = j := by
    simpa only [val3_X, val3_Y] using congrArg (padicValNat 3) h
  subst j
  have hp := X_pos n i
  rw [Y_eq_two_X] at h
  omega

theorem construction_blocks_disjoint (n : ℕ) :
    Disjoint ((Finset.range n).image (X n))
      ((Finset.range (n + 1)).image (Y n)) := by
  apply Finset.disjoint_left.mpr
  intro z hzX hzY
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hzX
  obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hzY
  exact X_ne_Y n i j (hix.trans hjy.symm)

/-- The cardinality stated at the start of Section 4.1. -/
theorem construction_card (n : ℕ) : (construction n).card = 2 * n + 1 := by
  unfold construction
  rw [Finset.card_union_of_disjoint (construction_blocks_disjoint n),
    Finset.card_image_of_injective _ (X_injective n),
    Finset.card_image_of_injective _ (Y_injective n)]
  simp only [Finset.card_range]
  omega

theorem X_mem_construction {n i : ℕ} (hi : i < n) : X n i ∈ construction n := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem Y_mem_construction {n i : ℕ} (hi : i ≤ n) : Y n i ∈ construction n := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

theorem construction_pos {n a : ℕ} (ha : a ∈ construction n) : 0 < a := by
  rcases Finset.mem_union.mp ha with hx | hy
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact X_pos n i
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact Y_pos n i

/-- First displayed AP relation used in Lemma 4.4. -/
theorem construction_ap_first {n i : ℕ} (hi : i < n) :
    X n i + Y n i = 2 * X n (i + 1) := by
  have he : n - i = n - (i + 1) + 1 := by omega
  simp only [X, Y, he, pow_succ]
  ring

/-- Second displayed AP relation used in Lemma 4.4. -/
theorem construction_ap_second {n i : ℕ} (hi : i < n) :
    X n i + Y n (i + 1) = 2 * Y n i := by
  have he : n - i = n - (i + 1) + 1 := by omega
  simp only [X, Y, he, pow_succ]
  ring

/-- The first listed AP is nonconstant and ordered as in the source. -/
theorem construction_ap_first_order {n i : ℕ} (hi : i < n) :
    X n i < X n (i + 1) ∧ X n (i + 1) < Y n i := by
  have ha := construction_ap_first hi
  have hy := Y_eq_two_X n i
  have hp := X_pos n i
  constructor <;> omega

/-- The second listed AP is nonconstant and ordered as in the source. -/
theorem construction_ap_second_order {n i : ℕ} (hi : i < n) :
    X n i < Y n i ∧ Y n i < Y n (i + 1) := by
  have ha := construction_ap_second hi
  have hy := Y_eq_two_X n i
  have hp := X_pos n i
  constructor <;> omega

/-- The valuation selects the unique level of an element of the construction. -/
theorem construction_at_valuation {n a i : ℕ} (ha : a ∈ construction n)
    (hv : padicValNat 3 a = i) :
    (i < n ∧ a = X n i) ∨ (i ≤ n ∧ a = Y n i) := by
  rcases Finset.mem_union.mp ha with hx | hy
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hji : j = i := by simpa only [val3_X] using hv
    subst j
    exact Or.inl ⟨Finset.mem_range.mp hj, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hji : j = i := by simpa only [val3_Y] using hv
    subst j
    exact Or.inr ⟨by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj, rfl⟩

/-- Two distinct elements of the same valuation must be the two entries at that level. -/
theorem construction_equal_valuation_pair {n a b : ℕ}
    (ha : a ∈ construction n) (hb : b ∈ construction n) (hab : a ≠ b)
    (hv : padicValNat 3 a = padicValNat 3 b) :
    ∃ i < n, (a = X n i ∧ b = Y n i) ∨ (a = Y n i ∧ b = X n i) := by
  let i := padicValNat 3 a
  have ha' := construction_at_valuation ha (show padicValNat 3 a = i from rfl)
  have hb' := construction_at_valuation hb (show padicValNat 3 b = i from hv.symm)
  rcases ha' with ⟨hai, hax⟩ | ⟨hai, hay⟩ <;>
    rcases hb' with ⟨hbi, hbx⟩ | ⟨hbi, hby⟩
  · exact False.elim (hab (hax.trans hbx.symm))
  · exact ⟨i, hai, Or.inl ⟨hax, hby⟩⟩
  · exact ⟨i, hbi, Or.inr ⟨hay, hbx⟩⟩
  · exact False.elim (hab (hay.trans hby.symm))

theorem construction_equal_valuation_sum {n a b : ℕ}
    (ha : a ∈ construction n) (hb : b ∈ construction n) (hab : a ≠ b)
    (hv : padicValNat 3 a = padicValNat 3 b) :
    ∃ i < n, a + b = Y n (i + 1) ∧ padicValNat 3 (a + b) = i + 1 := by
  obtain ⟨i, hi, hp | hp⟩ := construction_equal_valuation_pair ha hb hab hv
  all_goals
    have hsum : X n i + Y n i = Y n (i + 1) := by
      rw [Y_eq_two_X n (i + 1), construction_ap_first hi]
    rcases hp with ⟨rfl, rfl⟩
    refine ⟨i, hi, ?_, ?_⟩
    first | exact hsum | exact (by simpa only [add_comm] using hsum)
    first | simpa only [hsum] using val3_Y n (i + 1)
          | simpa only [add_comm, hsum] using val3_Y n (i + 1)


/-- Uniqueness between the equal-valuation representations in Lemma 4.2. -/
theorem construction_equal_pair_unique {n a b c d : ℕ}
    (ha : a ∈ construction n) (hb : b ∈ construction n)
    (hc : c ∈ construction n) (hd : d ∈ construction n)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : padicValNat 3 a = padicValNat 3 b)
    (hvcd : padicValNat 3 c = padicValNat 3 d) (hs : a + b = c + d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  obtain ⟨i, hi, hp⟩ := construction_equal_valuation_pair ha hb hab hvab
  obtain ⟨j, hj, hq⟩ := construction_equal_valuation_pair hc hd hcd hvcd
  have hsi : a + b = Y n (i+1) := by
    have hx : X n i + Y n i = Y n (i+1) := by
      rw [Y_eq_two_X n (i+1), construction_ap_first hi]
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hx
    · simpa only [add_comm] using hx
  have hsj : c + d = Y n (j+1) := by
    have hx : X n j + Y n j = Y n (j+1) := by
      rw [Y_eq_two_X n (j+1), construction_ap_first hj]
    rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hx
    · simpa only [add_comm] using hx
  have hij : i = j := by
    have hh := Y_injective n (hsi.symm.trans (hs.trans hsj))
    omega
  subst j
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

/-- Natural-number specialization of the ultrametric equality. -/
theorem val3_add_of_ne {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : padicValNat 3 a ≠ padicValNat 3 b) :
    padicValNat 3 (a+b) = min (padicValNat 3 a) (padicValNat 3 b) := by
  have hq : (a : ℚ) + (b : ℚ) ≠ 0 := by positivity
  have hva : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hvb : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hval : padicValRat 3 (a : ℚ) ≠ padicValRat 3 (b : ℚ) := by
    simpa only [padicValRat.of_nat, ne_eq, Nat.cast_inj] using hv
  have he := padicValRat.add_eq_min hq hva hvb hval
  have he' : ((padicValNat 3 (a+b) : ℕ) : ℤ) =
      min (padicValNat 3 a : ℤ) (padicValNat 3 b : ℤ) := by
    simpa only [← Nat.cast_add, padicValRat.of_nat] using he
  exact_mod_cast he'

/-- A pair with unequal valuations cannot collide with an equal-valuation pair.
This is the second assertion of Lemma 4.2. -/
theorem construction_mixed_pair_ne_equal_sum {n a b c d : ℕ}
    (ha : a ∈ construction n) (hb : b ∈ construction n)
    (hc : c ∈ construction n) (hd : d ∈ construction n)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : padicValNat 3 a = padicValNat 3 b)
    (hvcd : padicValNat 3 c ≠ padicValNat 3 d) : a+b ≠ c+d := by
  intro hs
  obtain ⟨i, hi, hsum, hval⟩ := construction_equal_valuation_sum ha hb hab hvab
  have hcp := construction_pos hc
  have hdp := construction_pos hd
  have hmin : min (padicValNat 3 c) (padicValNat 3 d) = i+1 := by
    rw [← val3_add_of_ne (by omega) (by omega) hvcd, ← hs]
    exact hval
  have hno (x y : ℕ) (hx : x ∈ construction n) (hy : 0 < y)
      (hxy : x ≠ y) (hxval : padicValNat 3 x = i+1)
      (hseq : x+y = Y n (i+1)) : False := by
    rcases construction_at_valuation hx hxval with ⟨hk, hX⟩ | ⟨hk,hY⟩
    · rw [hX, Y_eq_two_X] at hseq
      omega
    · rw [hY] at hseq
      omega
  rcases le_total (padicValNat 3 c) (padicValNat 3 d) with hle | hle
  · rw [min_eq_left hle] at hmin
    exact hno c d hc hdp hcd hmin (hs.symm.trans hsum)
  · rw [min_eq_right hle] at hmin
    exact hno d c hd hcp hcd.symm hmin (by omega)

/-- Type-1 uniqueness with each pair oriented by increasing 3-adic valuation. -/
theorem construction_mixed_pair_unique_oriented {n a b c d : ℕ}
    (ha : a ∈ construction n) (hb : b ∈ construction n)
    (hc : c ∈ construction n) (hd : d ∈ construction n)
    (hvab : padicValNat 3 a < padicValNat 3 b)
    (hvcd : padicValNat 3 c < padicValNat 3 d) (hs : a+b = c+d) :
    a = c ∧ b = d := by
  have hap := construction_pos ha
  have hbp := construction_pos hb
  have hcp := construction_pos hc
  have hdp := construction_pos hd
  have hmin : padicValNat 3 a = padicValNat 3 c := by
    have he := congrArg (padicValNat 3) hs
    rw [val3_add_of_ne (by omega) (by omega) (ne_of_lt hvab),
      val3_add_of_ne (by omega) (by omega) (ne_of_lt hvcd),
      min_eq_left hvab.le, min_eq_left hvcd.le] at he
    exact he
  let k := padicValNat 3 a
  have hbd : 3^(k+1) ∣ b := (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
  have hdd : 3^(k+1) ∣ d := (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
  have hXd : ¬3^(k+1) ∣ X n k := by
    rw [padicValNat_dvd_iff_le (by have := X_pos n k; omega), val3_X]
    omega
  have ha' := construction_at_valuation ha (show padicValNat 3 a = k from rfl)
  have hc' := construction_at_valuation hc (show padicValNat 3 c = k from hmin.symm)
  have hac : a = c := by
    rcases ha' with ⟨hak, hax⟩ | ⟨hak, hay⟩ <;>
      rcases hc' with ⟨hck, hcx⟩ | ⟨hck, hcy⟩
    · exact hax.trans hcx.symm
    · exfalso
      rw [hax, hcy, Y_eq_two_X] at hs
      have hbe : b = X n k + d := by omega
      exact hXd ((Nat.dvd_add_iff_left hdd).mpr (hbe ▸ hbd))
    · exfalso
      rw [hay, hcx, Y_eq_two_X] at hs
      have hde : d = X n k + b := by omega
      exact hXd ((Nat.dvd_add_iff_left hbd).mpr (hde ▸ hdd))
    · exact hay.trans hcy.symm
  exact ⟨hac, by omega⟩

/-- Lemma 4.1 between competing type-1 pairs. Equal-valuation competitors
are excluded separately by `construction_mixed_pair_ne_equal_sum`. -/
theorem construction_mixed_pair_unique {n a b c d : ℕ}
    (ha : a ∈ construction n) (hb : b ∈ construction n)
    (hc : c ∈ construction n) (hd : d ∈ construction n)
    (hvab : padicValNat 3 a ≠ padicValNat 3 b)
    (hvcd : padicValNat 3 c ≠ padicValNat 3 d) (hs : a+b = c+d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases lt_or_gt_of_ne hvab with hvab | hvab <;>
    rcases lt_or_gt_of_ne hvcd with hvcd | hvcd
  · exact Or.inl (construction_mixed_pair_unique_oriented ha hb hc hd hvab hvcd hs)
  · exact Or.inr (construction_mixed_pair_unique_oriented ha hb hd hc hvab hvcd
      (by omega))
  · have he := construction_mixed_pair_unique_oriented hb ha hc hd hvab hvcd (by omega)
    exact Or.inr ⟨he.2, he.1⟩
  · have he := construction_mixed_pair_unique_oriented hb ha hd hc hvab hvcd (by omega)
    exact Or.inl ⟨he.2, he.1⟩

/-- Proposition 4.3 in natural-number form. In fact the construction is weak
Sidon for every parameter, including the two boundary cases. -/
theorem construction_weakSidon_nat (n : ℕ) {a b c d : ℕ}
    (ha : a ∈ construction n) (hb : b ∈ construction n)
    (hc : c ∈ construction n) (hd : d ∈ construction n)
    (hab : a < b) (hcd : c < d) (hs : a+b = c+d) : a=c ∧ b=d := by
  by_cases hvab : padicValNat 3 a = padicValNat 3 b
  · by_cases hvcd : padicValNat 3 c = padicValNat 3 d
    · rcases construction_equal_pair_unique ha hb hc hd (by omega) (by omega)
        hvab hvcd hs with he | he
      · exact he
      · omega
    · exact False.elim (construction_mixed_pair_ne_equal_sum ha hb hc hd (by omega)
        (by omega) hvab hvcd hs)
  · by_cases hvcd : padicValNat 3 c = padicValNat 3 d
    · exact False.elim (construction_mixed_pair_ne_equal_sum hc hd ha hb (by omega)
        (by omega) hvcd hvab hs.symm)
    · rcases construction_mixed_pair_unique ha hb hc hd hvab hvcd hs with he | he
      · exact he
      · omega

/-- Proposition 4.3 over the paper's ambient field of real numbers. -/
theorem construction_weakSidon_real (n : ℕ) :
    IsWeakSidon (((↑) : ℕ → ℝ) '' (construction n : Set ℕ)) := by
  intro x y u v hx hy hu hv hxy huv hs
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨c, hc, rfl⟩ := hu
  obtain ⟨d, hd, rfl⟩ := hv
  have hab : a < b := by exact_mod_cast hxy
  have hcd : c < d := by exact_mod_cast huv
  have hs' : a+b = c+d := by exact_mod_cast hs
  obtain ⟨hac,hbd⟩ := construction_weakSidon_nat n ha hb hc hd hab hcd hs'
  exact ⟨congrArg (fun z : ℕ => (z : ℝ)) hac, congrArg (fun z : ℕ => (z : ℝ)) hbd⟩

theorem X_strictMonoOn (n : ℕ) : StrictMonoOn (X n) (Set.Iic n) := by
  apply strictMonoOn_Iic_of_lt_succ
  intro i hi
  exact (construction_ap_first_order hi).1

theorem Y_strictMonoOn (n : ℕ) : StrictMonoOn (Y n) (Set.Iic n) := by
  apply strictMonoOn_Iic_of_lt_succ
  intro i hi
  exact (construction_ap_second_order hi).2

/-- The two extreme points of the construction. -/
theorem construction_bounds {n a : ℕ} (ha : a ∈ construction n) :
    X n 0 ≤ a ∧ a ≤ Y n n := by
  have hxmono := (X_strictMonoOn n).monotoneOn
  have hymono := (Y_strictMonoOn n).monotoneOn
  rcases Finset.mem_union.mp ha with hx | hy
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
    have hlo : X n 0 ≤ X n i := hxmono (by simp) hin (by omega)
    have hhi : Y n i ≤ Y n n := hymono hin (by simp) hin
    have he := Y_eq_two_X n i
    exact ⟨hlo, by omega⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
    have hlo : X n 0 ≤ X n i := hxmono (by simp) hin (by omega)
    have hhi : Y n i ≤ Y n n := hymono hin (by simp) hin
    have he := Y_eq_two_X n i
    exact ⟨by omega, hhi⟩

/-- Lemma 4.4: every ordered nonconstant AP is one of the two displayed families. -/
theorem construction_ap_classification {n a m b : ℕ}
    (ha : a ∈ construction n) (hm : m ∈ construction n) (hb : b ∈ construction n)
    (ham : a < m) (hmb : m < b) (hs : a+b = m+m) :
    (∃ i, i+1 < n ∧ a = X n i ∧ m = X n (i+1) ∧ b = Y n i) ∨
    (∃ i, i < n ∧ a = X n i ∧ m = Y n i ∧ b = Y n (i+1)) := by
  rcases Finset.mem_union.mp hm with hx | hy
  · obtain ⟨i, hi, hmi⟩ := Finset.mem_image.mp hx
    have hin : i < n := Finset.mem_range.mp hi
    have hi0 : i ≠ 0 := by
      intro hz
      subst i
      have hlo := (construction_bounds ha).1
      omega
    let j := i-1
    have hji : j+1 = i := by omega
    have hjn : j < n := by omega
    have hAP := construction_ap_first hjn
    have hY : Y n j ∈ construction n := Y_mem_construction (by omega)
    have hX : X n j ∈ construction n := X_mem_construction hjn
    have horder := construction_ap_first_order hjn
    have hep : X n j < Y n j := horder.1.trans horder.2
    have heq : a+b = X n j + Y n j := by
      rw [hAP, hji, hmi] at *
      omega
    have he := construction_weakSidon_nat n ha hb hX hY (ham.trans hmb) hep heq
    exact Or.inl ⟨j, by omega, he.1, by omega, he.2⟩
  · obtain ⟨i, hi, hmi⟩ := Finset.mem_image.mp hy
    have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
    have hi' : i < n := by
      have hhi := (construction_bounds hb).2
      by_contra hh
      have : i = n := by omega
      subst i
      omega
    have hAP := construction_ap_second hi'
    have hY : Y n (i+1) ∈ construction n := Y_mem_construction (by omega)
    have hX : X n i ∈ construction n := X_mem_construction hi'
    have horder := construction_ap_second_order hi'
    have hep : X n i < Y n (i+1) := horder.1.trans horder.2
    have heq : a+b = X n i + Y n (i+1) := by
      rw [hAP, hmi] at *
      omega
    have he := construction_weakSidon_nat n ha hb hX hY (ham.trans hmb) hep heq
    exact Or.inr ⟨i, hi', he.1, hmi.symm, he.2⟩

/-- The two explicit AP families in Lemma 4.4, represented by increasing triples. -/
def constructionAPs (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n-1)).image (fun i => (X n i, X n (i+1), Y n i))) ∪
  ((Finset.range n).image (fun i => (X n i, Y n i, Y n (i+1))))

theorem constructionAPs_card (n : ℕ) : (constructionAPs n).card = 2*n-1 := by
  have hfirst : Function.Injective (fun i => (X n i, X n (i+1), Y n i)) := by
    intro i j hij
    exact X_injective n (congrArg Prod.fst hij)
  have hsecond : Function.Injective (fun i => (X n i, Y n i, Y n (i+1))) := by
    intro i j hij
    exact X_injective n (congrArg Prod.fst hij)
  have hdis : Disjoint
      ((Finset.range (n-1)).image (fun i => (X n i, X n (i+1), Y n i)))
      ((Finset.range n).image (fun i => (X n i, Y n i, Y n (i+1)))) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, hjp⟩ := Finset.mem_image.mp hq
    have he := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) (hip.trans hjp.symm)
    exact X_ne_Y n (i+1) j he
  unfold constructionAPs
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ hfirst, Finset.card_image_of_injective _ hsecond]
  simp only [Finset.card_range]
  omega

/-- Exact membership equivalence for the AP list of Lemma 4.4. -/
theorem mem_constructionAPs_iff {n a m b : ℕ} :
    (a,m,b) ∈ constructionAPs n ↔
      a ∈ construction n ∧ m ∈ construction n ∧ b ∈ construction n ∧
        a < m ∧ m < b ∧ a+b = m+m := by
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hfirst | hsecond
    · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hfirst
      have hin : i+1 < n := by have := Finset.mem_range.mp hi; omega
      have hi' : i < n := by omega
      have ha := congrArg Prod.fst he
      have hm := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) he
      have hb := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) he
      simp only at ha hm hb
      subst a; subst m; subst b
      refine ⟨X_mem_construction hi', X_mem_construction hin,
        Y_mem_construction (by omega), (construction_ap_first_order hi').1,
        (construction_ap_first_order hi').2, ?_⟩
      have hAP := construction_ap_first hi'
      omega
    · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hsecond
      have hin : i < n := Finset.mem_range.mp hi
      have ha := congrArg Prod.fst he
      have hm := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) he
      have hb := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) he
      simp only at ha hm hb
      subst a; subst m; subst b
      refine ⟨X_mem_construction hin, Y_mem_construction (by omega),
        Y_mem_construction (by omega), (construction_ap_second_order hin).1,
        (construction_ap_second_order hin).2, ?_⟩
      have hAP := construction_ap_second hin
      omega
  · rintro ⟨ha,hm,hb,ham,hmb,hs⟩
    rcases construction_ap_classification ha hm hb ham hmb hs with hfirst | hsecond
    · obtain ⟨i, hi, rfl,rfl,rfl⟩ := hfirst
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
    · obtain ⟨i, hi, rfl,rfl,rfl⟩ := hsecond
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

end SidonPaper
