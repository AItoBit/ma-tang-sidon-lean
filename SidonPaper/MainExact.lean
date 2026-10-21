module

public import SidonPaper.TransversalTheorem
public import SidonPaper.ConstructionUpper
public import SidonPaper.CeilingAsymptotic

@[expose] public section


namespace SidonPaper
open Filter

/-- A nonempty finite set has a singleton Sidon subset. -/
theorem one_le_h_of_nonempty {A : Finset ℝ} (hA : A.Nonempty) : 1 ≤ h A := by
  classical
  obtain ⟨a,ha⟩ := hA
  have hsingle : IsSidon (({a}:Finset ℝ) : Set ℝ) := by
    intro x y z w hx hy hz hw hxy hzw hs
    simp only [Finset.mem_coe,Finset.mem_singleton] at hx hy hz hw
    exact ⟨hx.trans hz.symm,hy.trans hw.symm⟩
  have hc := card_le_h (A := A) (B := {a}) (by simpa using ha) hsingle
  simpa only [Finset.card_singleton] using hc

/-- The lower bound in Theorem1.3, now using the proved general inequality4.6. -/
theorem g_lower {n : ℕ} (hn : 1 ≤ n) : (n+2)/2 ≤ g n := by
  obtain ⟨A,hcard,hw,hh⟩ := g_attained n
  by_cases hn1 : n = 1
  · have hpos : A.Nonempty := Finset.card_pos.mp (by omega)
    have hc := one_le_h_of_nonempty hpos
    omega
  · have hn2 : 2 ≤ A.card := by omega
    have he := apHypergraph_edges_card_le hw hn2
    have ht := FiniteHypergraph.transversal_four (apHypergraph_uniform A)
    have ha := h_add_hypergraph_tau hw
    change 4*(apHypergraph A).tau ≤ A.card + (apHypergraph A).edges.card at ht
    omega

/-- Theorem1.3: the exact ceiling formula, for every positive integer n. -/
theorem theorem_1_3 : Theorem_1_3 := by
  intro n hn
  exact Nat.le_antisymm (g_upper n) (g_lower hn)

/-- Theorem1.2: the normalized weak-Sidon extremal function tends to1/2. -/
theorem theorem_1_2 : Theorem_1_2 := by
  have heq : (fun n : ℕ => (((n+2)/2 : ℕ) : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => (g n : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    rw [theorem_1_3 n hn]
  exact Filter.Tendsto.congr' heq ceiling_half_ratio_tendsto

end SidonPaper
