module

public import SidonPaper.Attainment
public import SidonPaper.Limits

@[expose] public section


namespace SidonPaper
open Filter Set

private theorem ratio_image_eq (u : ℕ → ℝ) :
    ((fun n : ℕ => u n / (n : ℝ)) '' Ici 1) =
      {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = u n / (n : ℝ)} := by
  ext r
  constructor
  · rintro ⟨n,hn,hr⟩
    exact ⟨n,hn,hr.symm⟩
  · rintro ⟨n,hn,hr⟩
    exact ⟨n,hn,hr.symm⟩

/-- Existence and infimum characterization of the normalized weak-Sidon limit,
the first assertion in Theorem 1.2. Its value 1/2 requires Section 4. -/
theorem g_ratio_tendsto_inf :
    Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ)) atTop
      (nhds (sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = (g n : ℝ) / (n : ℝ)})) := by
  have hs : Subadditive (fun n : ℕ => (g n : ℝ)) := by
    intro m n
    simpa only [Nat.cast_add] using
      (Nat.cast_le.mpr (g_subadditive m n) : (g (m+n) : ℝ) ≤ (g m + g n : ℕ))
  have ht := fekete_nonnegative hs (fun n => Nat.cast_nonneg (g n))
  rw [ratio_image_eq] at ht
  exact ht

/-- Proposition 3.7, also including index zero. -/
theorem f_subadditive (m n : ℕ) : f (m+n) ≤ f m + f n := by
  classical
  obtain ⟨A,hAc,hA,hAf⟩ := f_attained m
  obtain ⟨B,hBc,hB,hBf⟩ := f_attained n
  obtain ⟨q,t,hq,hC,hCc,hCh⟩ := fourFive_affine_gluing A B hA hB
  have hh := f_le_h hC
  rw [hCc,hAc,hBc] at hh
  rw [hAf,hBf] at hCh
  exact hh.trans hCh

/-- Fekete's theorem applied to the nonnegative finite extremal sequence f. -/
theorem f_ratio_tendsto_inf :
    Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop
      (nhds (sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = (f n : ℝ) / (n : ℝ)})) := by
  have hs : Subadditive (fun n : ℕ => (f n : ℝ)) := by
    intro m n
    simpa only [Nat.cast_add] using
      (Nat.cast_le.mpr (f_subadditive m n) : (f (m+n) : ℝ) ≤ (f m + f n : ℕ))
  have ht := fekete_nonnegative hs (fun n => Nat.cast_nonneg (f n))
  rw [ratio_image_eq] at ht
  exact ht

/-- Theorem 1.5, with both convergence and the optimal-constant characterization. -/
theorem theorem_1_5 : Theorem_1_5 := by
  constructor
  · rw [cStar_eq_inf_f_ratio]
    exact f_ratio_tendsto_inf
  · exact cStar_eq_inf_f_ratio

end SidonPaper
