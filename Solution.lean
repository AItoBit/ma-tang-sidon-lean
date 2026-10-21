module

public import SidonPaper

public section

namespace SidonSubmission
open Filter SidonPaper

/-- Ma–Tang Theorem 1.2: the normalized weak Sidon extremum tends to 1/2. -/
theorem weak_sidon_limit :
    Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ)) atTop (nhds (1 / 2 : ℝ)) := by
  exact SidonPaper.theorem_1_2

/-- Ma–Tang Theorem 1.3, with the exact ceiling and positive-index range. -/
theorem exact_weak_sidon_size : ∀ n : ℕ, 1 ≤ n → g n = (n + 2) / 2 := by
  exact SidonPaper.theorem_1_3

/-- Ma–Tang Theorem 1.5: convergence and the optimal-constant identity. -/
theorem four_five_limit :
    Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop (nhds cStar) ∧
    cStar = sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = (f n : ℝ) / (n : ℝ)} := by
  exact SidonPaper.theorem_1_5

/-- Only the upper bound of Ma–Tang Theorem 1.6; the lower bound is omitted. -/
theorem density_upper : cStar ≤ (4 / 7 : ℝ) := by
  exact SidonPaper.cStar_le_four_sevenths

/-- Chvátal–McDiarmid bound, recalled as Ma–Tang Theorem 4.6. -/
theorem transversal_bound {α : Type*} {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) : 4 * H.tau ≤ H.vertices.card + H.edges.card := by
  exact SidonPaper.FiniteHypergraph.transversal_four h3

end SidonSubmission
