module

public import SidonPaper.Basic
public import SidonPaper.FiniteWitness

@[expose] public section


namespace SidonPaper

/-- The integer certificate uses exactly the same Sidon condition as the paper
when the integer set is viewed as a subset of the reals. -/
theorem sidon_intCast_iff (S : Finset ℤ) :
    IsSidon (((↑) : ℤ → ℝ) '' (S : Set ℤ)) ↔ Certificate.SidonByPairs S := by
  constructor
  · intro h a ha b hb c hc d hd hab hcd hs
    have hab' : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
    have hcd' : (c : ℝ) ≤ (d : ℝ) := Int.cast_le.mpr hcd
    have hs' : (a : ℝ) + (b : ℝ) = (c : ℝ) + (d : ℝ) := by
      simpa only [Int.cast_add] using congrArg (fun z : ℤ => (z : ℝ)) hs
    have he := h ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ hab' hcd' hs'
    exact ⟨Int.cast_injective he.1, Int.cast_injective he.2⟩
  · intro h x y u v hx hy hu hv hxy huv hs
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    rcases hu with ⟨c, hc, rfl⟩
    rcases hv with ⟨d, hd, rfl⟩
    have hs' : a + b = c + d := by
      apply Int.cast_injective (α := ℝ)
      simpa only [Int.cast_add] using hs
    obtain ⟨hac, hbd⟩ := h a ha b hb c hc d hd
      (Int.cast_le.mp hxy) (Int.cast_le.mp huv) hs'
    exact ⟨congrArg (fun z : ℤ => (z : ℝ)) hac,
      congrArg (fun z : ℤ => (z : ℝ)) hbd⟩

/-- The explicit eight-point witness in Lemma 5.1 is Sidon over the reals. -/
theorem witness_sidon_real :
    IsSidon (((↑) : ℤ → ℝ) '' (Certificate.witness : Set ℤ)) := by
  apply (sidon_intCast_iff Certificate.witness).mpr
  exact (Certificate.sidonByCount_iff Certificate.witness).mp
    Certificate.witness_sidon_by_count

end SidonPaper
