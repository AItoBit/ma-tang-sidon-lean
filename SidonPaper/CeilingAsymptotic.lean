module

public import SidonPaper.ExtremalLimits

@[expose] public section


namespace SidonPaper
open Filter

/-- The exact natural-number ceiling appearing in Theorem1.3 has normalized
limit1/2. This contains no claim about g until its exact formula is proved. -/
theorem ceiling_half_ratio_tendsto :
    Tendsto (fun n : ℕ => (((n+2)/2 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1/2 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => (1/2 : ℝ) + 1 / (n : ℝ))
      atTop (nhds (1/2 : ℝ)) := by
    have hz : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.add hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hnR : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    have hlow : n ≤ 2*((n+2)/2) := by omega
    have hlowR : (n:ℝ) ≤ 2 * (((n+2)/2:ℕ):ℝ) := by exact_mod_cast hlow
    apply (le_div_iff₀ hnR).mpr
    linarith
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hnR : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    have hup : 2*((n+2)/2) ≤ n+2 := by omega
    have hupR : 2 * (((n+2)/2:ℕ):ℝ) ≤ (n:ℝ)+2 := by exact_mod_cast hup
    apply (div_le_iff₀ hnR).mpr
    rw [add_mul,div_mul_cancel₀ _ hnR.ne']
    linarith

end SidonPaper
