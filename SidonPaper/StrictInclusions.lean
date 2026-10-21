module

public import SidonPaper.RealCertificate
public import SidonPaper.Relations

@[expose] public section


namespace SidonPaper

private def intWeak (S : Finset ℤ) : Prop :=
  ∀ a∈S,∀ b∈S,∀ c∈S,∀ d∈S,a<b → c<d → a+b=c+d → a=c ∧ b=d

private instance (S : Finset ℤ) : Decidable (intWeak S) :=
  inferInstanceAs (Decidable (∀ a∈S,∀ b∈S,∀ c∈S,∀ d∈S,
    a<b → c<d → a+b=c+d → a=c ∧ b=d))

private theorem cast_weak {S : Finset ℤ} (h : intWeak S) :
    IsWeakSidon (realImage S : Set ℝ) := by
  rw [realImage_coe]
  intro x y u v hx hy hu hv hxy huv hs
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  obtain ⟨c,hc,rfl⟩ := hu
  obtain ⟨d,hd,rfl⟩ := hv
  have hs' : a+b=c+d := by
    apply Int.cast_injective (α:=ℝ)
    simpa only [Int.cast_add] using hs
  obtain ⟨h1,h2⟩ := h a ha b hb c hc d hd
    (Int.cast_lt.mp hxy) (Int.cast_lt.mp huv) hs'
  exact ⟨congrArg (fun z:ℤ => (z:ℝ)) h1,congrArg (fun z:ℤ => (z:ℝ)) h2⟩

/-- The first strict-inclusion example in Section2.1. -/
theorem weak_not_fourFive_example :
    IsWeakSidon (realImage ({1,2,3,5}:Finset ℤ) : Set ℝ) ∧
    ¬ IsFourFive (realImage ({1,2,3,5}:Finset ℤ)) := by
  classical
  constructor
  · exact cast_weak (by decide +kernel)
  · intro h
    have hc : (realImage ({1,2,3,5}:Finset ℤ)).card=4 := by
      rw [realImage_card]; decide
    have hl := h _ (Finset.Subset.refl _) hc
    rw [differences_realImage,realImage_card] at hl
    have hd : (Certificate.positiveDifferences ({1,2,3,5}:Finset ℤ)).card=4 := by
      decide +kernel
    omega

/-- The second strict-inclusion example in Section2.1. -/
theorem fourFive_not_sidon_example :
    IsFourFive (realImage ({1,2,3,6}:Finset ℤ)) ∧
    ¬ IsSidon (realImage ({1,2,3,6}:Finset ℤ) : Set ℝ) := by
  classical
  constructor
  · exact fourFive_realImage (by decide +kernel)
  · intro h
    have hi := (sidon_intCast_iff ({1,2,3,6}:Finset ℤ)).mp
      (by rwa [← realImage_coe])
    have he := hi 1 (by simp) 3 (by simp) 2 (by simp) 2 (by simp)
      (by omega) (by omega) (by omega)
    omega

end SidonPaper
