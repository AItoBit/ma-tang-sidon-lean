module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section


/-!
# Finite certificates for Ma–Tang, arXiv:2602.23282v2, Lemma 5.1

This module checks the exact integer example in the paper. `SidonByCount` says
that the sum map on unordered pairs, including repeated summands, loses no
cardinality. `FourFiveByCount` checks all four-element subsets.

The checks use `decide`, whose proof terms are checked by Lean's kernel.
They do not use native evaluation. This module by itself does not establish
the real-valued extremal-function or limiting theorems of the paper.
-/

namespace SidonPaper.Certificate

/-- The fourteen integers in Lemma 5.1, without affine normalization. -/
def base : Finset ℤ :=
  {0, 136, 200, 243, 246, 249, 272, 286, 298, 323, 400, 528, 596, 1056}

/-- The explicit eight-point Sidon subset printed in the paper. -/
def witness : Finset ℤ := {0, 136, 200, 243, 246, 298, 323, 528}

/-- Unordered pairs represented by their nondecreasing enumeration. -/
def orderedPairs (S : Finset ℤ) : Finset (ℤ × ℤ) :=
  (S ×ˢ S).filter (fun p => p.1 ≤ p.2)

/-- All sums, including sums of an element with itself. -/
def pairSums (S : Finset ℤ) : Finset ℤ :=
  (orderedPairs S).image (fun p => p.1 + p.2)

/-- Finite-cardinality formulation of injectivity of the unordered-pair sum map. -/
def SidonByCount (S : Finset ℤ) : Prop :=
  (pairSums S).card = (orderedPairs S).card

instance (S : Finset ℤ) : Decidable (SidonByCount S) :=
  inferInstanceAs (Decidable ((pairSums S).card = (orderedPairs S).card))

/-- Positive differences: each unordered pair of distinct elements appears once. -/
def positiveDifferences (S : Finset ℤ) : Finset ℤ :=
  ((S ×ˢ S).filter (fun p => p.1 < p.2)).image (fun p => p.2 - p.1)

/-- Every four-element subset has at least five pairwise absolute differences. -/
def FourFiveByCount (S : Finset ℤ) : Prop :=
  ∀ B ∈ S.powersetCard 4, 5 ≤ (positiveDifferences B).card

instance (S : Finset ℤ) : Decidable (FourFiveByCount S) :=
  inferInstanceAs (Decidable (∀ B ∈ S.powersetCard 4,
    5 ≤ (positiveDifferences B).card))

/-- The usual uniqueness formulation, with the order fixing pair orientation. -/
def SidonByPairs (S : Finset ℤ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

 theorem sidonByCount_iff (S : Finset ℤ) :
    SidonByCount S ↔ SidonByPairs S := by
  unfold SidonByCount pairSums
  rw [Finset.card_image_iff]
  constructor
  · intro h a ha b hb c hc d hd hab hcd heq
    have hp : (a, b) ∈ orderedPairs S := by
      simp [orderedPairs, ha, hb, hab]
    have hq : (c, d) ∈ orderedPairs S := by
      simp [orderedPairs, hc, hd, hcd]
    have hpair := h hp hq heq
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  · intro h p hp q hq heq
    have hp' : (p.1 ∈ S ∧ p.2 ∈ S) ∧ p.1 ≤ p.2 := by
      simpa [orderedPairs] using hp
    have hq' : (q.1 ∈ S ∧ q.2 ∈ S) ∧ q.1 ≤ q.2 := by
      simpa [orderedPairs] using hq
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp'
    obtain ⟨⟨hc, hd⟩, hcd⟩ := hq'
    exact Prod.ext (h p.1 ha p.2 hb q.1 hc q.2 hd hab hcd heq).1
      (h p.1 ha p.2 hb q.1 hc q.2 hd hab hcd heq).2

 theorem sidonByCount_mono {S T : Finset ℤ} (hST : S ⊆ T)
    (hT : SidonByCount T) : SidonByCount S := by
  rw [sidonByCount_iff] at hT ⊢
  intro a ha b hb c hc d hd hab hcd heq
  exact hT a (hST ha) b (hST hb) c (hST hc) d (hST hd) hab hcd heq


end SidonPaper.Certificate
