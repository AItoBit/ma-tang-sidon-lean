module

public import SidonPaper.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section


/-! Exact main targets from arXiv:2602.23282v2.
These definitions are specifications, NOT proofs of the main results.
No unproved result is introduced as an axiom or theorem.
-/
namespace SidonPaper
open Filter

/-- Positive differences, one per unordered pair of distinct points. -/
noncomputable def differences (A : Finset ℝ) : Finset ℝ := by
  classical
  exact ((A.product A).filter (fun p => p.1 < p.2)).image (fun p => p.2 - p.1)

/-- The paper's local (4,5) condition. Positive differences equal the absolute
values obtained by taking one orientation of each unordered pair. -/
def IsFourFive (A : Finset ℝ) : Prop :=
  ∀ B : Finset ℝ, B ⊆ A → B.card = 4 → 5 ≤ (differences B).card

/-- Largest cardinality of a Sidon subset (the empty subset is permitted). -/
noncomputable def h (A : Finset ℝ) : ℕ := by
  classical
  exact (A.powerset.filter (fun B : Finset ℝ => IsSidon (B : Set ℝ))).sup Finset.card

/-- Independence number of the AP hypergraph, expressed through AP-free subsets. -/
noncomputable def apIndependenceNumber (A : Finset ℝ) : ℕ := by
  classical
  exact (A.powerset.filter (fun B : Finset ℝ => IsAPFree (B : Set ℝ))).sup Finset.card

/-- The equality of extremal quantities in Lemma 2.3. -/
theorem h_eq_apIndependenceNumber {A : Finset ℝ} (hw : IsWeakSidon (A : Set ℝ)) :
    h A = apIndependenceNumber A := by
  classical
  unfold h apIndependenceNumber
  congr 1
  apply Finset.filter_congr
  intro B hB
  apply sidon_subset_iff_apFree hw
  intro x hx
  exact (Finset.mem_powerset.mp hB) hx

/-- Weak Sidon extremal function. Attainment/nonemptiness still needs proving
before using this totalized natural infimum as a minimum. -/
noncomputable def g (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℝ, A.card = n ∧ IsWeakSidon (A : Set ℝ) ∧ h A = k}

/-- (4,5) extremal function, with the same attainment obligation as g. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℝ, A.card = n ∧ IsFourFive A ∧ h A = k}

/-- Optimal universal Sidon density in finite nonempty (4,5)-sets. -/
noncomputable def cStar : ℝ :=
  sSup {c : ℝ | ∀ A : Finset ℝ, 0 < A.card → IsFourFive A →
    c * (A.card : ℝ) ≤ (h A : ℝ)}

/-- Theorem 1.2: specification only. -/
def Theorem_1_2 : Prop :=
  Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ)) atTop (nhds (1 / 2 : ℝ))

/-- Theorem 1.3: ceiling((n+1)/2), NOT floor((n+1)/2). -/
def Theorem_1_3 : Prop := ∀ n : ℕ, 1 ≤ n → g n = (n + 2) / 2

/-- Theorem 1.5: specification only. -/
def Theorem_1_5 : Prop :=
  Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop (nhds cStar) ∧
    cStar = sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = (f n : ℝ) / (n : ℝ)}

/-- Theorem 1.6: specification only. -/
def Theorem_1_6 : Prop := (9 / 17 : ℝ) ≤ cStar ∧ cStar ≤ (4 / 7 : ℝ)

/-- Ordered AP edges give a canonical representation of the AP hypergraph. -/
noncomputable def apEdges (A : Finset ℝ) : Finset (ℝ × ℝ × ℝ) := by
  classical
  exact (A.product (A.product A)).filter
    (fun p => p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ p.1 + p.2.2 = p.2.1 + p.2.1)

/-- Positive-integer construction in Section 4.1. Use only indices i<n for X
and i≤n for Y; subtraction in the exponents then agrees with the source. -/
def X (n i : ℕ) : ℕ := 2 ^ (n - i) * 3 ^ i
def Y (n i : ℕ) : ℕ := 2 ^ (n - i + 1) * 3 ^ i

def construction (n : ℕ) : Finset ℕ :=
  ((Finset.range n).image (X n)) ∪ ((Finset.range (n + 1)).image (Y n))

/-- The five-edge F7 in Figure 1; not the seven-edge Fano plane. -/
def F7 : Finset (Finset ℕ) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {2, 4, 6}}

end SidonPaper
