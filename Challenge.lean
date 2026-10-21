module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Selected results of Ma–Tang, arXiv:2602.23282v2

This submission covers Theorems 1.2, 1.3, 1.5, the upper bound in 1.6,
and the finite three-uniform transversal bound recalled as Theorem 4.6.
It is a PARTIAL formalization of the paper: Theorem 5.3 and the lower
9/17 bound in 1.6 are not proved or claimed here.

A Sidon set has unique unordered pair sums, allowing repeated summands.
A weak Sidon set requires uniqueness only for pairs of distinct elements.
A (4,5)-set has at least five distinct positive differences in each
four-element subset. h(A) is the largest Sidon subset size; g(n) and f(n)
minimize h(A) among n-element weak Sidon and (4,5)-sets respectively.
The development proves that these minima are attained. cStar is the optimal
universal Sidon density over nonempty finite (4,5)-sets.

The natural quotient (n+2)/2 in Theorem 1.3 is ceil((n+1)/2), for n >= 1.
Theorem 1.5 includes convergence and the infimum characterization.
Theorem 4.6 applies to all finite three-uniform simple hypergraphs,
including isolated vertices. tau is the minimum transversal size.

Only this statement-only Challenge uses deliberate holes. Solution and its
entire proof closure have no holes or additional mathematical axioms.
-/

@[expose] public section

namespace SidonPaper
open Filter

/-- Unique sums of unordered pairs, including repeated summands. -/
def IsSidon (A : Set ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- Unique sums of unordered pairs with distinct endpoints. -/
def IsWeakSidon (A : Set ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a < b → c < d → a + b = c + d → a = c ∧ b = d

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

/-- Weak Sidon extremal function. The Solution proves nonemptiness and attainment. -/
noncomputable def g (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℝ, A.card = n ∧ IsWeakSidon (A : Set ℝ) ∧ h A = k}

/-- (4,5) extremal function; the Solution proves nonemptiness and attainment. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℝ, A.card = n ∧ IsFourFive A ∧ h A = k}

/-- Optimal universal Sidon density in finite nonempty (4,5)-sets. -/
noncomputable def cStar : ℝ :=
  sSup {c : ℝ | ∀ A : Finset ℝ, 0 < A.card → IsFourFive A →
    c * (A.card : ℝ) ≤ (h A : ℝ)}

/-- Finite simple hypergraphs; every edge is a nonempty subset of vertices. -/
structure FiniteHypergraph (α : Type*) where
  vertices : Finset α
  edges : Finset (Finset α)
  edge_subset : ∀ e ∈ edges, e ⊆ vertices
  edge_nonempty : ∀ e ∈ edges, e.Nonempty

namespace FiniteHypergraph
variable {α : Type*}

/-- T meets every edge. -/
def Transversal (H : FiniteHypergraph α) (T : Finset α) : Prop :=
  ∀ e ∈ H.edges, ∃ x ∈ e, x ∈ T

/-- Minimum cardinality of a transversal contained in the vertex set. -/
noncomputable def tau (H : FiniteHypergraph α) : ℕ :=
  sInf {n : ℕ | ∃ T : Finset α, T ⊆ H.vertices ∧ H.Transversal T ∧ T.card = n}

/-- Every edge contains exactly three vertices. -/
def ThreeUniform (H : FiniteHypergraph α) : Prop := ∀ e ∈ H.edges, e.card = 3

end FiniteHypergraph
end SidonPaper

namespace SidonSubmission
open Filter SidonPaper

/-- Ma–Tang Theorem 1.2: the normalized weak Sidon extremum tends to 1/2. -/
theorem weak_sidon_limit :
    Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ)) atTop (nhds (1 / 2 : ℝ)) := by
  sorry

/-- Ma–Tang Theorem 1.3, with the exact ceiling and positive-index range. -/
theorem exact_weak_sidon_size : ∀ n : ℕ, 1 ≤ n → g n = (n + 2) / 2 := by
  sorry

/-- Ma–Tang Theorem 1.5: convergence and the optimal-constant identity. -/
theorem four_five_limit :
    Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop (nhds cStar) ∧
    cStar = sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = (f n : ℝ) / (n : ℝ)} := by
  sorry

/-- Only the upper bound of Ma–Tang Theorem 1.6; the lower bound is omitted. -/
theorem density_upper : cStar ≤ (4 / 7 : ℝ) := by
  sorry

/-- Chvátal–McDiarmid bound, recalled as Ma–Tang Theorem 4.6. -/
theorem transversal_bound {α : Type*} {H : FiniteHypergraph α}
    (h3 : H.ThreeUniform) : 4 * H.tau ≤ H.vertices.card + H.edges.card := by
  sorry

end SidonSubmission
