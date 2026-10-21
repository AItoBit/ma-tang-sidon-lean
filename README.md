# Ma–Tang Sidon paper: selected verified results (partial paper formalization)

**Full formalization not completed.** The remaining principal dependency is
Theorem5.3 and the lower bound in Theorem1.6. This is not a completed paper formalization. The verified subset is packaged for Palomar with its omissions explicitly disclosed.

Source: Jie Ma and Quanyu Tang, *Largest Sidon Subsets in Weak Sidon Sets*,
arXiv:2602.23282v2, 6 March 2026, 15pages, no appendices. Both uploaded copies:
SHA256 51929e5f6794f12b972e005cf7c57467a5ca7b121fd86b5b2be377b13f4ce374.

## Main statements

| Source | Verified status |
|---|---|
| Theorem1.2 | COMPLETE: `theorem_1_2`, normalized g tends to1/2 |
| Theorem1.3 | COMPLETE: `theorem_1_3`, exact ceiling formula for every positive n |
| Theorem1.5 | COMPLETE: `theorem_1_5`, convergence and optimal-constant infimum identity |
| Theorem1.6 | Upper4/7 proved; lower9/17 remains UNPROVED |
| Theorem4.6 | COMPLETE: `FiniteHypergraph.transversal_four`, every finite3uniform H |
| Theorem5.3 | UNPROVED:17tau≤5n+3m for finite3uniform linearF7free H |

Definitions `Theorem_1_2`, etc. are specifications. The three corresponding
proof declarations above are actual kernel-checked theorems. There is no proof
of `Theorem_1_6` and no theorem assuming5.3 to disguise that missing dependency.

## Retry proof of Theorem4.6

The complete proof uses the finite hypergraph model already constructed:

1. Delete high-degree vertices, isolated vertices, isolated edges, and mixed
   degree-one/two edges. Exact transversal extension and cardinal accounting
   show a minimal counterexample must be two-regular.
2. Two edges meeting in two vertices also give a valid reduction, so the minimal
   counterexample is linear.
3. The incidence dual is a SIMPLE cubic graph. Original vertices give distinct
   dual two-element edges by linearity; dual edge count equals original n.
4. A maximum matching in any simple subcubic graph has at least one quarter
   of its edges. The formal proof excludes length-three augmenting paths,
   bounds external edges by twice the matching size, and double-counts degrees.
   It uses neither Shannon nor Vizing nor an assumed cycle theorem.
5. Pull back the matching to original vertices P, hitting exactly2|P| edges.
   Then tau+|P|≤m; incidence counting gives3m=2n and n≤4|P|, hence4tau≤n+m.
6. The hypothetical minimal counterexample is contradicted. No regularity or
   linearity hypothesis remains on the final theorem.

`MainExact.lean` uses4.6, APedge count and alpha+tau=n to prove the lower bound
for g, handles n=1 separately, combines it with `g_upper`, and transports the
unconditional ceiling-sequence limit to prove1.2. The ceiling is `(n+2)/2`, not
natural division `(n+1)/2`; n=0 is correctly excluded from1.3.

## Remaining obligations

* Prove Theorem5.3 in the actual `FiniteHypergraph` model:
 17tau(H)≤5|V(H)|+3|E(H)| under three-uniformity, linearity, and absence of the
 FIVE-edge F7 with edges012,034,056,135,246.
* Deduce9/17≤cStar using5.3 and the already verified AP bridges and optimal
 constant identity; then prove the full conjunction in Theorem1.6.
* Complete literal-all-assertions source review, including recalled historical
 inequality(1) and the explicit weak-Sidon nonlinearity witness if those
 ancillary literature statements are included in the scope.

The exact external source still needed is Henning–Yeo2021, *Affine Planes and
Transversals in3-Uniform Linear Hypergraphs*, DOI10.1007/s00373-021-02285-x,
Theorem7 and its internal lemmas. Its full proof was not accessible in this
session. New legitimate primary sources were obtained and selectively read,
but do not establish the required bound. See research/henning-retry.txt.
Consensus was invoked as requested but returned monthlysearchquotaexhausted;
no research thread or Consensus review was completed.

## Other verified development

Sections2–4 include the Sidon/(4,5)/weak implications, strict inclusions,
APfree equivalence, midpoint and edge bounds, linearity, affine invariance,
finite gluing including empty inputs, attained extrema, f/g subadditivity,
corrected Fekete applications, all construction uniqueness and APclassification,
and maximum Sidon size n+1. Section5 includes full real14point Lemma5.1,
F7avoidance Lemma5.2, and cStar≤4/7. The generic hypergraph machinery includes
attained alpha/tau, alpha+tau=n, and every AP correspondence used by the proofs.

The printed Fekete real-limit statement needs a bounded-below ratio hypothesis;
our applications prove nonnegativity and the zero-index subadditivity cases.

## Build, audit and reproduction

Pinned Lean:v4.35.0-rc4. Pinned Mathlib:
49fd9dee36e7bbf345fe7981d2de6aeeb591f75b.

Full current source closure: verification/build-round3.log.
All public theorem types/axioms: verification/AuditAll.lean and audit-round3.log.
Exact file hashes: verification/source-hashes-round3.json.
Independent mathematical/source review: research/retry-referee.txt.

Only propext, Classical.choice and Quot.sound occur in final theorem axiom
reports. No proof uses sorry, admit, new mathematical axioms, unsafe,
native_decide or Lean.ofReduceBool. Finite checks use decide+kernel.

On a normal elan installation run `lake update`, `lake exe cache get`, then
`bash scripts/check.sh`. The portable Lakefile pins the same Mathlib revision
that was used locally. A readlink compatibility shim was needed only on this
host; it did not alter Lean's compiler or kernel.

Independent agents checked the reduction, dual, matching, packing and exact
main-statement proofs. No novelty or registry verification is claimed.
The literature inventory records actual reading; a100paper review is not done.
Downloaded external PDFs and extracted fulltexts are not redistributed here.

## Palomar selection and statement boundary

`Challenge.lean` imports Mathlib only and contains explicit definitions and five
statements: Theorems1.2,1.3,1.5, upper1.6 and4.6. Its five deliberate proof holes
are statement placeholders, never imported by Solution. `Solution.lean` proves
the identical statements using this substantive development. The comparator
configuration permits only propext, Classical.choice and Quot.sound.

The original source logs are historical evidence for the pre-module checkpoint.
`verification/module-build.log` and `module-audit.log` record the current port;
`submission-audit.log` records the exact public compared theorem types/axioms.
A separate Palomar mechanical preflight is configured in GitHub Actions using
a pinned official reusable workflow. Local builds alone are not Palomar acceptance.

The formalization was produced by Codex agents under AItoBit's direction.
Independent AI agents reviewed the main proof chains; there has been no
independent human mathematical review. No novelty is claimed.
The repository snapshot is licensed Apache-2.0; cited papers retain their own
rights. The source-to-Lean correspondence is in research/coverage.tsv.
