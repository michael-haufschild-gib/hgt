# Recursive Stage-2 Lean certification sweep

- **Opened:** 2026-08-31
- **Scope:** every theorem card recursively below `docs/drafts/pipeline/2-fully-proven`, excluding
  ledgers, READMEs, and computation reports.
- **Baseline inventory:** 109 cards: 15 root; 3 constraint-relativity; 4
  nomological-geometry-and-dynamics; 6 Bottcher; 8 analytic-DA; 3 projective-geometry; 3
  RG/stochastic; 3 RH-zero-divisor; 64 universal-law-field.
- **Completion criterion:** exact dependency-closed theorem statement represented by an
  unconditional closed Lean theorem; targeted `lake env lean <file>` passes; public declarations'
  `#print axioms` contain no project axioms; targeted leaf `lake build <module>` passes; module is
  wired into its umbrella; card is moved to Stage 3.
- **Prohibited shortcuts:** no theorem weakening, no premise/hypothesis wrappers, no new axioms,
  no computation-backed proof, no heartbeat increases, no umbrella/full build.

## Search and audit discipline

- Every Lean-corpus lookup uses `scripts/formal_tools.py research "<query>"`.
- Mathlib names are checked in `/tmp` with `lake env lean` before use.
- Axiom checks are batched in `/tmp`; scratch files and owned Lean processes are removed after use.
- Existing successful checks are not repeated unless their source changes.

## Campaign status

| Cohort | Baseline | Certified and moved in this sweep | Remaining |
|---|---:|---:|---:|
| Root | 15 | 0 | 15 |
| Constraint relativity | 3 | 0 | 3 |
| Nomological geometry/dynamics | 4 | 0 | 4 |
| Bottcher complex dynamics | 6 | 0 | 6 |
| Analytic DA entire functions | 8 | 0 | 8 |
| HT/projective geometry | 3 | 0 | 3 |
| RG/stochastic fields | 3 | 0 | 3 |
| RH-zero-divisor geometry | 3 | 0 | 3 |
| Universal Law Field | 64 | 11 | 53 |
| **Total** | **109** | **11** | **98** |

## Closed prerequisite work during sweep

- Exact Matomaki--Teravainen Lemma 3.4, including published refinement, is closed by
  `HeathBrownSparseMeanValueBounded`, `HeathBrownSparseMeanValueBoundedRefined`, and
  `HeathBrownSparseMeanValueLemma34`. Direct checks, batched axiom audit, leaf builds, and
  `RHTower` wiring pass. This advances the two Route-E cards but does not finish them: genuine
  Lemma 3.5 Type I/Type I-II cancellation, routing/amplification, and final theorem remain.

## Active queue

1. Promote current Stage-2 cards already claiming exact Lean certification, after statement,
   axiom, leaf-build, and umbrella audit.
2. Finish the nine originally named root cards, sharing infrastructure where their exact theorems
   overlap.
3. Clear remaining root, constraint, nomological, and historical-corpus cards.
4. Clear all 64 Universal Law Field cards using the existing ULF sweep ledgers as evidence only;
   each current card still receives an individual exact-statement audit.

## Log

- 2026-08-31 — Baseline recursive inventory fixed at 109 cards; certification criteria and cohort
  accounting recorded.
- 2026-08-31 — ULF-TAFM-26 promoted after adding exact compact graph-load image properness, grade
  reconstruction from resolvent and Gibbs mass, compatibility laws, umbrella wiring, leaf build,
  and axiom audit.
- 2026-08-31 — ULF-TAFM-25 promoted after adding Laurent-derivative uniqueness, literal
  `I^r`-membership infrastructure, arbitrary-member reflection compatibility, joint-grade
  certificate, umbrella wiring, leaf build, and axiom audit.
- 2026-08-31 — ULF-TAFM-27 promoted after closing exact sign-sensitive transgression,
  primitive-factor uniqueness, logarithmic reconstruction, primewise valuation, exponential
  half-density, and actual finite-adele lattice sum/intersection laws; direct checks, both leaf
  builds, umbrella wiring, and new-declaration axiom audit pass.
- 2026-09-01 — ULF-TAFM-24 promoted after proving the exact augmentation-boundary annihilator,
  genuine degree-bounded polynomial-clock classification, coefficient-`ℓ¹` response/minimal-order
  theorem, and reflected first-grade winding reversal; direct check, completion leaf build,
  umbrella wiring, and new-declaration axiom audit pass.
- 2026-09-01 — ULF-TAFM-18 duplicate Stage2 paper card consolidated into its pre-existing Stage3
  record after making functional-equation reflection as constant local gauge and global-reflection
  holonomy invariance explicit, adding universal/literal zero-argument certificates, direct checks,
  leaf builds, umbrella wiring, and new-declaration axiom audit.
- 2026-09-01 — ULF-TAFM-19 duplicate Stage2 paper card consolidated into its pre-existing Stage3
  record after adding exact source reconstruction, clock identity/inverse laws, explicit absolute
  summability, universal/literal zero-argument certificates, direct checks, leaf builds, umbrella
  wiring, and new-declaration axiom audit.
- 2026-09-01 — ULF-TAFM-20 duplicate Stage2 paper card consolidated into its pre-existing Stage3
  record after closing exact fixed-probe boundedness/properness and escape equivalences, adding
  generic/literal zero-argument certificates, direct checks, one targeted literal leaf build,
  umbrella wiring, and new-declaration axiom audit.
- 2026-09-01 — ULF-TAFM-21 duplicate Stage2 paper card consolidated into its pre-existing Stage3
  record after making exact projection images/complement and constant-clock diagonal gauge explicit,
  adding one full zero-argument certificate, passing scratch/direct checks and targeted leaf build,
  retaining existing universal-field umbrella wiring, and auditing new declaration axioms.
- 2026-09-01 — ULF-TAFM-22 duplicate Stage2 paper card consolidated into its pre-existing Stage3
  record after closing generic polar depth reconstruction, completed-function ratio reflection,
  and exact logarithmic radical quotient; adding generic/arithmetic zero-argument certificates;
  passing scratch/direct checks and targeted leaf build; retaining existing umbrella wiring; and
  auditing new declaration axioms.
- 2026-09-01 — ULF-TAFM-23 promoted after closing complete affine-gauge classification, explicit
  unit quadrupoles, exact `ℓ¹(Fin 2 ⊕ ℕ)` sum-norm completion, dense finite chart, extension iff
  bounded curvature, exact dual norm, literal first-difference escape, uniform curvature,
  zeroth-source-jet convergence, and normalized source estimate. Direct elaboration, targeted leaf
  build, both umbrella wires, and eight capstone axiom audits pass. Open source estimate `(OJ.31)`
  remains explicitly open; only its already-proved implication to RH is certified.
- 2026-09-01 — ULF-TAFM-5 promoted after closing `(GRA.15)`--`(GRA.22)`: exact source-price/action
  sandwich, tensor Hellinger admission, geometric-mean factor localization, deterministic
  bounded-Lipschitz pullback equality, genuine binary prefix ultrametrics, exact discrete and
  inherited projection costs, literal Bernoulli Neyman--Pearson detector costs, unchanged source
  cylinder, and hypothesis-free half-ratio transfer certificate. Direct elaboration, one targeted
  leaf build, universal-field umbrella wiring, and seven capstone axiom audits pass. Open arithmetic
  producer `(GRA.23)` remains explicitly unasserted.
