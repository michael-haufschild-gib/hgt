# Universal-law-field stage-3 sweep ledger

Work list for full Lean certification and stage-3 promotion.  A card is `DONE` only when every
displayed theorem of the card is closed unconditionally in Lean, the modules are wired into
`GaloisForLFunctions.HTGeometry.UniversalLawField`, the axiom print is clean, and the paper card
has been moved into `docs/drafts/pipeline/3-formalized/universal-law-field/`.

| # | Card | Status |
|---|---|---|
| 1 | `amplified-generative-response-mechanics/amplified-admission-depth-escape-and-reduction-pencil-law.md` | HARD — needs the full intermediate k-positive reduction-map threshold |
| 2 | `beurling-cross-system-blindness-of-multiplicative-regularization-law.md` | NEEDS-LEAN — card flagged [NO LEAN]; corpus parent MultiplicativeRegularizationBlind.lean exists, necessity axiom N1 needs its own module |
| 3 | `c1-o-open-core-reduction-theorem.md` | NEEDS-LEAN — assembly card flagged [NO LEAN — user directive]; components are in-tree |
| 4 | `condensed-phase-probabilistic-death-modulus-budget-and-gaussian-fluctuation-law.md` | NEEDS-LEAN — audit which clauses already have modules |
| 5 | `critical-locus-hessian-classification-and-crystalline-transversality-law.md` | NEEDS-LEAN — theorem package Θ1, Θ2(i)-(v), Θ3.1-3.2 flagged [NO LEAN — user directive] |
| 6 | `eigen-pair-prime-identification-derivation.md` | PAPER-INCOMPLETE — card states D3–D6 open; only D1–D2 are derived, so full formalization is blocked on the paper proof |
| 7 | `failure-kernel-transversal-mechanics/nested-observer-hierarchical-maximal-coupling-face-law.md` | HARD — needs arbitrary finite-chain induction, full collision-stratum package, incompatible-partition countermodel |
| 8 | `finite-amplifier-width-cap-and-fejer-ratio-barrier-law.md` | NEEDS-LEAN — frame-level discharge of ULF-INV-4 open core |
| 9 | `formation-scale-mechanics/one-norm-impossibility-formal-receiver-collapse-and-wiener-scale-fusion-law.md` | OPEN — not yet audited in this sweep |
| 10 | `g-u-structure-admission-split-law.md` | NEEDS-LEAN — typing-grade split law flagged [NO LEAN — directive] |
| 11 | `generative-response-mechanics/centered-intervention-phase-gram-support-generation-law.md` | HARD — needs the coordinate-free spectral reduction of an arbitrary positive corank-one Gram face to diagonal gauge |
| 12 | `generative-response-mechanics/cofinal-generative-admission-gauge-and-three-cone-data-processing-law.md` | HARD — needs the full ell^1 closure identity and the Fourier uniqueness clause |
| 13 | `generative-response-mechanics/complex-time-exponential-generation-phase-recurrence-and-normalization-wall-law.md` | HARD — needs the countable Euler-shell identity (CTG.12) and its abscissa boundary |
| 14 | `generative-response-mechanics/fourier-kernel-admission-reconstruction-and-contact-localization-law.md` | HARD — needs the analytic finite-measure statements (FKA.6)-(FKA.23) |
| 15 | `genesis-termination-mechanics/compact-formation-depth-completion-exchange-and-observer-erasure-law.md` | HARD — needs section-6 calibrations 6.1 (compact system with nonempty boundary; discrete Kronecker density for an irrational rotation is missing from corpus and mathlib), 6.3 noncompact, 6.4 discontinuous, 6.5 depth-divergence-not-sufficient |
| 16 | `law-control-mechanics/abelian-zeta-gas-law-commutator-and-four-shadow-response-law.md` | IN PROGRESS — done: Thm 3.1 (LawCommutator), Thm 6.1/AZC.17 + chamber holomorphy + socle tail layer (SocleResponse), Thm 7.1 for the response (SocleHypertranscendence). Left: AZC.12 as an expectation, AZC.18 order bookkeeping, Thm 5.1 fugacity Jeffreys law, Thm 8.1 recurrence |
| 17 | `law-saturation-mechanics/bipolar-admission-hull-critical-shell-and-infinite-alternation-law.md` | HARD — needs: closed-hull least-closed-equivalence form, reporter intersection law, both realizability criteria, Dirac-TV response, bounded-alternation closedness, two-ended cofinal model |
| 18 | `local-exponential-test-closure-mechanics/local-exponential-complete-order-fusion-and-euler-shell-witness-escape-law.md` | HARD — no Lean written; needs a new LocalExponentialTestClosure module covering Theorems 2.1, 3.1, 3.2, 4.1, 4.2, 5.1, 6.1, 7.1 |
| 19 | `nonvacuous-independence-and-polarization-import-law.md` | BLOCKED-ON-PREREQ — quantitative core certified (SelbergSpectralParameter); the rest is citation-level and needs a hyperbolic-surface spectral layer (Laplace spectrum, Eisenstein series, Maass-Selberg truncation, Selberg trace formula and zeta) absent from mathlib and the corpus |
| 20 | `odd-coordinate-mechanism-universal-law-set.md` | NEEDS-LEAN — law set; Law 6 proved here |
| 21 | `parity-duality-rg-shell-splitting-and-multiplicative-resolution-cap-law.md` | NEEDS-LEAN — signed-sector and organ-scope law |
| 22 | `pole-purchase-escape-and-collision-gap-law.md` | NEEDS-LEAN — necessity axiom N6 and amplification-gap opening |
| 23 | `route-q-ratio-gate-decision.md` | BLOCKED-ON-NUMERICS — gate mechanism certified (DivisorHeightRatioGate: height damping, unconditional geometric decay, `9 < c` implies the gate); remaining inputs are gamma_1 > 9 (verified-zero computation) and a signed-moment lower bound (zero-location input) |
| 24 | `source-formation-harmonic-mechanics/bilateral-reflection-formation-energy-unitarity-selection-law.md` | CONCURRENT — written minutes ago by another session and marked [LEAN-FORMALIZED]; re-audit and promote once that session is idle |
| 25 | `source-formation-harmonic-mechanics/source-native-five-shadow-formation-fusion-and-selection-gate-law.md` | CONCURRENT — written minutes ago by another session and marked [LEAN-FORMALIZED]; re-audit and promote once that session is idle |
| 26 | `specification-consistency-polarization-independence-and-cusp-concentration-law.md` | NEEDS-LEAN — consistency and independence metatheorem for the inverse-theory axioms |
| 27 | `transverse-information-fusion-mechanics/prime-boolean-mass-hankel-recurrence-transverse-information-law.md` | OPEN — not yet audited in this sweep |
| 28 | `witt-formation-mechanics/conservative-inverse-completion-zero-exclusion-and-rh-selection-gate-law.md` | CONCURRENT — written minutes ago by another session and marked [LEAN-FORMALIZED]; re-audit and promote once that session is idle |

Completed and promoted:

- `pole-unit-formation-mechanics/pole-unit-scale-cocycle-correction-jet-reconstruction-and-divisor-memory-law.md` — 2026-08-11
- `complete-test-closure-mechanics/complete-atomic-fourier-hankel-order-and-inertia-fusion-law.md` — 2026-08-11
  (Theorem 5.1 closed by a new complex-Hermitian inertia layer: `HermitianInertia`,
  `CompleteAtomicInertiaFusion`; Theorems 3.1 and 4.1 also closed in concrete matrix form)

Cross-area findings during this sweep (not universal-law-field cards, recorded so they are not lost):

- `formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/SocleNoLimit.lean` does not elaborate and is
  not wired into any umbrella.  It is mathlib-drift damage, not an unfinished proof: one `linarith`
  needed `ratio_temperatureParameters` rewritten in the goal as well as the hypothesis (fixed here),
  and the remainder are `measurable_pi_apply … |>.natCast`, `isProbabilityMeasure_map`, and a
  `Finset.sum_mul` rewrite that no longer matches.  Repairing it is a drift task, not a card task.
- The lint gate also reports `HTGeometry.CriticalSchurIdealInertiaTransport`,
  `HTGeometry.EllipticGammaJetRealization` and `RHTower.XiMassRadialRiemannLebesgue` unreachable
  from their area umbrellas.  Those belong to another session's in-flight work; do not rewire them
  blind.
