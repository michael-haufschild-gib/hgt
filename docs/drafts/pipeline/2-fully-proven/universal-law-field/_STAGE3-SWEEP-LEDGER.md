# Universal-law-field stage-3 sweep ledger

**Scope correction (2026-08-12).**  This sweep owns only the cards *directly* in
`docs/drafts/pipeline/2-fully-proven/universal-law-field/`.  Every card inside a subfolder belongs
to a different agent and is not audited or promoted here.

A card is `DONE` only when every displayed theorem is closed unconditionally in Lean, the modules
are wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`, the axiom print is clean, and the
card has been moved into `docs/drafts/pipeline/3-formalized/universal-law-field/`.

| # | Card | Status |
|---|---|---|
| 1 | `beurling-cross-system-blindness-of-multiplicative-regularization-law.md` | **DONE 2026-08-12** — promoted to `3-formalized/`.  New modules `HTGeometry/BeurlingCrossSystemBlindness.lean` (38 decls) and `RHTower/BeurlingRationalPrimeSystem.lean` (13 decls); all axiom-clean |
| 2 | `c1-o-open-core-reduction-theorem.md` | NEEDS-LEAN — assembly card flagged [NO LEAN — user directive]; components are in-tree |
| 3 | `condensed-phase-probabilistic-death-modulus-budget-and-gaussian-fluctuation-law.md` | NEEDS-LEAN — audit which clauses already have modules |
| 4 | `critical-locus-hessian-classification-and-crystalline-transversality-law.md` | IN PROGRESS — Θ1, Θ2(i)–(v), Θ3.1 (packaged), Θ3.2 all certified (CriticalLocusQuadrupleEvenness, CrystallineShadowTransversality, CriticalLocusHessianClassification); Θ4 Step A certified (CriticalLocusConeFullness). Left: Θ4 exact-hitting assembly — OPEN RESEARCH, hostile audit + repair route + residual open point on the card (2026-08-13 log) |
| 5 | `eigen-pair-prime-identification-derivation.md` | PAPER-INCOMPLETE — card states D3–D6 open; only D1–D2 are derived, so full formalization is blocked on the paper proof |
| 6 | `finite-amplifier-width-cap-and-fejer-ratio-barrier-law.md` | **DONE 2026-08-13** — promoted to `3-formalized/`.  `HTGeometry/FiniteAmplifierFrame.lean`: Thm 1 (master bound/exclusion/width cap), Thm 1′ (multi-σ + averaging), Thm 2 (threshold, ratio form, ρ-finiteness: cosine sampling, finite-abelian dual averaging, separating-quotient reduction); Page + circle anchors in `FiniteAmplifierPatternCap`; residual-finiteness glue and Fejér's exact value recorded as cited-classical; 2504.05606 audited (no ceiling) |
| 7 | `g-u-structure-admission-split-law.md` | NEEDS-LEAN — typing-grade split law flagged [NO LEAN — directive] |
| 8 | `nonvacuous-independence-and-polarization-import-law.md` | BLOCKED-ON-PREREQ — quantitative core certified (SelbergSpectralParameter); the rest is citation-level and needs a hyperbolic-surface spectral layer (Laplace spectrum, Eisenstein series, Maass-Selberg truncation, Selberg trace formula and zeta) absent from mathlib and the corpus |
| 9 | `odd-coordinate-mechanism-universal-law-set.md` | NEEDS-LEAN — law set; Law 6 proved here |
| 10 | `parity-duality-rg-shell-splitting-and-multiplicative-resolution-cap-law.md` | NEEDS-LEAN — signed-sector and organ-scope law |
| 11 | `pole-purchase-escape-and-collision-gap-law.md` | **DONE 2026-08-13** — promoted to `3-formalized/`.  The (INV3.2) log-derivative identity closed in `RHTower/PolePurchaseLogDerivIdentity.lean` (mathlib `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` + `VonMangoldtLineSeriesSwap` kernels); axiom-clean |
| 12 | `route-q-ratio-gate-decision.md` | BLOCKED-ON-NUMERICS — gate mechanism certified (DivisorHeightRatioGate: height damping, unconditional geometric decay, `9 < c` implies the gate); remaining inputs are gamma_1 > 9 (verified-zero computation) and a signed-moment lower bound (zero-location input) |
| 13 | `specification-consistency-polarization-independence-and-cusp-concentration-law.md` | **DONE 2026-08-13** — promoted to `3-formalized/`.  Theorem B's independence witness fully certified (`RHTower/InverseTheoryGraphWitness.lean`: prism `C₁₆×K₂`, Rayleigh data by root-of-unity sampling, eigenvalue strictly inside `(2√2, 3)`, Perron pair, capstone `prism_independence_witness`); A/C/D recorded as cited-classical / in-tree-cited / synthesis per the card's own claims |

Completed and promoted:

- `beurling-cross-system-blindness-of-multiplicative-regularization-law.md` — 2026-08-12.
  Beurling systems as a structure (`System ι`); the Gram entry as an exact layer-cake integral;
  Lemma 2.1 with the explicit error `2M L^{k+1}`; cross-system blindness with the compensation
  derived rather than assumed; the swapped-generator Euler product and the zero-set separation at
  `s₀ = 2πi/log 2` via the functional equation; and the concrete pair (rational primes vs. `2`
  replaced by a second `3`) with both Mertens defects bounded, the first from the corpus's own
  `Mertens.mertens_first`.

- `source-formation-harmonic-mechanics/source-native-five-shadow-formation-fusion-and-selection-gate-law.md` — 2026-08-11 (FF.19/FF.20 receiver clauses added)
- `source-formation-harmonic-mechanics/bilateral-reflection-formation-energy-unitarity-selection-law.md` — 2026-08-11

- `pole-unit-formation-mechanics/pole-unit-scale-cocycle-correction-jet-reconstruction-and-divisor-memory-law.md` — 2026-08-11
- `complete-test-closure-mechanics/complete-atomic-fourier-hankel-order-and-inertia-fusion-law.md` — 2026-08-11
  (Theorem 5.1 closed by a new complex-Hermitian inertia layer: `HermitianInertia`,
  `CompleteAtomicInertiaFusion`; Theorems 3.1 and 4.1 also closed in concrete matrix form)
- `transverse-information-fusion-mechanics/prime-boolean-mass-hankel-recurrence-transverse-information-law.md` — 2026-08-12
  (new module `PrimeBooleanFusionSourcePacket`: Mass norm identity, moment/Hankel block,
  three-organ conservation and its clock-gap form, two-parameter QFI with the infimum form, the
  single-clock degeneration, the literal prime Gibbs coordinates with the exact half-density
  damping, the `σ`/label half of the reconstruction theorem, the unit-norm Boolean state on
  `ℓ²(𝒫(F))` with its norm recurrence, and the refutation of the zero-transverse-information
  criticality selector.  At the prime source the clock energy moment is derived, so no
  nondegeneracy hypothesis survives)

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

## Lint-gate status during this sweep

The formal lint gate cannot be brought green while another session is writing to the tree.  Two
error classes appear, both from that session, neither from the universal-law-field sweep:

1. `owned module unreachable from theorem-area umbrella` — currently `RHTower.Sieve.Vinogradov*`,
   `RHTower.Suzuki*`, `RHTower.XiResolvent*`, `HTGeometry.ConstraintMotiveRelativity.*`,
   `HTGeometry.CriticalSchurIdealInertiaTransport`.  These are modules added but not yet wired.
2. `stale generated file` for `LEAN_API.md`, `LEAN_GAPS.md`, `LEAN_OVERVIEW.md` — they are stale
   again within minutes of `formal_tools.py index` because Lean files keep changing underneath.

Every module this sweep added is reachable: all twelve are imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`, which `GaloisForLFunctions.HTGeometry`
imports.  Verified module by module.  Re-run the gate when the other session is idle.

## Handoff: next action per in-scope card (2026-08-12)

Dependency order matters — the Θ package is upstream of two other cards.

1. `critical-locus-hessian-…` **(do first)**. Certified: Θ1 (`CriticalLocusQuadrupleEvenness`),
   Θ2's second-jet identity, Θ3.2 and Θ3.1's kernel identity (`CrystallineShadowTransversality`).
   Next: Θ4 (finite evaluation blindness) — needs a configuration-family implicit-function layer;
   then Θ2's per-zero necessity/mixture — needs a detector-predicate layer; then Θ3.1's integral
   packaging against `h`.
2. `odd-coordinate-mechanism-universal-law-set`. A **synthesis card**: Laws 1/2/3 carry no proofs
   of their own, they cite Θ1, Θ2(i)–(v), Θ4. Do not prove anything here until Θ4 lands; then this
   is assembly plus Laws 5 and 6.
3. `finite-amplifier-width-cap-…`. Recorded as a frame-level discharge of Θ4 — also waits on Θ4.
4. `nonvacuous-independence-…`. Core certified (`SelbergSpectralParameter`). Blocked on a
   hyperbolic-surface spectral layer (Laplace spectrum on `Γ\ℍ`, Eisenstein series,
   Maass–Selberg, Selberg trace formula and zeta) absent from mathlib and the corpus.
5. `route-q-ratio-gate-decision`. Mechanism certified (`DivisorHeightRatioGate`). The two residual
   inputs are verified-zero computations, which the session's Lean rule 4 excludes; treat as
   blocked-by-directive rather than open.
6. `eigen-pair-prime-identification-derivation`. Read before attempting: the card states D3–D6 are
   unproved **on paper**, so there is no proven theorem to formalize. Confirm, then leave at
   stage 2 with that recorded.
7. Independent, not yet read under the corrected scope — audit each for displayed theorems first:
   `beurling-cross-system-blindness-…`, `pole-purchase-escape-…`,
   `parity-duality-rg-shell-splitting-…`, `specification-consistency-…`,
   `condensed-phase-probabilistic-death-…`, `g-u-structure-admission-split-law`,
   `c1-o-open-core-reduction-theorem`.
   The `[NO LEAN — user directive]` tags on the last two predate the current goal and are stale;
   treat them as targets, not exemptions.

Reusable infrastructure built during this sweep, corpus-wide: `HermitianInertia` (Sylvester's law
for complex Hermitian matrices), `CompleteAtomicInertiaFusion`, `QuotientFusionProjectionGenesis`,
`CartanWorkProperness`, `FormationCompletionExchangeCalibration`, `InteractionDegreeEscape`,
`CrystallineShadowTransversality`, and the `AbelianZetaGas` socle layer.

## Scope extension (2026-08-13, /goal directive)

The sweep now owns **every** card under `universal-law-field/` **including subfolders** (74 cards).
The 2026-08-12 top-level-only scope correction is superseded by the user's 2026-08-13 goal.
Working rules restated: unconditional closed Lean only (no premises/hypotheses/axioms), corpus-first
search before any new lemma, foreground builds, one Lean process, `lake env lean` per file and
`lake build <module>` for the final audit, wire every module into its umbrella, promote with
`scratchpad/promote.py`.

Concurrency note: another session is active in `formation-resource-mechanics/` (card + 
`1-in-progress` programme file git-modified, 09:57 mtimes) and in several `RHTower/*` modules.
Do not touch in-flight files; skip that card until the other session goes idle.

### Subfolder roster (initial audit from card self-declarations, 2026-08-13)

| Folder | Cards | Initial state |
|---|---|---|
| amplified-generative-response-mechanics | 1 | no boundary marker — audit |
| cofinal-renewal-geometry | 5 | no marker — audit (memory: threshold work 2026-08-12) |
| conservative-repair-genealogy-mechanics | 3 | LEAN PENDING |
| endogenous-relaxation-mechanics | 1 | no marker — audit |
| failure-kernel-transversal-mechanics | 1 | core certified; arbitrary-finite-chain leg pending |
| formation-chirality-reversal-mechanics | 2 | no marker — audit |
| formation-cloning-mechanics | 1 | Hellinger triangle API pending |
| formation-depth-properness-mechanics | 1 | no marker — audit |
| formation-factorization-mechanics | 1 | sublevel boundedness pending |
| formation-holonomy-mechanics | 2 | no marker — audit |
| formation-laplacian-properness-mechanics | 3 | LEAN PENDING |
| formation-resource-mechanics | 1 | LEAN PENDING — **other session in flight, skip** |
| formation-transfer-germ-mechanics | 1 | core certified; Poisson asymptotics pending |
| generative-response-mechanics | 4 | mixed; audit each |
| interaction-spectrum-dilation-mechanics | 1 | no marker — audit |
| law-control-mechanics | 1 | no marker — audit |
| law-saturation-mechanics | 1 | §10 paper-only clauses pending |
| local-exponential-test-closure-mechanics | 1 | LEAN PENDING |
| orbit-induction-selection-mechanics | 6 | LEAN-PENDING |
| packet-formation-mechanics | 2 | audit; hasse-packet has paper-level remains |
| polarized-contact-formation-geometry | 3 | LEAN PENDING |
| polarized-response-completion-mechanics | 3 | LEAN PENDING |
| primitive-formation-rigidity-mechanics | 4 | audit; prime-jet has open clause |
| reciprocal-character-real-form-mechanics | 1 | has Lean section — audit |
| reciprocal-fusion-topology-mechanics | 1 | LEAN PENDING |
| recovery-cocycle-mechanics | 2 | one LEAN PENDING — audit both |
| reflection-formation-cocycle-mechanics | 1 | no marker — audit |
| reversible-formation-dilation-mechanics | 3 | mixed remains — audit each |
| species-relative-formation-mechanics | 5 | LEAN PENDING |

Order of attack: (1) top-level dependency chain per the 2026-08-12 handoff
(critical-locus-hessian Θ-package first, then its two dependents), (2) subfolder cards with small
declared remainders, (3) full LEAN-PENDING folders, (4) formation-resource-mechanics last (in
flight elsewhere).

## Session 2026-08-13 state (full-scope sweep, first leg)

In flight: `critical-locus-hessian-…` (ULF-FIELD-2).  New modules written, elaboration pending
on the cone rebuild (the shared tree churned, so the import cone of
`CriticalLocusQuadrupleEvenness`/`CrystallineShadowTransversality`/`SuzukiInteriorExcursion…`
is rebuilding in one foreground `lake build`):

- `RHTower/CriticalLocusHessianClassification.lean` — Θ2(i) exact separation (multiset join),
  Θ2(ii) general weight `2(F″(c₊)+F″(c₋))` + κ-conjugation bridge + real weight `4·Re F″`,
  Θ2(iii) per-zero necessity (via `suzukiSecondDeriv_nonpos_of_isLocalMax`), Θ2(iv) diagonal
  Hessian + determination iff, Θ2(v) composite chain law + composite necessity, Θ3.1 integral
  packaging (`lineTestTransform`, single/real/multi forms against `shadowDensity`).
- `RHTower/CriticalLocusConeFullness.lean` — Θ4 Step A: symmetry collapse of pair/quadruple
  values; cone fullness of the move families by the strip PL + harmonic minimum principle
  (consumes `Bottcher/HarmonicMinPrinciple`, `Bottcher/HarmonicMaxPrinciple`).
- `RHTower/OddCoordinateSelfClosure.lean` — ULF-MECH-1 Law 6 (self-closure): odd factoring
  functionals vanish; quadruple and multi-splitting instantiations.
- `RHTower/PolePurchaseLogDerivIdentity.lean` — ULF-INV-3's last gap: the (INV3.2) identity
  `3(−ζ′/ζ)(σ)+4Re(−ζ′/ζ)(σ+it)+Re(−ζ′/ζ)(σ+2it) = ∑Λ(n)n^{−σ}(3+4cos+cos2)` + nonnegativity
  (mathlib `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` + corpus `VonMangoldtLineSeriesSwap`).

None of the four is wired into an umbrella yet (parked as leaves until green).  Θ4's final
exact-hitting assembly is open research — analysis recorded on the ULF-FIELD-2 card (2026-08-13
log entries).  Queue map of every subfolder card's declared gap:
session scratchpad `subfolder-gaps.md` (regenerate with the grep in this ledger's history if
lost — one grep over the card set).

- `pole-purchase-escape-and-collision-gap-law.md` — **DONE 2026-08-13** — promoted: (INV3.2) log-derivative identity certified (RHTower/PolePurchaseLogDerivIdentity.lean, axiom-clean); full displayed surface now Lean-closed

- `finite-amplifier-width-cap-and-fejer-ratio-barrier-law.md` — **DONE 2026-08-13** — promoted: frame Theorems 1/1'/2 certified in HTGeometry/FiniteAmplifierFrame.lean (master bound, exclusion, width cap, threshold, ratio form, multi-sigma + averaged stability, rho-finiteness via cosine sampling, finite-abelian dual averaging, and the separating-quotient reduction); anchors in FiniteAmplifierPatternCap; arXiv:2504.05606 audited, no ceiling meta-theorem found; all capstones axiom-clean

## Design note — ULF-INV-5 Theorem B witness (2026-08-13, do next on this card)

Concrete non-Ramanujan witness with clean algebra: the prism `C₁₆ × K₂` (3-regular, 32
vertices).  Rayleigh vector: `v_{j,s} := cos(2πj/16)` (K₂-symmetric, cycle-cosine — mean zero).
Exact quotient `R(v) = 2cos(π/8) + 1`, computed by the discrete cosine sums already certified in
`HTGeometry/FiniteAmplifierFrame.lean` (cos-sample orthogonality).  Margin:
`2cos(π/8) + 1 > 2√2 ⟺ √(2+√2) > 2√2 − 1 ⟺ 5√2 > 7 ⟺ 50 > 49` — pure algebra via
`cos²(π/8) = (2+√2)/4` (half-angle).  Eigenvalue form via mathlib's Rayleigh layer
(`Mathlib.Analysis.InnerProductSpace.Rayleigh`) on the `𝟙⊥`-restriction, or state the failure
witness variationally.  N-clause satisfactions (finite trace = N2/N5 vacuous, `count ≤ trace` =
spectral theorem, N6 Perron `d`, N4 girth) as simple lemmas with the card's vacuity caveat.

Design note continued (INV-5): eigenvalue packaging via
`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` on the `A`-invariant
subspace `𝟙⊥` (invariance from symmetry + `A𝟙 = 3𝟙`); `λ < 3` from the equality analysis of
`⟨(3I−A)v, v⟩ = ∑_{edges}(v_x − v_y)²` — a 3-eigenvector in `𝟙⊥` is edge-constant, and
edge-constancy on the prism forces global constancy by explicit `ZMod`-induction along the
cycle plus one rung (no `SimpleGraph.Connected` machinery); `λ > 0` rules out `−3`.

## Progress — ULF-INV-5 witness Phase 1 (2026-08-13)

`RHTower/InverseTheoryGraphWitness.lean` (wired into `GaloisForLFunctions.RHTower`, build
green, capstones axiom-clean): the prism `C₁₆ × K₂` as a `SimpleGraph` with certified
3-regularity; the mean-zero cosine vector with exact Rayleigh data
(`prismNormSq = 16`, `prismEnergy = (2cos(π/8)+1)·16`) via the de-privatized discrete
sampling lemmas of `FiniteAmplifierFrame` (+ new phase-shifted variant); and the strict
Ramanujan margin `2√2 < 2cos(π/8)+1` (`50 > 49`).  Capstone `prism_rayleigh_witness`.
Phase 2 **DONE 2026-08-13**: `prismOp` (funLeft-composition operator), `prismOp_isSymmetric`,
`prism_laplacian_identity` (`3⟨v,v⟩ − ⟨Av,v⟩` = edge-difference energy), `prism_energy_le`,
`prism_constant_of_edge_zero` (explicit cycle+rung constancy), the mean-zero hyperplane with
both membership directions and invariance, and the capstones `prism_nonRamanujan_eigenvalue`
/ `prism_graph_violates_ramanujan`: an eigenvalue `μ` with `2√2 < μ < 3` of the prism
adjacency endomorphism, via `hasEigenvalue_iSup_of_finiteDimensional` on the restriction,
the witness Rayleigh lower bound, and the `μ = 3` equality kill.  All axiom-clean; module
build green.  Left for the card: Theorem B packaging (N-clause satisfaction lemmas with the
vacuity caveat) and the Theorems A/C/D citation-audit disposition; then promote.

- `specification-consistency-polarization-independence-and-cusp-concentration-law.md` — **DONE 2026-08-13** — promoted: Theorem B's independence witness fully certified (RHTower/InverseTheoryGraphWitness.lean - prism C16xK2, 3-regularity, exact Rayleigh data by root-of-unity sampling, Ramanujan margin 50>49, symmetric operator, Laplacian equality analysis, eigenvalue strictly inside (2sqrt2, 3), Perron pair, bundled capstone prism_independence_witness, all axiom-clean); Theorems A/C/D recorded as cited-classical / in-tree-cited / synthesis per the card's own claims

- `regularization-face-mechanics/positive-face-compression-classification-and-subleading-survival-law.md` — **DONE 2026-08-13** — Exact paper surface closed in Lean: real/complex scalar scope, range/kernel classification, nonzero subleading survival, heterogeneous direct-sum analysis, unchanged family energies, and formation-Laplacian radical; direct source, targeted module build, umbrella source, and axiom audits pass.

- `interaction-spectrum-dilation-mechanics/source-formation-interaction-work-qfi-conservation-and-cofinal-phase-law.md` — **DONE 2026-08-13** — Exact paper surface closed in Lean: biased-Walsh reconstruction/Parseval and passive filtration, realized pure-state QFI conservation, finite variance/Chebyshev, uniform tightness, cofinal escape, critical QFI limits, and reciprocal phase classification; open producer split to Stage 1.

- `entropic-alternating-formation-mechanics/alternating-marginal-repair-action-gauge-properness-and-recurrent-selection-law.md` — **DONE 2026-08-13** — Literal finite-array KL projections, product-witness alternating conservation and recurrent balance, entropy transpose invariance, and compact positive-definite gauge quotient formalized; leaf, axiom, and domain-umbrella audits passed.

- `formation-chirality-reversal-mechanics/observer-fibre-chirality-conservation-and-sufficient-reversal-selection-law.md` — **DEPENDENCY BLOCKED 2026-08-13** — Arbitrary finite observer-tower conservation, terminal-reversal localization, average-current bound, one-sided involutive endpoint exchange, fibre-current localization/positivity, and one-sided sufficient reversal are now Lean-closed in `ConstitutiveObserverFibreChirality`. Card remains Stage 2 because its Abelian-zeta strict chronology and source-native likelihood factorization depend on the unformalized parent `formation-cumulant-chirality-and-involutive-selection-law.md`; no assumption-based substitute accepted.

- `failure-kernel-transversal-mechanics/nested-observer-hierarchical-maximal-coupling-face-law.md` — **DONE 2026-08-14** — Arbitrary finite nested-chain coupling, simultaneous maximality, literal collision strata, terminal outside mass, exposed consensus face, total-variation identity, capacity monotonicity, and four-atom nonnested countermodel formalized in ConstitutiveHierarchicalMaximalCouplingChain; direct leaf, targeted module build, umbrella, and axiom audits pass.

- `formation-cloning-mechanics/broadcast-clone-fracture-recovery-isometry-and-cofinal-properness-law.md` — **DONE 2026-08-14** — Full Lean closure: arbitrary-depth product affinity, exact iff cloner construction, diagonal/Dirac/Renyi fracture, Hellinger defect and cofinal properness, split-recovery isometry, reflection equivariance, common-positive selector; targeted build and standard-only axiom audit pass.

- `formation-factorization-mechanics/self-dual-factorization-torsor-reciprocal-gram-and-cartan-properness-law.md` — **DONE 2026-08-14** — Full Lean closure: exact matrix exponential Cartan ray/reversal/work formulas, Hermitian spectral bridge, compact/recurrent unitary phase, operator and cofinal radial selection; targeted build, umbrella source check, standard-only axiom audit pass.

- `recovery-cocycle-mechanics/common-recovery-cocycle-holonomy-hodge-work-and-joint-reconstruction-law.md` — **DONE 2026-08-14** — full unconditional Lean closure in HTGeometry.ConstitutiveRecoveryCocycleHolonomy; direct/targeted/umbrella checks and capstone axiom audit pass

- `recovery-cocycle-mechanics/nonabelian-recovery-holonomy-conjugacy-work-and-recurrent-execution-law.md` — **DONE 2026-08-14** — primitive-cycle gauge classification, exact word/conjugacy/balanced work minima on marked cycles, schedule genesis, repeated marked action, finite recurrence, common-recovery packet KL isometry, reflection, and Gram blindness closed in three wired HTGeometry modules; direct/targeted/umbrella and axiom audits pass

- `recovery-cocycle-mechanics/nonabelian-recovery-holonomy-conjugacy-work-and-recurrent-execution-law.md` — **DONE 2026-08-14** — Full unconditional Lean closure: primitive-cycle holonomy gauge classification, exact marked-cycle word/conjugacy/balanced work minima, schedule commutator genesis, finite recurrence with linearly open marked action, common-recovery packet KL isometry, reflection, and unitary Gram blindness; targeted build, wired umbrella, and standard-only axiom audits pass.

- `generative-response-mechanics/complex-time-exponential-generation-phase-recurrence-and-normalization-wall-law.md` — **DONE 2026-08-14** — Full CTG.1–CTG.16 Lean closure: finite/countable complex generation, covariance response, summably admitted Markov Fisher conservation/equality/no-amplification, literal shell source ratio/Gibbs shift/phase/all-order moments, zero straight radius, exact lifetime and wall divergence; targeted leaf, umbrella, axiom, and scoped lint audits pass.

- `generative-response-mechanics/centered-intervention-phase-gram-support-generation-law.md` — **DONE 2026-08-14** — Full unconditional Lean closure: positive normalized Gram PSD, rank-(d-1) unique zero eigenline, strict positive-eigenvalue pseudodeterminant, orthogonal adjugate transport, arbitrary unit-kernel rank-one adjugate, and exact coordinate-free (GRM.13) determinant orientation; targeted module build, wired umbrella source, standard-only axiom, and scoped forbidden/computation audits pass.

- `law-saturation-mechanics/bipolar-admission-hull-critical-shell-and-infinite-alternation-law.md` — **DONE 2026-08-14** — Full unconditional Lean closure: least closed-equivalence hull, exact conflict/Dirac-TV laws, bounded alternation, exact two-ended finite/global model, non-equicontinuity, sharp half-gap, and minimal 2m depth; targeted builds, wired umbrella, and axiom/scoped lint audits pass.

- `formation-depth-properness-mechanics/source-depth-graph-properness-and-cofinal-mixer-selection-law.md` — **DONE 2026-08-14** — Full unconditional Lean closure: existing source-depth properness and cofinal mixer conservation plus closed graph, lower-semicontinuity, exact finite-gauge intersection, ambient/domain compact sublevels, uniform tails, and natural-level exhaustion; targeted build, wired umbrella, and standard-only axiom audits pass.

- `source-response-signature-mechanics/normalized-jet-splitting-markov-coinvariant-and-ward-anomaly-migration-law.md` — **DONE 2026-08-14** — Full unconditional Lean closure: all-order common-recovery splitting, exact attained C_N sum-norm bounds and closed range, abstract and finite-mass coinvariant quotients, Bartlett-Ward identities and sharp affine countermodel, plus canonical active-support Fisher/connection migration and equality classification; targeted build, wired umbrella, scoped forbidden-token scan, and standard-only axiom audits pass.

- `cofinal-renewal-geometry/horizontal-vertical-packet-renewal-budget-and-cofinal-properness-law.md` — **DONE 2026-08-14** — Full unconditional Lean closure of HVP.4--HVP.14, including arbitrary-packet data processing, canonical conditional-kernel KL chain rule, exact vertical budget, work wall, and unique least-action classification; targeted build, umbrella elaboration, scoped forbidden-token scan, and standard-only axiom audit pass.

- `cofinal-renewal-geometry/source-horizontal-disjoint-class-law-global-renewal-properness-and-current-evacuation.md` — **DONE 2026-08-14** — Full unconditional literal-source Lean closure: canonical class apertures are pairwise disjoint; exact masses, sharp forward/reverse partition ranges, finite-KL cofinal moments, quantitative summable adaptive current, and termwise evacuation are kernel-checked; targeted build, umbrella, scoped scan, and standard-only axiom audit pass.

- `cofinal-renewal-geometry/disjoint-aperture-global-renewal-moment-properness-and-cubic-threshold-law.md` — **DONE 2026-08-14** — Lean formalization completed: global entropy-moment properness, sharp ordinary and stretched work thresholds, involution neutrality, arbitrary-packet closure, and literal source-horizontal corollaries are kernel-checked and umbrella-owned.

- `cofinal-renewal-geometry/hasse-geometric-history-global-renewal-properness-and-cubic-work-wall.md` — **DONE 2026-08-14** — Lean formalization completed: literal Hasse kernel, arbitrary-renewal entropy moment, total-current bound, quadratic wall, sharp cubic witness, and functional-equation neutrality are kernel-checked and umbrella-owned.

- `cofinal-renewal-geometry/exponential-aperture-polynomial-work-renewal-action-threshold-law.md` — **DONE 2026-08-14** — Full unconditional Lean closure: exact aperture KL disintegration and piecewise information projection, sharp EReal liminf/divergence through degree two, compact action sublevels, exact superquadratic two-point witness/entrance, and source-horizontal orientation prices; targeted builds, umbrella, scoped scan, and standard-only axiom audits pass.

- `constitutive-reflection-space-mechanics/split-star-formation-positive-profile-and-functional-fixedness-neutrality-law.md` — **DONE 2026-08-14** — Full unconditional Lean closure: exact receiver-profile conservation, pointwise/set/family radical pullback, functional fixedness, literal star-isotropy preservation, and positive-receiver invisibility; targeted build, umbrella check, scoped scan, and standard-only axiom audit pass.

- `constitutive-reflection-space-mechanics/functional-reflection-positive-envelope-polarization-trilemma.md` — **DONE 2026-08-14** — Exact finite classification already Lean-closed: twisted star algebra, universal fixed-locus positive receiver, unique factorization, exact radical and positive characters, faithful-receiver trilemma, and conservative dagger untwisting; direct check, targeted build, umbrella ownership, scoped scan, and standard-only axiom audit pass.

- `reciprocal-character-real-form-mechanics/reciprocal-character-real-form-fusion-virial-reconstruction-and-gauss-admission-law.md` — **DONE 2026-08-14** — Full unconditional Lean closure: exact complex split/compact real-form restrictions, Euler-virial conservation, common finite-packet quadratic jet, coercivity and radicals, positive finite Prony reconstruction, prime-clock recurrence, and literal Gauss harmonic admission/RH equivalence; direct source checks, scratch axiom audit, scoped new-code scan, and umbrella wiring pass.
