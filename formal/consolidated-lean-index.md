# Consolidated Lean Implementation Index

**Historical bridge index.** For current formal navigation start with
`formal/LEAN_OVERVIEW.md`, then search `formal/LEAN_API.md` or run
`scripts/formal_tools.py research "<query>"`. This file tracks older
`docs/consolidated/` bridge status and is not the primary proof map.

Working index for the goal: turn the claims in `docs/consolidated/` into Lean
artifacts in this project where possible.  The consolidated files are treated as
read-only sources.

Status key:

| Status | Meaning |
|---|---|
| Lean proved | A theorem/lemma with a proof is present in `formal/GaloisForLFunctions`. |
| Lean conditional | Lean proves the implication skeleton, with the hard analytic/native hypothesis left as an explicit premise. |
| Lean statement | A conjectural proposition is represented as a `def : Prop`; it is not asserted. |
| Paper BRIDGE | The consolidated corpus records a paper proof, but the full statement is not yet Lean-formalized. |
| Partial Lean | A finite/algebraic anchor is formalized, but the full consolidated claim is broader. |
| Observed | Numerical/experimental support only. |
| Open | No proof claimed; not formalized as a theorem. |
| Import | Classical theorem relied on as mathematics outside this Lean project. |
| Failed/no-go | Corpus marks the route as false, retired, or a guardrail. |

## Root Lean Artifacts

| Artifact | Status | Notes |
|---|---|---|
| `formal/GaloisForLFunctions.lean` | Lean aggregation | Imports the current library modules, including `ConsolidatedBridges`. |
| `formal/GaloisForLFunctions/ConsolidatedBridges.lean` | Lean proved, conditional | Adds `twoLemmaBridge_forces_onLine`, `supportBridge_forces_onLine`, `rhFalseBridge_forces_onLine`, `faithfulIndex_zero_forces_finiteRHLike`, `signedCarrier_separates`. These do not prove RH; they prove the logic after missing hypotheses are supplied. |
| `formal/GaloisForLFunctions/FieldConjectures.lean` | Lean statement + finite theorem | Represents DSS/realization as `Prop`s and proves the finite carrier Herglotz iff on-line shadow. |
| `formal/GaloisForLFunctions/SigmaOrbit.lean` | Lean proved | Now includes `sigma_fixed_iff_eq_half` for the holomorphic FE involution's single fixed point and `sigmaConj_fixed_iff_critical` for the full anti-holomorphic critical-line fixed locus. |

## Deep-Research Report Addendum

Additional read-only source: `docs/consolidated/deep-research-report.md`.

| Report proposition | Claim | Lean status | Notes |
|---|---|---|---|
| A1 | Correct seam symmetry: `s -> 1-s` fixes only `1/2`; `s -> 1-conj(s)` fixes the critical line | Lean proved | `sigma_fixed_iff_eq_half`, `sigmaConj_fixed_iff_critical`. |
| A2 | Gamma-real shift and logarithmic connection | Lean proved / Import | `gammaReal_shift_two`, `gammaRealLogConnection`, `digamma_half_add_one`; classical Gamma facts imported through mathlib. |
| A3 | Functional equation one-form symmetry and symmetric-lane modulus equality | Partial Lean / Import | `fePullback_*` derivative reversal exists; completed zeta FE and scalar modulus theorem for `xi` are not formalized in hgt. |
| A4 | Critical modulus criterion for prime modes | Lean proved | `norm_cpow_eq_critical_iff`, `diagonalBoundary_unit_norm_iff`. |
| A5 | Euler convergence and logarithmic derivative convergence on `Re s > 1` | Import / Open in hgt | No analytic convergence theorem in hgt yet. |
| A6 | Argument principle for `d log xi` | Import / Open in hgt | No contour/residue theorem specialized to `xi` in hgt. |
| A7 | Pole-centre localization | Open in hgt | Elementary calculus target; not yet formalized. |
| A8 | Curvature identity, RH-concavity, off-line convexity window | Partial/Open | Some finite curvature/susceptibility anchors exist; full `Xi` Mittag-Leffler identity not formalized. |

## Consolidated Proven Theorems T1-T29

| ID | Consolidated claim | Lean status | Relevant Lean artifacts | Notes |
|---|---|---|---|---|
| T1 | Constraint-not-flow: FE involution, fixed seam, prime-flow spectrum RH-blind | Partial Lean | `sigma_involutive`, `sigma_fixed_iff_eq_half`, `sigmaConj_fixed_iff_critical`, `primeLogFrequency_*`, `fePullback_*` | Holomorphic-vs-antiholomorphic fixed-locus correction formalized; Connes/spectral/no-flow reading remains import/paper. |
| T2 | Two sources / sigma-orbit balance; CC iff orbit degree zero; Gamma non-CC | Partial Lean | `orbitDegree_*`, `eq_sum_single_sub_base_of_orbitDegree_zero`, `MultiplierDichotomy`, `ArchimedeanGamma` | Finite orbit algebra and multiplier anchors exist; full Gamma divisor/HT import not Lean-proved. |
| T3 | Multiplier dichotomy: CC -> holonomic; non-CC -> HT via Holder/ADH | Partial Lean + Import | `ccGaugeMultiplier_eq_const`, `hasDerivAt_mul_exp_const_ode` | Gauge algebra formalized. Hypertranscendence implication is classical/imported, not proved in Lean. |
| T4 | Corank seam invariant; linear floor below algebraic apex | Partial Lean | `linearIndependent_log_primes`, `finitePrimeLogAnnihilator_eq_singleton`, `BigradedCorank` | Linear floor formalized; algebraic/trdeg apex remains open/imported. |
| T5 | G3 corank dichotomy | Paper BRIDGE | `HolonomicityLimit`, `ArchimedeanCorank` anchors | Full infinite-base holonomic iff corank theorem is not fully Lean-formalized. |
| T6 | Holonomicity-limit nonclosure | Partial Lean | `monotoneNat_eventually_constant_of_bddAbove` | Monotone finite stabilization anchor only; category-level nonclosure remains paper. |
| T7 | G1 difference-Holder finite-order q-difference exclusion | Paper BRIDGE | `logPrime_no_rat_relation`, `primeLogFrequency_eq_zero_iff` | Linear independence floor formalized; no full q-difference nonexistence theorem in Lean. |
| T8 | Orthogonality of independence and positivity | Partial Lean | `rankOne_noSelfDualMultiplier_of_sq_ne_one` | Rank-one obstruction formalized; universal prime-side no-polarization remains paper/open beyond finite anchors. |
| T9 | Universal prime-side orthogonality / FE is not Source-B automorphism | Partial Lean | `cpow_inversion_scale`, `boundaryUnitNormalize_norm_eq_one_iff` | Bohr inversion/scale and boundary modulus formalized; full no-source-B-polarization statement not. |
| T10 | Seam firewall: finite-place positivity cannot force archimedean positivity | Paper BRIDGE | None specific | No full Lean theorem yet. |
| T11 | Two lattices / digamma residue seam | Partial Lean | `deriv_archimedeanPrimeMode`, `gammaRealLogConnection`, `digamma_half_add_one` | Finite generator/Gamma connection anchors. |
| T12 | Archimedean-prime cross-term; FE cocycle; commutation | Partial Lean | `coextensionComposite_eq_iff_flatCondition`, `coextension_commutes_iff_flatCondition`, `scaleCoordinate_commute`, `fePullback_*` | Algebraic cocycle/commutation skeleton formalized; analytic Gamma-ratio defect not fully. |
| T13 | Archimedean generator axis mode, no combination modes | Partial Lean | `deriv_archimedeanPrimeMode`, `twoAxis_*`, `scaleCoordinate_commute` | Finite modes formalized. |
| T14 | Explicit formula as constraint; RH iff Weil positivity iff kappa minus zero | Lean conditional + Paper BRIDGE | `supportBridge_forces_onLine`, `twoLemmaBridge_forces_onLine`; finite inertia modules | Lean now proves bridge logic only; Weil positivity/RH equivalence remains import/paper. |
| T15 | Intrinsic RH locus / faithful off-line index | Partial Lean + Lean conditional | `multiPair_carrier_exact_neg_inertia`, `multiPair_carrier_linearIndependent`, `faithfulIndex_zero_forces_finiteRHLike` | Exact finite inertia exists; new finite route proves vanishing faithful index implies no finite off-line points. Global carrier open. |
| T16 | Phase-cancellation crux / affine confinement | Partial Lean | `susceptibilityMirrorFrequencyFactor_*`, secular/Hankel anchors | Some finite/exponent calculations formalized; transverse hierarchy remains open. |
| T17 | Prime-zero susceptibility transverse balance | Lean proved for exponent skeleton | `susceptibilityExponent_zero_iff`, `susceptibilityMirrorFrequencyFactor_eq_one_forall_iff` | Does not prove analytic zero motion. |
| T18 | Critical-line abscissa of convergence | Paper BRIDGE / Import | None specific | Selberg/Kronecker analytic inputs not Lean-formalized. |
| T19 | Erosion cocycle / threshold | Paper BRIDGE | None specific | Analytic L2 coboundary statement not Lean-formalized. |
| T20 | Fisher signature wall | Paper BRIDGE | None specific | Analytic `zeta(2 sigma)` metric/signature not Lean-formalized. |
| T21 | Corank-transcendence continuation | Paper BRIDGE / Partial Lean | `BigradedCorank` anchors | Inequality and F_q exactness not fully Lean-formalized. |
| T22 | F1 inversion / finite Stieltjes collapse | Partial Lean | `stieltjes_pairing_cauchy_j`, `StieltjesWeld` | Cauchy-product coefficient formalized; trdeg/corank statement not fully. |
| T23 | F1 two-face criterion | Paper BRIDGE | `ArchimedeanCorank` partial | Criterion not fully Lean-formalized. |
| T24 | Frobenius collapse linear vs algebraic | Paper BRIDGE | None specific | Witness-level algebraic transcendence not formalized. |
| T25 | G2/G4/G5 over F_q | Partial Lean + Import | `functionField_localFactor_FE`, `functionField_esymm_FE`, `functionFieldWeightNormalize_norm_eq_one_iff` | FE/weight algebra formalized; Papanikolas, Deligne-Katz, Deligne purity imported. |
| T26 | DSS lower-bound orbit no-go | Paper BRIDGE | None specific | No Lean theorem yet. |
| T27 | Stieltjes-log weld linear floor | Partial Lean | `stieltjes_pairing_cauchy_j`, `linearIndependent_log_primes` | Linear algebra/Cauchy floor formalized; value-theoretic layer open. |
| T28 | Koszul acyclicity and omega/RH coupling | Partial Lean | `koszulD1_eq_zero_iff_additiveCocycle`, `koszulD1_koszulD0_eq_zero` | Multiplicative skeleton formalized; RH/omega equivalence not. |
| T29 | Li-secular change of basis | Lean proved | `li_secular_pointwise`, `secular_li_pointwise_inv`, `superzeta_*` | Finite/pointwise algebraic identities formalized. |

## Lean-Verified Bedrock From Consolidated 07 §2

| Bedrock item | Lean status | Notes |
|---|---|---|
| Log-prime Q-linear independence | Lean proved | `linearIndependent_log_primes`, `logPrime_no_rat_relation`. |
| Finite prime-log annihilator | Lean proved | `finitePrimeLogAnnihilator_eq_singleton`. |
| FE involution and critical fixed locus | Lean proved | `sigma_involutive`, `sigma_fixed_iff_eq_half`, `sigmaConj_fixed_iff_critical`. |
| Boundary modulus critical line | Lean proved | `norm_cpow_eq_critical_iff`, `boundaryUnitNormalize_norm_eq_one_iff`. |
| Gamma real shift / log connection / digamma shift | Lean proved | `gammaReal_shift_two`, `gammaRealLogConnection`, `digamma_half_add_one`. |
| Archimedean prime-mode derivative | Lean proved | `deriv_archimedeanPrimeMode`. |
| Archimedean corank no-collapse | Lean proved | `primeLogFullSpan_rank_with_archimedean` family. |
| Additive Koszul cocycle skeleton | Lean proved | `koszulD1_eq_zero_iff_additiveCocycle`, `koszulD1_koszulD0_eq_zero`. |
| CC gauge trivialization | Lean proved | `ccGaugeMultiplier_eq_const`, `hasDerivAt_mul_exp_const_ode`. |
| Function-field FE algebra skeleton | Lean proved | `functionField_localFactor_FE`, `functionField_esymm_FE`; purity excluded. |
| Faithful finite kappa-minus count | Lean proved | `multiPair_carrier_exact_neg_inertia`, `multiPair_carrier_linearIndependent`. |
| FE quadruple kappa two | Lean proved | `fe_quadruple_kappa_two`. |
| Superzeta additive resolvent trace | Lean proved | `superzeta_coeff_eq_powerSum`, `superzeta_eq_sum_resolvent`. |
| Finite spectral Torelli | Lean proved | `powerSum_torelli`, `spectralTorelli_faithful`, `esymm_eq_of_powerSum_eq`. |
| Rank-one dual multiplier obstruction | Lean proved | `rankOne_noSelfDualMultiplier_of_sq_ne_one`. |
| Orbit-degree algebra | Lean proved | `orbitDegree_*`, `eq_sum_single_sub_base_of_orbitDegree_zero`. |
| Stieltjes-log Cauchy product | Lean proved | `stieltjes_pairing_cauchy_j`. |
| Bezout/residue Gram brick | Lean proved | `bezout_eq_residue_gram`, `bezout_brick`. |
| Sato-Tate Chebyshev orthogonality | Lean proved | `satoTate_orthonormal`, `satoTate_moment`. |
| Li/secular triangular transform | Lean proved | `li_secular_pointwise`, `secular_li_pointwise_inv`. |
| Moment-positivity Schur-Cohn bridge | External Lean repo / not in hgt | Consolidated cites `moment-positivity`; not imported here. |

## Required Lemma Shapes L-A to L-E

| ID | Lemma shape | Lean status | Notes |
|---|---|---|---|
| L-A | Local pole geometry for reset center, phase-space area, Berry/co-failure detectors | Partial Lean / Open | Curvature and finite algebra anchors exist; remaining detector package not formalized. |
| L-B | Completion symmetry / Berry-as-theorem from FE | Open | FE pullback derivative skeleton exists; Berry amplitude theorem not formalized. |
| L-C | Continuum association operator with spectral gap | Open | No continuum kernel or spectral-gap theorem yet. |
| L-D | Phase-Sobolev regularity functional predicting Group B | Open | No Sobolev/phase functional formalized. |
| L-E | Source-measure bridge / off-seam defect confinement | Lean conditional | `supportBridge_forces_onLine`, `twoLemmaBridge_forces_onLine`; hard detection/confinement hypotheses remain open. |

## Theorems Toward RH, A-L

| ID | Theorem shape | Status | Lean notes |
|---|---|---|---|
| A | Far-left phase-weld limit: true tends to log 2, finite tends to 0 | Open | No Lean theorem. |
| B | Transport metric separates true from finite/random | Open | No Lean theorem. |
| C | Coupled low-reserve lane co-failure excess | Observed | No theorem. |
| D | q70 association-gate spectral gap | Observed/Open | No Lean spectral-gap theorem. |
| E | Berry two-path completion switch | Observed/Open | FE derivative skeleton only. |
| F | Observed-volume covariance sign | Observed | No Lean theorem. |
| G | Phase-space caustic / signed action integral | Observed | `signedCarrier_separates` proves only sign-separation logic. |
| H | Phase-regulated dissolution exits | Observed | No Lean theorem. |
| I | Reset-occupation center recovers beta | Partial/Open | Local model not yet formalized in hgt. |
| J | Two-clock gate/tension covariance sign crossing | Observed | No Lean theorem. |
| K | Context-fragility monotone | Observed | No Lean theorem. |
| L | Right-strip Euler collapse | Paper/import | No Lean convergence theorem in hgt. |

## Light-Tower Claims LT1-LT8

| Claim | Status | Lean implementation notes |
|---|---|---|
| LT1 transport-not-scalar | Observed + Paper BRIDGE | No single Lean theorem. |
| LT2 weld + seam | Partial Lean | FE seam, boundary modulus, two-source algebra anchors. |
| LT3 constraint-not-flow | Partial Lean + Paper BRIDGE | FE involution and derivative reversal formalized; no Hilbert-Polya/no-flow theorem in Lean. |
| LT4 coupled non-product measure | Observed/Open | No Lean theorem. |
| LT5 Berry completion switch | Observed/Open | FE skeleton only. |
| LT6 reset occupation / one-half | Observed + Partial Lean | Susceptibility exponent and critical-line fixed loci formalized. |
| LT7 oriented signed structure | Observed + Lean conditional | `signedCarrier_separates` formalizes the sign-separation consequence. |
| LT8 off-line iff off-seam bridge | Lean conditional + finite index anchors | `rhFalseBridge_forces_onLine`, finite kappa-minus anchors; global equivalence open. |

## Carrier-Synthesis Conjectures C1-C6

| ID | Conjecture | Lean status | Notes |
|---|---|---|---|
| C1 | Carrier is an oriented 2-form with true/surrogate sign reversal | Lean conditional | `signedCarrier_separates` proves sign reversal separates objects; existence/canonicity of the 2-form open. |
| C2 | Carrier is holonomy of affine weld connection | Partial Lean / Open | `FlatConnection` gives cocycle algebra; named cohomology group and carrier identification open. |
| C3 | Long-run coherence is one phase-Sobolev regularity gap | Open | No Lean statement/theorem. |
| C4 | Weld is 2-D rigid via divergent cross-lane correlation length | Open | No Lean statement/theorem. |
| C5 | Genuine crossover scale sigma* | Open | No Lean statement/theorem. |
| C6 | Inverse problem: realize Gamma-infinity + zeta'/zeta from primes + boundary cocycle | Open | No Lean theorem; related `RealizationProblem` exists as abstract `Prop` for finite carrier shape. |

## Bridge Conjectures B1-B3

| ID | Conjecture | Lean status | Notes |
|---|---|---|---|
| B1 | Completed transport features force support of source measure onto the seam | Lean conditional | `supportBridge_forces_onLine` proves the support-confinement implication. The actual source measure theorem is open. |
| B2 | Two-lemma bridge: detect off-line defects and confine source-carrying defects | Lean conditional | `twoLemmaBridge_forces_onLine` proves the logic. Lemma 1 global and Lemma 2 are open. |
| B3 | RH-false bridge: off-line zero iff off-seam source-carrying defect | Lean conditional | `rhFalseBridge_forces_onLine` proves equivalence + confinement implies all zeros on-line. Equivalence is open. |

## Apex Open Cores

| ID | Open core | Lean status | Notes |
|---|---|---|---|
| APEX-A | Schanuel-for-prime-logs / DSS / value axis | Lean statement + partial floor | `DSS` is a `Prop`; log-prime linear floor proved. Algebraic independence remains open. |
| APEX-B | Faithful positivity / kappa-minus zero / Hankel hierarchy | Partial Lean + Lean conditional | Finite faithful-index anchors and `faithfulIndex_zero_forces_finiteRHLike`; global positivity/index vanishing open. |
| APEX-C | Universal prime-side orthogonality | Partial Lean / Open | Rank-one and Bohr-scale obstructions formalized; universal theorem open. |
| APEX-D | C5/C5-star native weld theorem | Open | No Lean proof; current work remains BRIDGE/substrate. |

## Named Research Conjectures

| ID | Conjecture | Lean status | Notes |
|---|---|---|---|
| C-2026-06-18-005 | Route-C archimedean minus prime positivity iff RH | Open | No Lean theorem. |
| C-2026-06-18-011 | Type-III rigidification / master object with integer kappa at q->1 | Open | No Lean theorem. |
| C-2026-06-18-001 | Infinite period-domain ellipticity iff RH | Open | No Lean theorem. |
| C-2026-06-18-021 | Hodge-index realization of `Q_W = Omega - Pi` | Open | No Lean theorem. |
| C-2026-06-18-039 | Two-variable kernel `K_MS` / `N_0` criterion | Open | No Lean theorem. |
| C-2026-06-18-008 | Archimedean Iwasawa / Takesaki crossed product | Open | No Lean theorem. |
| C-2026-06-18-018 | `Q_3` / higher-Chowla discriminator | Open | No Lean theorem. |
| DSS-cross 3b | DSS iff Stieltjes constants algebraically independent over period field, modulo GPC | Lean statement only | `DSS` is a `Prop`; no period-field theorem. |
| Jensen TP-defect = 2 kappa-minus | Open / Partial finite experiments | No Lean theorem connecting Jensen defects to kappa-minus. |
| Regularization manufactures transcendence | Open/meta | No Lean theorem. |
| C-2026-06-18-044 | Free infinite divisibility positivity sufficient for RH if identifications built | Open | No Lean theorem. |

## Source-Built / Faithful-Index Construction Conjectures

| ID | Conjecture | Lean status | Notes |
|---|---|---|---|
| G-C10 | Source-built faithful-index object | Lean conditional | `faithfulIndex_zero_forces_finiteRHLike` handles the finite consequence after construction/equality/vanishing. Construction open. |
| G-C11 | F1/Hodge polarization forces faithful index to vanish | Open | No Lean theorem. |
| G-C15 | One object, two entrances (Jacobi/Krein/Hodge and Jensen/LP) | Open | No Lean theorem. |
| G-C16 | Source-built Jacobi positivity | Open | No Lean theorem. |
| G-C17 | Uniform Jensen stability | Open | No Lean theorem. |
| G-C18 | Faithful-index rigidity | Lean conditional | Finite consequence formalized; rigidity/forcing open. |
| G-C19 | Primitive Schur/Hodge equivalence | Open | No Lean theorem. |

## Failed Or No-Go Routes From Consolidated 05

| Route | Status | Lean notes |
|---|---|---|
| Archimedean corank collapse | Failed/no-go | `ArchimedeanCorank` supports no-collapse anchors. |
| Omega splits wild-kernel freeness | Failed/no-go | No Lean theorem in this batch. |
| F1 Hodge-Riemann modular route via measured trace | Failed/no-go | Guardrail only. |
| Transcendence implies GUE | Failed/no-go | No Lean theorem. |
| Is Lambda a period | Failed/no-go | Guardrail only. |
| Schwarz lemniscate transcendence dichotomy | Failed/no-go | No Lean theorem. |
| Moonshot knot/memory/skyrmion/river-delta routes | Failed/no-go | No Lean theorem. |
| B24 spectral Galois action | Failed/no-go | No Lean theorem. |
| Tamagawa strength-one / tropical zeta values / percolation sync | Failed/no-go | No Lean theorem. |

## Classical Imports Still Outside Lean

| Import | Use | Lean status |
|---|---|---|
| Baker-Wustholz | Log-prime linear independence lower bounds, reducibility, Stieltjes weld | Basic unique-factorization log-prime independence proved; quantitative Baker not. |
| Holder 1887; ADH / Hardouin-Singer | Gamma hypertranscendence and non-CC -> HT | Import only. |
| Weil explicit formula / Weil positivity | RH as FE-polarization positivity | Import/paper only. |
| Connes spectral realization | Zeros as archimedean spectrum | Import only. |
| Kronecker-Weyl; Selberg CLT | Random Euler convergence and critical abscissa | Import only. |
| Papanikolas; Deligne Weil II; Deligne-Katz | F_q border G2/G4/G5 | Algebra skeleton only in Lean; theorems imported. |
| Procesi / Artin | Character-variety trace invariants | Import only. |
| Gelfond-Schneider; Nesterenko; Lipshitz | Degree-2/transcendence/diagonal inputs | Import only. |
| Krein-Langer; GORZ / Polya-Jensen; Csordas-Norfolk-Varga | Faithful index and positivity hierarchy | Finite carrier/inertia anchors only. |

## Current Batch Notes

| Date | Change | Verification |
|---|---|---|
| 2026-06-21 | Added `ConsolidatedBridges.lean` and imported it from `GaloisForLFunctions.lean`; added `sigma_fixed_iff_eq_half`; indexed `deep-research-report.md` A1-A8. | Pending targeted Lean checks; current Lean process is starved/slow under concurrent external build load. |
