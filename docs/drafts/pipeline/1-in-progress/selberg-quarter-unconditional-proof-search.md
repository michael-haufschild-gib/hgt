# Unconditional Selberg quarter bound: route-open proof search

- **ID:** SELBERG-QUARTER-UNCONDITIONAL
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Resumed user goal, 2026-09-08; prior symmetric-power search and quarter-conjecture corpus audit.
- **Statement:** Prove the positive hyperbolic Laplacian quarter bound for every nonzero weight-zero congruence Maass cusp eigenfunction, with no unproved mathematical assumptions or added axioms.

## Goal and current status

The resumed objective does not prescribe a proof route. The full congruence spectral statement remains the goal; scalar analogues, finite-level results, and conditional implications are not substitutes. No proof has been obtained. The earlier symmetric-power search remains recorded in [its card](selberg-symmetric-power-unconditional-route.md); this resumption starts a fresh blocked audit.

**Research status: blocked after three consecutive resumed turns; full goal unachieved.** The native modular cusp operator, character-twist estimate, trace/monodromy candidates, and a newly located July 2026 modular-symbol route all leave an arithmetic exclusion theorem unproved. The third turn revalidated current source changes and the declaration index without finding a viable proof step. This card remains in progress because no route has been proved impossible or retired.

## Gates and plan

- [x] Revalidate current worktree, relevant memories, prior audits, and available project docs. `docs/architecture.md` and `docs/testing.md` remain absent.
- [x] Search the full declaration index for direct energy, spectral/trace, twist-nonvanishing, and other arithmetic mechanisms; inspect relevant exact statements.
- [x] Audit the new native cusp operator and distinguish a constructed spectral ray from exclusion of smaller cuspidal eigenvalues.
- [x] Audit the strongest remaining arithmetic candidate against current primary sources and actual corpus hypotheses.
- [x] In resumed turn two, check trace/monodromy rigidity and character-perturbation alternatives, including the July 2026 modular-symbol paper, against exact corpus declarations.
- [x] In resumed turn three, revalidate current commits, changed source, and the refreshed index; audit the full objective and record the persistent mathematical blocker.
- [ ] Obtain a dependency-closed paper proof of the full conjecture.
- [ ] Formalize that proof in Lean, wire finished modules, run foreground targeted checks and the formal lint gate, and inspect axioms in scratch.

The `update_plan` tool is unavailable; this card records the plan. No computations or numerical certificates will be used. No full or umbrella builds, commits, or pushes are authorized.

## Findings

### Corpus search

Nineteen searches used the full own-tree declaration index. The first refreshed it; later queries used `--no-refresh`, with `--limit 100` for discovery where appropriate. These are search-result counts, not a claim to have audited every unrelated theorem or a proof that no differently named construction exists.

| Query | Declarations / modules |
|---|---:|
| `"spectral" "quarter"` | 44 / 21 |
| `"maass" "eigenvalue"` | 3 / 2 |
| `"cusp" "coerciv"` | 0 / 0 |
| `"poincare" "inequality"` | 5 / 3 |
| `"twist" "nonvanishing"` | 5 / 2 |
| `"kuznetsov"` | 1 / 1 |
| `"selberg" "trace"` | 11 / 2 |
| `"kloosterman" "cancellation"` | 14 / 8 |
| `"twist" "mean"` | 19 / 10 |
| `"character" "nonvanish"` | 0 / 0 |
| `"geodesic"` | 133 / 25 |
| `"congruence" "gap"` | 17 / 6 |
| `"hardy" "boundary"` | 578 / 140 |
| `"cusp" "spectrum"` | 103 / 30 |
| `"poincare" "positive"` | 40 / 23 |
| `"hyperkloosterman"` | 0 / 0 |
| `"hardy inequality"` | 19 / 3 |
| `"ground state" "transform"` | 1 / 1 |
| `"cusp" "eigen"` | 112 / 18 |

The broad Hardy search mostly located Hardy function spaces, so it was refined to the inequality phrase. The trace and Kuznetsov results led back to conditional periodization identities and finite arithmetic carriers. No actual all-level cuspidal trace certificate or twist-family nonvanishing theorem was found.

### Native modular cusp operator: exact scope

Sources below are under `formal/GaloisForLFunctions/RHTower/`.

- `ThetaCuspHawkingBMModularEnergyDomain.lean` constructs a graph completion of fields invariant under the full `PSL2Z`. It does not quantify over arbitrary congruence subgroups. Its `embedding_norm_le` controls scalar mass by value-plus-gradient energy.
- `ThetaCuspHawkingBMGlobalAngularWeakResponse.lean` constructs the self-adjoint form operator. `energy_inner_decomposition` retains scalar mass plus two squared derivative norms. This supplies the mass-one baseline for the shifted operator, not a quarter improvement for the positive Laplacian.
- `ThetaCuspHawkingBMOperatorCore.lean` identifies the actual operator on full periodized tests as `T = 1 - Delta_H`, where `Delta_H` has the opposite sign from the positive Laplacian in the Selberg target.
- `ThetaCuspHawkingBMCuspLogTest.lean` defines a compact smooth logarithmic profile supported in `t > log 2`. The inverse transform vanishes at all heights `y ≤ 2`. `ThetaCuspHawkingBMCuspHeightTest.lean` proves its modular field equals the prescribed height-only profile on the fundamental domain. Here “cusp” means support in the geometric cusp; it does not impose zero horizontal Fourier constant term.
- `ThetaCuspHawkingBMCuspSpectralRay.lean` proves that `T - lam` has no bounded left inverse for every real `lam ≥ 5/4`, using constructed unit approximate vectors. This is a spectral inclusion at and above the shifted threshold. It is not spectral exclusion below the threshold. In particular, it supplies neither the cuspidal restriction nor the all-congruence quantifier required for Selberg.

These are genuine new operator constructions, but their exact conclusion leaves the small cuspidal eigenvalue problem untouched. A proof using them would still need a congruence-sensitive quarter coercivity theorem on the actual cuspidal domain, with the compact part and all cusps retained.

### Character-twist mean: error audit

[Luo–Rudnick–Sarnak, Proposition 3.1 and equation (3.22)](https://www.math.tau.ac.il/~rudnick/papers/lrsGAFA.pdf) give errors `Q*Y^(1-sigma+epsilon)` and `Q^(1+K)*Y^(-sigma)`, where `sigma = Re(beta)` and `K = (m^2+1)/2`. The main term has order `Q^2/log Q`.

Elementary optimization of these stated bounds: put `Y = Q^a` and omit epsilon. The two exponents are

`E1 = 1 + a*(1-sigma)`, `E2 = 1 + K - a*sigma`.

For `0 < sigma < 1`, their weighted average is

`sigma*E1 + (1-sigma)*E2 = 1 + K*(1-sigma)`.

Thus `max(E1,E2)` is at least this value, attained at `a=K`. Lower-order errors require `sigma > 1 - 2/(m^2+1)`. Changing the smoothing scale alone cannot extend this estimate to every positive parameter. This audits those bounds, not all possible twist methods.

### Arithmetic carrier audit

`RHTower/Sieve/KloostermanTerminalGeometricCancellation.lean` has an unconditional finite terminal estimate

`norm(block) ≤ sum_x sum_y 2 / norm(1 - crossPhaseRatio q r x y)`

for unequal moduli. This retains a modulus-dependent reciprocal phase-separation sum. The theorem does not provide the collective hyper-Kloosterman character average or a smaller error in the preceding global mean. Its own source explicitly distinguishes finite phase cancellation from the missing collective spectral modulus average. No estimate closing that step was located in the searches above.

### Verification and outcome

`lake env lean /tmp/selberg_route_open_audit.lean` passed in one foreground process using existing oleans. It checked the full modular invariance field, cusp support, low-height vanishing, energy decomposition, spectral-ray theorem, and terminal Kloosterman estimate. Both audited capstones report only `propext`, `Classical.choice`, and `Quot.sound` under `#print axioms`.

The PDF skill was used for the error audit. Text extraction left the formulas garbled; only the two affected formula pages were rendered and inspected. No numerical proof experiment was run.

No Lean source was edited, no extra mathematical axiom introduced, and no substitute theorem added. No build or umbrella build was run. An unrelated agent's live `DivisorCoreMellinBoundary.lean` process was observed and left untouched; this task's Lean audit finished successfully.

**Full goal remains unachieved.** This resumed turn produced evidence about two alternative routes, not an unconditional proof. The next mathematical requirement is a new arithmetic exclusion mechanism: a stronger actual twist-family estimate or an all-congruence cuspidal spectral/energy certificate. No dependency-closed candidate for either is currently available from this audit. The goal remains active under the fresh resumed audit; no route is being declared impossible or retired.

### Resumed turn two: trace, monodromy, and perturbation

Twenty further declaration-index searches were performed. The first refreshed the index. Broad discovery results were refined before inspecting relevant source statements; unrelated matches are not claimed to have been exhaustively proof-audited.

| Query | Declarations / modules |
|---|---:|
| `"congruence" "representation"` | 2 / 2 |
| `"monodromy" "selberg"` | 1 / 1 |
| `"trace" "cuspidal"` | 0 / 0 |
| `"hecke" "operator"` | 0 / 0 |
| `"arithmetic" "tempered"` | 1 / 1 |
| `"congruence subgroup"` | 8 / 4 |
| `"amplifier"` | 364 / 68 |
| `"trace formula"` | 77 / 27 |
| `"complementary" "exclude"` | 0 / 0 |
| `"pole" "exceptional"` | 28 / 16 |
| `"monodromy integrality"` | 0 / 0 |
| `"rankin" "positive"` | 1 / 1 |
| `"maass" "amplif"` | 0 / 0 |
| `"modular symbol"` | 0 / 0 |
| `"eigenvalue" "perturb"` | 0 / 0 |
| `"residual" "eigen"` | 11 / 4 |
| `"kloosterman" "zeta"` | 0 / 0 |
| `"hellmann"` | 39 / 9 |
| `"pseudolaplacian"` | 0 / 0 |
| `"finite amplifier"` | 23 / 2 |

#### Exact trace and rigidity statements

- `RHTower/SelbergExceptionalAnalogy.lean`, `RHTower.simple_pole_no_exceptional`, takes natural numbers `m,j` and hypotheses `m = 1+j` and `m = 1`, then proves `j = 0`. It does not construct a spectral determinant or identify pole order with the number of exceptional Maass eigenvalues. Self-adjointness alone leaves the real exceptional parameters permitted by its other scalar lemmas.
- `RHTower/SelbergLedgerCeiling.lean`, `selberg_ledger_exclusion`, assumes a strict comparison between a finite sum of explicit Poisson-kernel weights and a target weight. Its conclusion is a cardinality/width inequality. Producing that strict comparison for the actual cuspidal trace is still necessary.
- `HTGeometry/FiniteAmplifierFrame.lean`, `HTGeometry.frame_width_ratio_form`, similarly retains the explicit strict inequality `hexcl`. Its coefficient bounds constrain the specified finite positive patterns; they do not prove every conceivable congruence spectral argument must have that form.
- `docs/drafts/pipeline/4-publication-ready/monodromy-integrality-selberg.md` studies Selberg-class normality, not the Laplace quarter bound. Its central meromorphic/nonvanishing correlation hypothesis MI is explicitly open. The class itself retains Ramanujan coefficient growth as an input: `RHTower/SelbergClass/Full.lean`, `SelbergClass.ramanujan`. No unconditional general-Maass instance or spectral-pole counting dictionary was found. The draft's standard-twist “cusp-spectrum radius” is not the cuspidal Laplace spectrum.

#### New primary-source candidate: modular symbols

[Diamantis–Friedberg–Strömberg, July 2026, Theorem A](https://arxiv.org/html/2607.10786v1#S1) continues the modular-symbol Kloosterman zeta function **meromorphically** into `Re(s)>1/2`, explicitly retaining potential poles where `s(1-s)` is exceptional. Theorem B retains terms `r_j*x^alpha_j` from those poles in the summatory formula. Neither theorem excludes them.

[Conjecture 7.3](https://arxiv.org/html/2607.10786v1#S7.SS3) separately asks for a nonzero residue coefficient detecting each spectral mode and an `O(X^(1/2+epsilon))` remainder after subtraction of the prescribed linear term. These are proposed sufficient arithmetic inputs, not established estimates. The general nonzero-frequency route also leaves residue detection unresolved. No numerical investigations from the paper were reproduced or used as proof.

#### Perturbation route and corpus reuse boundary

[Risager, Theorem 1.1 and Conjecture 1.2](https://arxiv.org/html/0707.2332v3#S1) identifies Selberg with absence of small **residual** eigenvalues throughout a neighborhood of certain character deformations. Absence at the undeformed character is insufficient. The arithmetic nonvanishing theorem supplies one side of a proposed contradiction; the deformation stability assertion supplies the other and remains a conjecture. This is a 2008 arXiv version, later published in 2011; the HTML's regenerated 2026 date is not evidence of a new proof.

The corpus search found a different meaning of “eigen-residual”: `HTGeometry/SimpleEigenvalueBranchRCLike.lean` defines the equation error `(A(c)phi - nu*phi, inner(psi0,phi)-1)`. It is unrelated to the residual automorphic spectrum.

`HTGeometry/HellmannFeynmanUnconditional.lean` constructs normalized differentiable branches for bounded symmetric operator families with a supplied simple eigenvalue and transverse gap; in finite dimensions simplicity supplies the gap. This is useful perturbation infrastructure, but its theorem neither constructs the required character-deformed Laplacian/scattering family nor controls whether a persisting eigenvector is cuspidal or residual. Applying it to a suitable bounded resolvent would still require those constructions and the arithmetic regularity argument. No proof of that regularity was found.

#### Turn-two verification and status

`lake env lean /tmp/selberg_perturbation_scope_audit.lean` passed in one foreground process using existing oleans. It checked the exact pole-budget, ledger, finite-amplifier, Hellmann–Feynman, and Ramanujan-field signatures. The four theorem axiom audits contain no axioms beyond `propext`, `Classical.choice`, and `Quot.sound` (the elementary pole-budget theorem does not use `Classical.choice`).

No Lean source changed and no new theorem or axiom was introduced. No builds, numerical computations, or umbrella builds were run. The task's Lean process exited successfully; another agent's `DivisorCoreMellinStrip.lean` process was left untouched.

**No unconditional Selberg proof was obtained.** The new candidate requires a proof of deformed-scattering regularity or the explicit modular-symbol detection/cancellation inputs. None is currently dependency-closed in the audited sources or corpus. This is the second resumed turn with the same fundamental impasse: no established arithmetic exclusion of complementary-series cusp forms. The goal remains active until the resumed blocked-audit threshold is met or a viable proof is found. No route has been retired or claimed impossible; no negative result is being passed off as a solution.

### Resumed turn three: current-state and completion audit

The preceding turn is classified as evidence progress: it found and checked a July 2026 route and identified the additional residue-detection and cancellation requirements. It did not discharge the fundamental mathematical blocker. The blocker is unchanged across all three resumed turns, even though the candidate routes differ.

Current `HEAD` is `875d56442`. The diff from `2dca80eea` contains 145 formal source paths, including native modular operator work already inspected in turn one. The Maass correspondence, scalar symmetric-power amplification, exceptional compact model, and Hellmann–Feynman files selected for direct diff verification are unchanged across those commits. The newly committed cusp spectral-ray theorem has the same above-threshold non-invertibility conclusion audited in turn one.

The refreshed index was searched for `"selberg" "quarter"` (3 declarations / 2 modules) and `"maass"` (228 / 17, first 100 declarations retrieved), followed by `"symmetric power" "automorph"` (0), `"cuspidal" "positive"` (0), `"scattering" "regular"` (4 / 2), and `"twist" "nonvanish"` (0). These queries revalidate discovery, not a theorem of nonexistence. The scattering hits concern different analytic/physical carriers; no general-Maass exclusion was located.

The new untracked `RHTower/ThetaCuspHawkingBMMixedSmoothCurrentLaplace.lean` was inspected through its continuation theorem. Its exact input is a `XiZeroCopy` with a fixed physical source and pointwise radial/angular arguments. It continues the actual switched source integral as an entire numerator divided by the source-frequency difference. It does not continue the full inverse or construct an all-congruence cuspidal spectral family. The accompanying `3-formalized/hb-original-wave-and-ingoing-source-continuation.md` explicitly retains the full retarded inverse and source-dependent cusp response as unfinished. These changes do not resolve any missing Selberg premise.

| Requirement | Authoritative evidence and outcome |
|---|---|
| Unconditional quarter bound for every congruence Maass cusp eigenfunction | No dependency-closed paper proof or Lean theorem obtained. **Missing.** |
| No unproved mathematical assumptions or added axioms in the target | There is no target proof to audit. Existing signature checks explicitly expose the inputs that cannot be assumed. **Not established.** |
| Corpus-first search and use of current sources | Resumed run contains 45 declaration-index searches, source inspections, and primary-source checks. This is research evidence, not completion evidence. |
| Foreground Lean verification, one process per agent | Two scratch audits passed in turns one and two. No Lean process was started in turn three; unchanged checks were not repeated. |
| No computations used as mathematical proof | No numerical proof experiment or computational certificate was used. |
| Finished modules wired and final targeted module build/lint | No new target module exists. There is nothing to wire or build; these completion gates remain unmet. No full or umbrella build was run. |
| Process cleanup | Prior task-owned audit processes terminated successfully. Final `ps`/`rg` check found no running Lean or Lake process; only the checking shell and `rg` matched. Other agents' work is untouched. |

The concrete blocker is the absence of a proved arithmetic mechanism excluding complementary-series cusp representations: compatible generic unitary lifts in unbounded degree, a sufficient actual twist-family estimate, an all-congruence quarter coercivity/trace certificate, or the specified deformation/modular-symbol alternative. No currently justified construction or proof step discharging one of these inputs has been identified. More restatement or auxiliary scalar formalization would not establish the requested theorem. Resumption needs a substantive new mathematical argument or newly available result resolving such an input; it does not need permission to run a build.

The three-turn resumed blocked threshold is now met. The full objective is preserved and must not be marked complete. This is an impasse in this proof search, not a proof that Selberg or any particular route is impossible.

## Log

- 2026-09-08 — Opened before the resumed proof attempt. Scope now includes alternatives to symmetric-power amplification. No new Lean theorem has been asserted.
- 2026-09-08 — Completed nineteen corpus queries, native cusp-domain and spectral-ray audits, exact character-mean error optimization, and a foreground Lean signature/axiom check. Neither alternative supplies the unconditional arithmetic exclusion. No claim of Selberg completion.
- 2026-09-08 — Resumed turn two: twenty further corpus queries; exact trace/monodromy and perturbation statement audits; checked July 2026 modular-symbol results and Risager's character-deformation equivalence. Foreground Lean signature/axiom audit passed. No unconditional exclusion or new Lean theorem obtained.
- 2026-09-08 — Resumed turn three: six index queries and current commit/source revalidation. No new arithmetic exclusion. Full completion audit fails at the target proof itself. Same mathematical blocker persisted for three resumed turns; goal blocked, not complete.
