# WP02 — Exposing-ray archimedean positivity

- **ID:** weil-work-02-exposing-ray
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/weil-work/02-exposing-ray.md
- **Goal:** Prove the universal exposing-ray archimedean inequality and apply its existing RH receiver in Lean.
- **Status:** OPEN. No new positivity theorem claimed.

## Work plan
1. Read exact dual/test definitions; corpus and external-frontier audit.
2. Form an exact source-energy conjecture, attack novelty, circularity and counterexamples.
3. Complete its paper proof or isolate the obstruction and strongest positive survivor.
4. Formalize only dependency-closed statements, targeted foreground audit, umbrella wiring and lint.
5. Repeat; keep main inequality open until unconditional proof is compiled.

## Current mathematical question
Can the near-null polar Riemann-kernel family provide a signed-energy decomposition on the entire matched-trace cone, with a residual controlled solely by the exposing box tail, uniformly in aperture? An energy identity alone is insufficient: the residual sign is the open core.

## Established starting evidence
- `WeilDualBound` quantifies over ALL finite nonnegative mixtures of complex C² polar tests, including multiplier zero.
- `riemannHypothesis_iff_forall_weilDualBound_archimedean` is the existing receiver, not a new result.
- `sum_archEnergy_eq_of_matched` already splits matched energy into the exact truncated Λ-pairing plus zero-side energy.
- External compact-window and finite Galerkin certificates do not provide the required cofinal estimate.

## Constraints and audit notes
- No numerical computations; no added premises, axioms, sorry, unsafe, heartbeat increases or full builds.
- New Lean scope: `WeilWorkExposingRay*.lean`; preserve existing work. User explicitly requests umbrella wiring.
- `docs/architecture.md` and `docs/testing.md` absent.
- `update_plan` and `multi_tool_use.parallel` unavailable; plan tracked here, independent reads batched with Promise.allSettled.
- Serena symbol lookup rejects the ignored Lean path; exact source inspection uses rg and bounded reads.

## Log
- 2026-10-07: hgtl7 loaded; current goal already active. Session init, corpus frontier and source receiver read. First hybrid search complete, but coverage snapshot older than index generation; most declarations source-only. No applicability inferred from search ranking.
- 2026-10-07: Exact tail-repair proof closed on paper in owned PROOF.md. Verdict BRIDGE, not scientific novelty: it extracts an existing two-point-resonator mechanism into a quantitative exposing-tail certificate. New leaf under foreground compilation; no verified result claimed yet.
- 2026-10-07: Ground-state rewrite was already in `RiemannKernelGroundStateZeroIdentity`; no sign deduction. Frequency-only relaxation also cannot drop the two polar constraints: `integral_normSq_paperFT_fejerTest_mul_arch_neg` supplies a prime-blind nonpolar negative test. Any next source estimate must retain polar divisibility and all integer samples simultaneously.
- 2026-10-07: Tail repair leaf passes `lake --old env lean`; four capstones pass scratch axiom audit with only propext/Classical.choice/Quot.sound. RHTower import wired. Formal lint has eleven unrelated unreachable-module errors, no WP02 error. Main card remains in progress; result BRIDGE / CONDITIONAL ADVANCE, RH open.
- 2026-10-07: Stronger next candidate: exact logarithmic asymptotic of normalized two-point repair energy. Corpus upper bound known; Laptev–Weth Theorem 4.1 supplies its general uncertainty parent. No novelty claim. The collective matched-ray lower energy, retaining all polar and integer constraints, remains the hard target.

## Cycle 2 — collective source residual

Previous turn classified PROGRESS: verified exact tail-repair certificate and changed the extension step. Main positivity frontier unchanged.

- Isolated repair log-cost conjecture meets logarithmic uncertainty parent theory; do not count its routine specialization as a significant research advance.
- Scalar spectral factorization of a finite autocorrelation mixture meets Krein/Boas–Kac factorization. Polar zeros must be allocated to both half-planes; C² regularity is not automatically preserved. No sign follows.
- Current exact candidate: analyze the actual narrow polar resonator with coefficients c(n)=1/sqrt(n). Its arithmetic quadratic form simplifies by the divisor identity sum_{d|n}Lambda(d)=log n. Determine the source archimedean residual after the leading log N cancellation, including cross terms, and whether it has an unconditional sign.
- [OPEN CORE]: asymptotic or exact control of the full archimedean cross term in this collective profile. A diagonal-only energy estimate cannot decide it.

## Cycle 3 — collective polar-packet coercivity

Cycle 2 harmonic vector rejected as a target producer: its multiplicative trace does not equal the exposing ray. Spectral factorization provides no missing sign. Verdict: NO-PROGRESS on source positivity; no Lean wrapper added.

Exact candidate: for w=1/(N+1), every complex coefficient vector c satisfies

    archEnergy(resonator N c w) >= (log(N+1)-C) * integral |paperFT(resonator N c w)|^2,

with one explicit C independent of N and c. No positivity premise. The zero vector and N=0 are included. All cross terms remain in the Fourier energy; disjointness is used only for the physical L2 masses of the packet and its compact polar primitive.

Paper mechanism: F=(D^2-1/4)G gives |Fhat|^2=(tau^2+1/4)^2|Ghat|^2. Disjoint supports give ||G||^2 <= R*w^4*||F||^2, with R=(integral Psi^2)/(integral (Psi'')^2). A scalar log inequality and the proved digamma lower bound yield the claim without integrating a separate logarithmic weight.

Attack: arbitrary destructive coefficient interference is retained by the multiplier identity; no estimate deletes cross terms. Single-bump N-scaling matches known logarithmic uncertainty. Parent literature and corpus identities make scientific novelty unestablished. Verdict SURVIVES PRELIMINARY ATTACK as a source-class boundary / BRIDGE, not RH positivity. General matched tests need not have the shrinking compact-primitive bound.

- 2026-10-07: `WeilWorkExposingRayPacketCoercivity.lean` passes final `lake --old env lean` with no warnings. Five public theorems establish exact Fourier multiplier, packet mass, primitive mass, inverse-mass bound and uniform logarithmic archimedean lower bound. RHTower umbrella wired. Heartbeat bottleneck fixed by specifying the function in the autocorrelation expression; no heartbeat increase. Axiom/lint audits underway.

## Next exact conjecture and attack

Can the packet lower bound remain valid, with C independent of the number of terms, for *overlapping* sums of the same polar bumps of width w, replacing log(N+1) by log(1/w)? This is the precise transfer needed before any density argument could turn packet positivity into general source positivity.

Attack priority: overlapping primitives can approximate a fixed broad smooth G while F=(D^2-1/4)G retains bounded energy. If the corpus's convolution approximation controls the actual archimedean form, this disproves the conjecture and identifies the missing overlap control. No density assertion is accepted without energy convergence. Positive survivor already formalized: coercivity follows from a small compact-primitive mass; disjointness is one concrete producer of that bound. This next attack is not counted as progress until its source and proof are checked.

- Final packet audit: exact-source scratch plus mathlib-name checks exited 0. Multiplier, inverse mass and coercivity use only propext/Classical.choice/Quot.sound. Index refreshed. Latest lint has seven unrelated unreachable modules, no WP02 error. Owned scratch/search artifacts cleaned. Main goal remains OPEN; scientific verdict BRIDGE / source-class boundary, not a global positivity producer.

## Cycle 4 — overlap attack and source reassessment

Previous goal turn: PROGRESS. Authoritative source now includes the checked coefficient-uniform coercivity theorem and umbrella import. Full exposing-ray receiver is still unproved.

Plan: corpus audit of actual archimedean-form convergence for overlapping polar translates; prove or refute the overlap extension on paper; extract the exact surviving mass/overlap control; then choose a source estimate addressing the full matched cone. Avoid adding another equivalent receiver or treating packet-space positivity as full positivity.

- Cycle 4 overlap extension: FALSE on paper. Smooth convolution plus finite H1 Riemann sums approximate a fixed broad polar test by arbitrarily narrow overlapping packets. Fourier mass stays positive and actual archimedean energy stays bounded. See OVERLAP-PROOF.md; no Lean no-go theorem claimed.
- Positive survivor chosen for formalization: for every finite overlapping packet F and its literal compact primitive G, and every real b, `(b-C_a) M(F) <= E(F)+exp(b)^4 M(G)/4`. No separation or positivity premise. This is the precise penalty hidden by the previous disjointness argument, not the full exposing-ray estimate.
- Reciprocal-resolvent convexity candidate meets known Stieltjes parent theory (Merkle 2004), so rejected as a separate scientific-novelty target. No extra receiver or convexity wrapper added.

- Stronger survivor: `exposingCompact_archimedean_primitive_bound` applies the same penalty inequality directly to every `CCMComplexSmoothInteriorSource a` primitive and its existing polarMultiplier. Exact-source scratch and axiom audit passed; standard three axioms only. The finite-overlap theorem also passes. Current full target-file audit and lint/index checks are running.
- Critical assessment: no scientific novelty beyond uncertainty parent theory established. The overlap obstruction changes the next action: no density transfer of a width-only bound. The new full smooth compact inequality retains the unresolved primitive mass explicitly. Coarse digamma constants and discarded positive remainders prevent identifying the sharp exposing endpoint from this bound alone.

## Next source question

The main conjecture remains the exact universal exposing-ray bound. Next attack should retain the actual gamma Gauss remainder and arithmetic samples, using the canonical compact primitive's Green representation to connect the new penalty to the matched trace. Source inspection of `CCMRestrictedWeilPolarGroundVariance` shows that source variance plus shifted positivity already has an arithmetic-zero-ground countermodel; repeating that mechanism cannot close the sign. No further coarse norm estimate or equivalent receiver is accepted as a producer.

- Cycle 4 final state: full compact-interface source theorem passes `lake --old env lean` without warnings. New capstone axiom audits use only the standard three. Index refreshed; existing umbrella import checked. Latest lint has twelve unrelated reachability errors, no WP02 finding. Owned temporary artifacts and processes cleaned. Main objective remains OPEN. Scientific verdict: source-control BRIDGE and verified positive survivor of the overlap obstruction, not an endpoint producer.

## Cycle 5 — literal ray and sampling structure

Previous turn: PROGRESS on the compact-primitive source inequality; exact endpoint remains open. Plan: audit the literal exposing trace and exact gamma/arithmetic residual; attack proposed improvements against current corpus; formalize only a dependency-closed statement that changes the source problem.

- Corpus frontier audit rejects scalar free-lag certificates, local finite-probe repairs, and width-only overlap transfer as endpoint producers. The retained prime-edge/gamma domination is still unpaid.
- Candidate: exact finite matched families approach the exposing threshold from above. This follows abstractly from existing all-level strong duality and the exposing upper bound (normalizing a positive multiplier, or appending a fixed ray realization to a negative zero-ray witness). Verdict BRIDGE / routine dual consequence; no new wrapper is being formalized and no explicit quantitative aperture rate is claimed.
- Literal kernel sign is not inferred from autocorrelation positivity: `polarExposingKernel c = polarShift c (polarShift c riemannKernelAutocorr)` has signed shifted terms. Search found no proved sign of the individual exposing coefficients. No sign conjecture is adopted without a source argument.
- Sampling candidate under audit: the exposing trace is nonzero at some integer, because its spectral density is a bounded nonnegative multiplier of Xi squared and the corpus's critical-rate Carlson theorem forbids blindness at all integers. If proved with the actual gamma decay, this connects the packet mass/coercivity obstruction to the literal ray. Need verify transform normalization, critical exponential integrability and infinite-mixture interchange; these are obligations, not established facts.

- Stronger literal-source conjecture selected: `exposingWeight n` is eventually strictly positive and `log(exposingWeight n)/n -> -2*pi*exp(-2)`; consequently the existing box/repair tail has every exponential upper rate below `2*pi*exp(-2)`. Full paper proof written in TAIL-SIGN-PROOF.md. Load-bearing source facts checked: exact leading theta lower bound and the sharp sub-pi theta decay theorem. The signed operator's outermost positive shift has distance two; every negative shift has distance at most one. This proves a separation of decay rates, retaining all k terms. Formalization in progress; no Lean result claimed yet.

- Formal implementation is being audited in `/tmp/wp02_tail_work.lean` before installation as `WeilWorkExposingRayTailAsymptotic.lean`. The initial source check found real/complex `exp` ambiguity; removed the unnecessary `Complex` opening. Direct leading-term polynomial absorption replaces the larger theta-threshold import. The two kernel envelopes, literal polar expansion, uniform infinite-mixture upper/lower bounds and eventual positivity are in the current scratch audit. Logarithmic-rate and box-tail proofs are drafted separately in `/tmp/wp02_tail_final.fragment`; not yet appended/audited. No new Lean theorem is claimed as complete.
- Scratch audit advanced to the full tail candidate: `/tmp/wp02_tail_work.lean` now includes the logarithmic-rate theorem, subcritical exponential tail bound, and strict tail positivity. The previous pass accepted the upper kernel estimate and later algebraic steps but reported a lower-bound proof-layout error and a non-definitional reassociation in the polar bound; both have been revised. All builds remain one owned foreground leaf process at a time. No heartbeat overrides or numerical jobs.

- Full tail scratch file exited 0. Installed `WeilWorkExposingRayTailAsymptotic.lean` and added its RHTower umbrella import. Exact-source axiom audit and final leaf audit are next. Public capstones prove eventual coefficient positivity, exact logarithmic decay, exponential upper bounds for the existing tail, and strict tail positivity. The generic theta-autocorrelation envelopes are also available in `RHTower.ExposingRayTail`.

- Exact-source axiom audit passed for both autocorrelation envelopes and all six new exposing/tail capstones: only propext, Classical.choice and Quot.sound. Final installed leaf audit is running. Interpretation corrected: double-exponential decay describes the literal tail budget, not an unavoidable precision barrier for all RH proofs; vanishing-slack compactness can bypass that rate.

## Next candidate after the tail theorem

Quantitative source realization, pending corpus search and attack: do universal constants C,K exist such that every sufficiently large cutoff N admits a finite family of actual polar C2 tests, all at apertures at most log(N)/2+C, whose nonnegative mixture has exact atom trace `exposingWeightTrunc N` at every integer n>=2, multiplier one, and total archimedean energy at most `archimedeanExposingThreshold + K*exposingTail N`?

Unlike abstract all-level feasibility, this asks for the natural aperture scale and the actual tail budget. Proposed producer: finitely many polar differences of truncated Phi, followed by exact two-point repairs. Unpaid estimates: uniform double-exponential weighted autocorrelation truncation error, uniform near-null energy bound and finite-mixture truncation with compatible aperture. The new positive exponential lower envelope for the tail could pay these errors after a fixed aperture shift. No result is claimed. Main universal lower bound remains the objective; this upper construction must not be mistaken for it.

- Final installed tail module exits 0 without warnings under `lake --old env lean`. The umbrella is wired, exact-source axiom checks passed, index refreshed (seven changed entries), and owned-file whitespace audit passed. Lint result is being recorded separately. Cycle verdict: PROGRESS on literal source-tail structure; universal exposing-ray positivity still OPEN. Novelty beyond the source-specific combination remains unclaimed.

- Latest lint exits 1 on seven unrelated unreachable modules: RHTower.WeilWorkDeficitArithmeticMean, RHTower.WeilWorkHigherDenominatorFiniteBoundary; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No WP02 module is flagged. Global lint is not clean; unrelated files were preserved.

- Cycle 5 cleanup complete: owned scratch/name/axiom files and search outputs removed; all owned foreground Lean/index/lint processes have exited. Durable proof, Lean module, report and next candidate remain. Goal stays active.

## Cycle 6 — uniform source truncation at the literal tail scale

- Revalidated cycle 5 capstones and all three umbrella imports. Two deep searches completed without partial flags; compiled coverage remains sparse/stale, so applicability checked against source. No universal source lower bound found.
- Exact natural-aperture realization candidate: for all large N, a finite polar matched family at aperture <= (log N)/2+C has t=1, exact full integer trace w_N, and archimedean energy <= E+K*tau_N. This is an UPPER construction; never substitutes for the universal lower bound.
- Attack verdict: BRIDGE. Abstract upper feasibility is routine conic duality; the quantitative source/aperture statement requires a new uniform rate. No scientific novelty beyond the specific literal-source refinement claimed. Main lower producer remains open.
- Selected dependency-closed substatement: uniformly in 0<=c<=1, the actual polar autocorrelation has weighted truncation error <= C exp(-exp(2(L-1))) exp(-2|y|), and its normalized archimedean energy differs from its literal limiting Lambda pairing by <= C exp(-exp(2(L-1))) for all large L. Paper proof in UNIFORM-TRUNCATION-PROOF.md before Lean.
- Plan: prove weighted theta envelope and correlation error; transfer through both polar shifts uniformly; combine with the actual near-radical zero-side estimate; leaf/axiom/lint audits; then assemble exact finite matched families. No change to main receiver.

- Complete uniform-truncation scratch passed without warnings. Installed module: `WeilWorkExposingRayUniformTruncation.lean`, with public `ExposingRayTruncation.autocorr_error`, `polar_autocorr_error`, `polar_pairing_error`, `archimedean_error`. Wired into RHTower. Final leaf and axiom audits pending.
- Stronger next exact statement now has a complete paper proof in REALIZATION-PROOF.md: fixed aperture overhead C, every epsilon>0, all sufficiently large N, exact finite matched trace w_N and energy <=E+(1+epsilon)*tau_N. Not yet formalized. Uses the actual eventual positive coefficient lower envelope to pay all residual errors; covers all integer atoms, not just primes.
- Anti-theatre: no literature-level novelty established. This is source construction progress, not universal lower positivity. Anti-laziness: hardest sign remains unsolved, no effort/size excuse used. Finish exact assembly, then confront the universal signed residual; do not accumulate further receiver reformulations.

### Cycle 6 handoff details for the next formal construction

`WeilDualBound` already accepts arbitrary finite index types, so use the disjoint union `(Fin J) Sum {n // n in Icc 2 M}`; no Fin reindexing wrapper is needed. `Fintype.sum_sum_type`, `Finset.sum_coe_sort`, and `Finset.sum_ite_eq` are the existing repair proof pattern in `WeilPositivityLinearDuality`. Actual atom normalization is `atomCoeff(twoPointResonator n s)m = 2*resonatorMass n*(if m=n then s else 0)`. For arbitrary residual r_n use |r_n|/(4*pi*mass_n), not the existing exposingRepairCoeff tied to w. `atomCoeff_eq_zero_of_floor_lt` handles ALL omitted integers. `weilTest_ofReal_eq` identifies actual source traces with the real autocorrelation.

For the weighted l1 repair bound, the existing source is `RHTower.WeilExcess.summable_log_add_mul_inv_sq` in `WeilFullConeNearNullPositiveDefinite.lean` (namespace verified): summability of `(2*log n+C)*(n^2)^-1` for C>=0. It dominates `(log n+boxConst)/n^2`. Avoid proving another generic summability wrapper unless needed for the exact construction. Own completed uniform-truncation and tail-asymptotic leaves may need cache .olean files before importing them; build only necessary leaves in the foreground, never a full umbrella.

- Cycle 6 complete verification: installed leaf exits 0 with no warnings; exact-source four-capstone axiom audit exits 0 with only propext/Classical.choice/Quot.sound. No owned processes remain. Nine owned temporary files cleaned after evidence capture. Latest lint has eight unrelated unreachable modules and no WP02 error. Main goal ACTIVE/OPEN. Next exact task is the full finite realization theorem in REALIZATION-PROOF.md, followed by renewed attack on the universal lower residual.

## Cycle 7 — exact finite matched realization

Previous turn PROGRESS: uniform source error capstones and final audits completed. Current source statements and all four umbrella imports revalidated. Plan: refresh corpus audit; build only required own leaf caches; formalize disjoint-union exact residual repair, finite mixture trace/energy errors, and natural-aperture tail comparison; final leaf/axiom/lint audits. Full WP02 lower inequality remains the unchanged objective. Quantitative existential upper bound is a construction milestone, not a positivity proof.

- Uniform-truncation and tail-asymptotic leaf caches built individually in foreground for the new construction; both exit 0. Current scratch `/tmp/wp02-cycle7-proof.lean` contains general exact residual repair, geometric finite-mixture error, actual polar source support/trace/energy estimates, full box-weighted residual cost, prescribed-cutoff realization, and eventual tail lower bound. Natural-aperture capstone drafted separately in `/tmp/wp02-cycle7-natural.txt` to append after current scratch process exits. First pass revealed only proof-code issues; no mathematical obstruction or weakened statement. Active scratch process is tool session 23378.

- Second scratch pass accepted exact atom matching, geometric summability, polar source support, and energy estimates after explicit source identities. Remaining errors concerned finite reindexing, inequality orientation, and algebraic normalization. All fixed in the next pass; natural-aperture capstone now appended to `/tmp/wp02-cycle7-proof.lean`. Active foreground Lean session 98320. No statement weakened, no heartbeat changes.

- Complete `/tmp/wp02-cycle7-proof.lean` passed without warnings; exact-source axiom audit for repair, at_cutoff, and natural_aperture reports only propext/Classical.choice/Quot.sound. Installed `WeilWorkExposingRayFiniteRealization.lean` (458 lines) and wired umbrella. Final installed leaf currently tool session 11661. Lint completed; diagnostics recorded separately before cleanup.
- Next hard-direction audit begun: can the OPPOSITE truncated trace -w_N be realized with energy <=-E+(1+epsilon)*tau_N? If valid, appending such a family would convert a below-threshold exposing witness into a negative zero-trace family. This is an exact source-production question, not a new RH receiver. Need corpus cone-uniqueness audit and serious falsification before adopting it. First deep search completed but returned no applicable producer; follow-up search `...cone singleton uniqueness without existence` is pending. No opposite-ray theorem claimed.

- Cycle 7 final audit: installed finite-realization leaf exits 0 with no warnings; all three public capstones use standard three axioms only. This completes the exact natural-aperture upper construction, not the universal lower bound. Eight unrelated lint reachability errors, none WP02. Source index and temporary cleanup follow final evidence capture.
- Next source conjecture is recorded exactly in OPPOSITE-RAY-CONJECTURE.md. Both deep searches completed; no applicable producer found in inspected hits. Candidate would force polar-cone uniqueness if a cone point exists; existing inspected exposure and order-comparable theorems do not prove it. Attack remains open; no Lean receiver or opposite-ray proof claimed.
- Anti-theatre: new quantitative construction in the corpus, literature novelty unestablished; no RH positivity claim. No effort estimate used to avoid hard work. Main gap is now expressly the universal lower residual; next cycle must attack a source mechanism that could address it, not refine the already-sufficient positive upper bound.

## Cycle 8 — opposite-ray production and cone obstruction

Previous turn PROGRESS: exact finite positive-ray realization completed and fully audited. Current capstone and all five umbrella imports revalidated. Plan: audit near-null positive-definite and critical-zero-carried cone source results; attack exact opposite-ray conjecture for contradiction, circularity, or known parent reduction; extract a nontrivial source theorem or obstruction; complete paper proof before Lean. Original universal lower inequality remains open and unchanged.

### Cycle 8: opposite-ray audit and far-polar leakage candidate

- Critical-zero-carried rigidity needs the carried-support premise. Near-null translated mixtures give a positive-definite deviation potential, not its vanishing. STATUS MUST-818 and prior bohr-route detection row 71 rule out treating tempered certificates or another uniqueness reformulation as a producer.
- Opposite-ray conjecture remains OPEN; no applicable separating cone point or construction found in inspected corpus hits. Recasting it as near-null prime-blind source production is REDISCOVERED, not progress.
- Concrete next attack: far polar corrections converge uniformly on the real Fourier line and have negative energy, but their full weighted atom-repair budget might diverge. Paper proof in POLAR-LEAKAGE-PROOF.md gives the sharp scale X exp(X), dominated by the secondary window near exp(2X). Formalize this exact survivor after source/API audit; do not interpret it as a lower bound for arbitrary coherent repairs.

Cycle 8 verification checkpoint: full sharp-scale budget bounds compiled without warnings in /tmp/wp02_cycle8_leakage.lean. Added exposing-target matchingBudget_lower; first audit found two local elaboration errors (simp branch and abs_add name), corrected and recompiling. Existing capstones report standard axioms; matching capstone axiom audit remains pending until compile succeeds. No project Lean file installed yet. Owned next candidate is LATTICE-REPAIR-CONJECTURE.md; search partial, applicability/novelty not yet established.

### Cycle 8 completed — PROGRESS, main target OPEN

- Installed sixth owned leaf `WeilWorkExposingRayPolarLeakage.lean` (358 lines), wired in RHTower umbrella. Exact complete repair budget has sharp scale X exp(X); exposing-target residual lower bound holds uniformly for every cutoff N. Actual far-polar tests retain negative energy and uniformly small traces.
- Complete scratch and final `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayPolarLeakage.lean` audits passed with no warnings. Four capstones use standard three axioms only. Lint fails on ten unrelated unreachable modules listed in EVIDENCE; no WP02 finding. Index refreshed two changed entries.
- Anti-theatre: no new universal positivity, no cone nonemptiness, no assumed uniqueness. New result is an analytic source diagnostic and exact quantitative survivor, not established external scientific novelty. Divergent box budget does not imply divergent optimal coherent repair energy.
- Anti-laziness: next primary conjecture attacks precisely that limitation: bounded coherent completion of the same sources via a compact smooth spectral factor, COHERENT-COMPLETION-CONJECTURE.md. Actual factorization/regularity/polar preservation must be proved without a premise. Even successful fixed total energy would still leave the zero-cost endpoint open. Common-profile lattice sampled mass identity is a secondary candidate, with known continuous polar moment parent.
- Final factorization searches: deep completed non-partial with no applicable producer in inspected hits; lexical rephrase and exact source search found Poisson/finite-rank factors. No absence claim. Uniform source-completion conjecture remains OPEN, no Lean started for it.
- Working memory: rh/weil_work_02_polar_leakage_2026_10_07. Main goal ACTIVE. No own running process, no subagents, no commits/push; cycle 8 temporary files removed at close.

### Cycle 9 started

Revalidated cycle 8 budget_bounds/matchingBudget_lower and all six umbrella imports. Previous turn PROGRESS. Primary target bounded coherent completion; inspect compact spectral factorization and actual profile regularity before new Lean. Initial source audit: the corpus only proves contDiff_flatBump and contDiff_fejerTest at order 2. Therefore the proposed differential majorant 8(D²-1/4)psi cannot yet be claimed C². Investigate a short polar SHIFT majorant instead: its real multiplier has a strictly positive gap, preserves the existing profile regularity and can remain below log(2)/2. Commensurate shifts may permit finite Laurent factorization with explicit allocation of both polar roots; continuous factorization remains an alternative, not an assumption.

Cycle 9 construction selected: positive FINITE geometric filter, avoiding both compact spectral factorization and quadrature. With N=ceil(200X), s=X/N, q=exp(-s/2), the actual farPolarTest X is a positive finite sum of translates of farPolarTest s, weights ((1+q²)/(1+q^(2N))) q^(j+k), j,k<N. Total weight is uniformly bounded because s>=1/201. Weighted variance of the translated short polar tests supplies a finite exact opposite-trace mixture at aperture X+17/50 and uniformly bounded repair energy. Every integer coefficient cancels by the exact Fourier density identity. Paper proof COHERENT-COMPLETION-PROOF.md written before Lean. This is finite-mixture target; single-test factorization remains stronger/unproved. Deep searches partial due semantic deadlines; available candidates/arguments inspected, no novelty claim. Lean scratch /tmp/wp02_cycle9_coherent.lean started; names audited separately in /tmp/wp02_cycle9_names.lean. No project Lean edits yet.

Cycle 9 intermediate verification: finite geometric Fourier mean, same-aperture polar support, translation modulus, and exact spectral variance identity compile successfully with default heartbeat limits. Uniform mass bound and integrated energy/atom identities are under audit; the final capstone and step-selection proof are drafted in a separate fragment while that foreground process runs. No numerical computation or new analytic premise. All exact-cancellation claims will be marked formal only after the complete leaf audit.

### Cycle 9 completed — PROGRESS, main target OPEN

- Seventh leaf `WeilWorkExposingRayCoherentCompletion.lean` installed, 478 lines, umbrella wired. Public `RHTower.ExposingRayCompletion.bounded_coherent_completion`: every X>=4 admits nonnegative finite actual polar repairs at aperture X+17/50, exact cancellation of every integer atom n>=2, and uniform repair-energy upper bound. Construction is the finite positive geometric filter and weighted variance from the paper proof.
- Full scratch and final `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayCoherentCompletion.lean` exit 0 without warnings. Capstone axiom audit: propext/Classical.choice/Quot.sound only. Default heartbeat limits; no numerical job, full build or umbrella build. Direct definition-bearing import replaces the broader exposed-duality import.
- Lint exits 1 with six unrelated unreachable modules, no WP02 error; names in EVIDENCE.md. Index exits 0, one changed entry. Scoped whitespace checks clean.
- Anti-theatre: exact bounded completion is real source-construction progress; external scientific novelty is unestablished, and neither PBAP nor the WP02 lower bound follows. Single-test factorization remains stronger/unproved and unnecessary for this finite dual cone.
- Anti-laziness: return to the literal opposite exposing source and its vanishing tail budget. Next candidate remains OPPOSITE-RAY-CONJECTURE.md; first unpaid step for a geometric filter on a truncated Riemann profile is its entire short-step integer trace, which no longer vanishes by support. Bounded energy alone does not pay that residual. Do not propose zero-cost Fejer completion without auditing critical-zero spectral compatibility.
- Main goal ACTIVE. No subagents or commits/push. Final process/temporary cleanup recorded below.

Cycle 9 cleanup complete: all owned Lean/search/lint/index processes exited; eleven owned temporary files removed after recording evidence. Durable memory: rh/weil_work_02_coherent_completion_2026_10_07. Next turn revalidate capstone and resume source-production audit; main goal remains ACTIVE.

### Cycle 10 started — source sign and endpoint audit

Previous turn PROGRESS. Revalidated bounded_coherent_completion, all seven imports, and exact WP02 receiver. Plan: (1) corpus/primary-source audit of opposite-ray mechanisms and small-shift residual; (2) attack uniform tail-sign conjecture for actual polar Riemann-kernel autocorrelations; (3) paper-proof then formalize a nontrivial survivor only if the source argument closes; (4) leaf/axiom/lint audits and next conjecture. No new analytic premise or numerical computation.

Fresh frontier map contains exact pole-vanishing ground gap >=1/10 at aperture log2/2, stronger than the generic small-aperture hits inspected in cycle9. This prevents treating that generic search as the true small-aperture frontier. The previous map's WP02 finite-realization status is stale relative to the completed owned source; retain the authoritative leaf proof.

Candidate under attack: exists Y, for every 0<c<=1 and y>=Y, polarExposingKernel c y>0. Existing fixed-shift envelopes suggest the sign but are NOT uniform as c tends to zero. Proposed missing invariant is positivity of (D²-1/4)² applied to the actual autocorrelation on a common tail; polar second differences then average this derivative with positive Green kernels. The actual theta derivative/tail identities must be found and proved; none is assumed. Finite positive mixtures of untruncated shifts are already excluded from exact blindness by Carlson, so count only a stronger positive sign/quantitative survivor as new work, not another blindness receiver.

Cycle 10 paper proof complete in POLAR-UNIFORM-TAIL-PROOF.md. Actual F=(D²-1/4)Phi has degree-four cusp polynomial with leading coefficient 16*pi^4; full-series bounds imply F*F(y)>=exp(-2*pi*exp(2)*exp(y)) eventually, after integrating an explicit envelope for EVERY negative contribution. Positive compact Green convolution then yields a common positive tail for all 0<c<=1 on paper. Scratch /tmp/wp02_cycle10_tail.lean formalizes the actual differential source and signed autocorrelation; current owned Lean handle 82572 is still running, never restarted on wait timeouts. Separate Green-identity fragment prepared, not yet appended. Full uniform shift result remains PAPER ONLY.
The preceding handle completed between observation and checkpoint writing: exit 1 with one local algebraic mismatch in the upper-envelope proof (negated exponential expression). Fixed that equality explicitly; the signed-autocorrelation proof itself was accepted. Appended exact one-step Green identity to scratch; current audit handle is 74591, returned by the foreground tool invocation.

Cycle 10 continued: full differential-source/Green scratch audit exits 0, five capstones use standard three axioms only. Generalized the signed-correlation estimate to common analytic envelopes; that refactor also exits 0 without warnings. Next exact step is the normalized Green average described in the paper addendum: it gives shift-independent envelopes and hence the actual uniform polar-autocorrelation sign. No project leaf installed yet; no full uniform Lean claim yet.

Cycle 10 full transfer now drafted: normalized positive Green averages have common signed-correlation envelopes; exact untruncated polar autocorrelation identity is accepted by Lean. The quantitative capstone gives fixed D,C>0 and Y with D*c^4*exp(-C*exp(y))<=polarExposingKernel c y for every 0<c<=1 and y>=Y. Previous complete audit found only three local issues in the added quartic normalization (interval-integral beta reduction and explicit polarWeight positivity); these are corrected in the current scratch. No heartbeat increase or numerical job. Final capstone still pending successful audit; scratch proof is not installed yet.

### Cycle 10 completed — PROGRESS, main target OPEN

- Eighth leaf `WeilWorkExposingRayUniformPolarTail.lean` installed (707 lines), umbrella wired. Capstones `ExposingRaySmallShift.polarExposingKernel_uniform_quartic_lower` and `polarExposingKernel_uniform_positive_tail`: fixed D,C>0 and Y work for ALL 0<c<=1 and y>=Y, with lower bound D*c^4*exp(-C*exp(y)). No hidden positivity or zero-location premise.
- Actual source theorem `(D²-1/4)Phi` has full-series envelopes. Signed autocorrelation proof pays all negative contributions; exact Green averaging cancels the small-shift normalization before bounding. Fixed-c outermost-shift dominance alone would not have established this uniform theorem.
- Complete scratch and final installed `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayUniformPolarTail.lean` pass without warnings. Seven capstones use standard three axioms only. No numerical job, heartbeat increase, full/umbrella build, subagent, commit or push.
- Lint exits 1 with fifteen unrelated reachability findings, none WP02; exact names in EVIDENCE.md. Index exits 0, five changed entries. Owned whitespace and prohibited-declaration checks clean.
- Anti-theatre: this is an unconditional literal-source theorem, not a universal energy estimate, cone nonemptiness, PBAP or RH. External scientific novelty remains unestablished; classical parents are acknowledged. The original exposed-dual receiver is unchanged and OPEN.
- Anti-laziness: no size/effort excuse used. Next source conjecture is recorded in COHERENT-GAP-CONJECTURE.md: the EXACT finite geometric completion has a positive uniform TOTAL energy floor. Fresh corpus search and source inspection supply the existing one-tenth small-aperture ground gap; C2/normalization and uniform source mass remain unpaid. Do not generalize this family-specific statement to arbitrary repairs. If already a direct known consequence, cite the bridge and move to a different opposite-ray source mechanism.
- Main goal ACTIVE. Final process and temporary cleanup follows the durable memory write.

Cycle 10 cleanup complete: every owned Lean/search/lint/index process exited; sixteen owned temporary files removed after evidence capture. Installed proof bodies matched the successful scratch exactly. Durable memory: rh/weil_work_02_uniform_polar_tail_2026_10_07. Next turn revalidate the two new capstones and all eight imports, then attack COHERENT-GAP-CONJECTURE.md using the actual corpus C2 energy bridge. Main goal remains ACTIVE.

### Cycle 11 started — geometric-completion endpoint

Previous turn PROGRESS. Revalidated the actual two uniform-tail capstones, eight umbrella imports, and exact WP02 universal receiver. Plan: audit the C2 restricted-Weil/archEnergy bridge and exact geometric-family energy normalization; attack the positive-total-energy-floor conjecture against current corpus and primary sources; if its proof closes, formalize the source-specific lower bound and audit it; otherwise extract the strongest valid survivor and move to another opposite-ray mechanism. Full WP02 objective remains unchanged. No generic positivity premise is admissible.

Cycle 11 paper argument recorded in COHERENT-GAP-PROOF.md. Partial deep search (Qdrant budget timeout) returned the exact existing halfLogTwo archimedean-form identity; this removes the boundary-prime term without a new support approximation. Every candidate/source hit and proposed ingredient set inspected; no absence claim. The only inspected C2/CCM overlap was the smooth-core bridge, which requires C-infinity. Direct weighted-L2 admission of the actual C2 source is therefore under Lean audit in /tmp/wp02_cycle11_gap.lean. Name audit completed (invalid namespace guesses corrected from source; valid measure scaling is Integrable.comp_mul_left' and Measure.integral_comp_mul_left). No project Lean edits yet. Proof uses the existing actual flatBump_eq_one to show the short source is nonzero; no numerical experiment.

Cycle 11 strengthening: the actual fixed plateau gives an explicit source norm bound, and the geometric multiplier at zero gives the exact invariant mass*(1-c_s)=1-c_(Ns). Together they predict a fixed positive total-energy floor for Ns>=4 even as s tends to zero. Recorded as a new conjecture with a dependency-closed paper proof before implementation; fresh corpus search running. This supersedes the weaker compact-step continuity argument. C2 admission/energy-transfer scratch remains under audit, with no project Lean change yet.

Cycle 11 verification checkpoint: exact C2 admission, both polar moments, archimedean normalization, and the half-log-two coercivity theorem pass Lean with only standard axioms. The explicit short-source plateau is accepted. A support-expression elaboration timeout was removed by using the actual MemLp interface; default heartbeat limits retained. One set-integral beta-reduction rewrite remains under final scratch audit, current handle 35290. Geometric-family mass-defect and total-energy capstones are drafted separately in /tmp/wp02_cycle11_completion.lean, awaiting the proved bridge import. No project Lean source installed yet. Next actual-source capacity candidate is recorded in LOCAL-SEED-CAPACITY-CONJECTURE.md, with generic Cauchy–Schwarz explicitly classified as a bridge rather than scientific novelty.

Cycle 11: installed C2/short-source leaf and necessary cache audit both pass with no warnings; umbrella wired. Complete geometric-completion scratch passes with standard axioms for mass_defect_identity, pointwise energy floor, and macroscopic uniform positive floor. Final scratch now generalizes the separation threshold to every X0>0 and records the original fixed-step conjecture as a direct corollary. No completion source edit installed until that pass finishes. The next mixed-seed capacity argument now has a full paper proof in LOCAL-SEED-CAPACITY-PROOF.md, including the literal k=0 truncated Riemann source and its exact 1/(2*pi) mixture normalization; no Lean theorem or arbitrary-repair obstruction is claimed for it yet.

### Cycle 11 completed source verification — PROGRESS, main target OPEN

- Ninth leaf `WeilWorkExposingRayCoherentGap.lean` installed (238 lines), direct RHTower umbrella import. Literal compact C2 admission, exact polar moments and Fourier normalization transfer the established one-tenth ground gap. Public `c2_halfLogTwo_coercivity` gives `(pi/5)*integral norm(f)^2<=archEnergy(f)` for actual half-log-two polar tests. Actual plateau gives `short_source_energy_floor` for ALL 0<=s<=1/200.
- Existing owned `WeilWorkExposingRayCoherentCompletion.lean` extended (550 lines). Public `mass_defect_identity`, `geometric_completion_energy_floor`, `geometric_completion_uniform_positive_floor` and `geometric_completion_fixed_step_gap` prove the exact cost floor and original conjecture. Any fixed X0>0 supplies a positive bound for Ns>=X0, even under s->0. Actual weight/mass/repair definitions exposed so the theorem specifies its concrete family.
- Both final installed sources pass `lake --old env lean -o <target-cache> <leaf>` with no warnings; only required target caches refreshed. Complete scratch capstones use standard axioms. Imported-cache eight-capstone axiom audit passed; every theorem uses only propext/Classical.choice/Quot.sound. No full/umbrella build, heartbeat increase, numerical job, new axiom, subagent, commit or push.
- Lint: 18 unrelated reachability findings, none WP02; names in EVIDENCE.md. Index exits 0 (two changed entries). Scoped whitespace/prohibited-declaration audits clean.
- Anti-theatre: this is an exact analytic source-family obstruction and positive quantitative survivor, with classical finite-variance/Cauchy–Schwarz and existing ground-gap parents. External scientific novelty unestablished. No arbitrary-repair positivity, cone nonemptiness, or RH claim. Universal WP02 lower frontier remains OPEN.
- Anti-laziness: no effort/size excuse used. The next conjecture already targets the literal exposing source, allowing UNEQUAL local seeds, arbitrary finite weights and translations. LOCAL-SEED-CAPACITY-PROOF.md has the full paper argument and source normalization; Lean remains outstanding. General capacity alone is a routine bridge; the actual fixed positive cost for the truncated Riemann source is the intended new survivor. Retain every integer residual before claiming any conclusion about the full opposite-ray producer.
- Main goal ACTIVE. Final axiom result, memory and owned-temp cleanup follow.

Cycle 11 closure: final imported-cache axiom audit exits 0; all eight public theorems use only standard three axioms. All owned Lean/search/lint/index processes exited. 15 owned temporary files removed after evidence capture. Durable memory: rh/weil_work_02_coherent_gap_2026_10_07. Main goal ACTIVE; next turn revalidate exact capstones and resume literal-source local-seed capacity audit.

### Cycle 12 started — literal Riemann-source local completion capacity

Previous turn PROGRESS. Revalidated exact C2 coercivity, all geometric gap capstones, nine umbrella imports and unchanged universal WP02 receiver. Current frontier map still calls the completed finite realization paper-only; owned audited source remains authoritative. Plan: fresh corpus/primary-source and falsification audit of LOCAL-SEED-CAPACITY-PROOF.md; formalize the full unequal-seed variance identity and actual truncated Riemann source floor if applicability closes; final leaf/axiom/lint audits; return to source mechanisms outside this local class. General Cauchy–Schwarz alone is a routine bridge and must not replace the literal source theorem or be sold as a global lower producer. No computation, new premise or heartbeat increase.

Cycle 12 intermediate audit: generic unequal-seed finite variance, translated-source/polar admission, signed-symbol energy identity, and all-real-frequency capacity pass a complete scratch audit with default heartbeats. The literal Riemann-source mass and exact first exposing-mixture weight are appended in the current scratch audit; not installed or claimed formal yet. Positive capacity uses the actual C2 half-log-two ground gap and the cutoff's retained central mass. Generic Cauchy–Schwarz remains a classical bridge, not a novelty claim. A second corpus query now audits mechanisms using only discrete integer traces, since full local variance completion has a fixed cost.

### Cycle 12 completed — PROGRESS, main target OPEN

- Tenth leaf `WeilWorkExposingRayLocalCapacity.lean` installed (389 lines), umbrella wired. Arbitrary unequal short C2 polar seeds, nonnegative weights and translations obey exact signed variance energy identity and all-frequency capacity kappa*|Fhat(t)|^2, kappa=pi/(5*log2). Actual truncated Riemann unit-shift source has cutoff-independent positive zero-frequency mass; every such completion pays riemannCapacity>0. Full finite exposing mixture pays at least riemannCapacity/(2*pi), including different finite seed types at each k.
- Full scratch and final `lake --old env lean -o <target-cache> <leaf>` pass without warnings. All nine public theorem axiom audits pass using only propext/Classical.choice/Quot.sound. Cache current; all ten imports present. Lint has seven unrelated reachability findings and no WP02 finding; exact names in EVIDENCE. Index exits 0, two changed entries. No numerical job, new axiom, heartbeat increase, full/umbrella build, subagents, commit or push.
- Anti-theatre: source-class obstruction plus exact positive survivor; classical variance/Cauchy–Schwarz ingredients, external novelty unestablished. Hard universal lower frontier remains OPEN. Arbitrary discrete atom repairs need not admit the local variance representation; no conclusion about their optimum follows.
- Anti-laziness: no size/effort excuse used. Next conjecture remains active in LATTICE-REPAIR-CONJECTURE.md: exact recovery of complete polar coefficient mass from rounded integer samples of arbitrary-spacing, common-Fejer-profile translates. Fresh corpus audit found the prior geometric radical outer-support/injective power-sampling theorem; a mere lattice nonexistence consequence is already known in a related class. Next cycle must attack the quantitative identity, every window-isolation/normalization detail, and its utility before Lean. Do not lose the all-integer residual or replace the main target with this subproblem.
- Main goal ACTIVE. Owned-process cleanup and durable memory recorded below.

Cycle 12 cleanup complete: all owned processes exited and thirteen temporary files removed after recording evidence. Durable memory: rh/weil_work_02_local_seed_capacity_2026_10_07. Next turn revalidate the literal-source/full-mixture capacity capstones and ten imports, then attack the sampled lattice mass conjecture against its existing geometric-grid parent. Main goal remains ACTIVE.

### Cycle 13 started — sampled polar mass on a separated profile lattice

Previous turn PROGRESS. Revalidated literal-source/full-exposing-mixture capacity capstones, ten owned imports, and unchanged universal WP02 receiver. Plan: fresh corpus/primary-source audit of the exact Fejer sampled mass candidate against the existing geometric-radical obstruction; derive and attack all rounding/window/polar identities on paper; formalize the full quantitative survivor only if it adds a useful source constraint; final leaf/axiom/lint audits and return to the universal signed lower problem. No computation, analytic premise, or heartbeat increase. The full objective is not replaced by this restricted source class.

Cycle 13 intermediate: fresh targeted search non-partial, all candidates/arguments inspected, complete 68,474-file inventory but predominantly pending/stale compiler metadata. No sampled mass producer among inspected results; no absence/novelty claim. Paper proof LATTICE-REPAIR-PROOF.md now includes the full polar defect and weighted stability, and shows one half-pole suffices. Current scratch accepts analytic rounding, every correlation-window isolation and the exact atom sample. Finite polar moment/stability/classification audit is running in one foreground Lean process; no project Lean file installed yet. Follow-up corpus query audits whether a discrete cosh moment survives overlap on the integer-base grid for the actual truncated Riemann profile.

### Cycle 13 completed — PROGRESS, main target OPEN

- Eleventh leaf `WeilWorkExposingRayLatticeMass.lean` installed (440 lines), umbrella wired, namespace `RHTower.ExposingRayLattice`. Exact rounded samples recover all Fejer-lattice covariance coefficients. `sampled_mass_balance` retains the polar defect of arbitrary complex coefficients; `mixture_mass_identity` and `mixture_mass_stability` give exact mass and weighted stability under only one actual half-pole. `exists_negative_sample` and `sampled_nonnegative_iff_zero_active` classify nonnegative sampled traces for nonnegative mixtures. All site counts/zero weights included.
- Full scratch and final `lake --old env lean -o <target-cache> <leaf>` pass without warnings. All seven public theorem axiom audits use only propext/Classical.choice/Quot.sound. Cache current; eleven imports present. Lint has ten unrelated reachability findings and no WP02 finding; EVIDENCE records names. Index exits 0, zero changed/removed at snapshot; generated references refreshed. No computation, heartbeat override, full/umbrella build, subagent, commit or push.
- Anti-theatre: exact source conservation and quantitative stability beyond a bare obstruction; generic covariance/pole algebra classical and external novelty unestablished. No universal signed energy lower bound. Do not count the existing geometric-radical injectivity theorem as new work, or infer bounds for arbitrary repairs.
- Anti-laziness: no effort/size excuse. Fresh corpus query supports a next paper mechanism in GEOMETRIC-POLAR-MASS-CONJECTURE.md: recover actual physical mass at b-power samples for overlapping truncated Riemann profiles on the log(b) grid. Its explicit utility gate asks whether the extra repeated half-pole zeros merely explain a known restriction. Before new Lean, audit applicability to the near-radical opposite-ray endpoint and every residual. If only another restricted no-go, classify/reject it and return to the complete arithmetic/Gamma floor. The original target remains unchanged and OPEN.
- All owned processes exited. Durable memory and temporary cleanup recorded below. Main goal ACTIVE.

Cycle 13 cleanup complete: nine owned temporary files removed, every own process terminal. Generated LEAN_API includes the new leaf's public declarations. Durable memory: rh/weil_work_02_lattice_mass_2026_10_07. Next turn revalidate the exact mass/stability/classification capstones and eleven imports, then run the overlapping-Riemann-source utility audit before deciding whether to formalize or reject that conjecture. Main goal ACTIVE.

### Cycle 14 started — utility gate and unrestricted signed estimate

Previous turn PROGRESS. Revalidated all seven lattice-mass capstones, eleven owned umbrella imports and unchanged universal WP02 receiver. Plan: audit the overlapping-profile conjecture's actual extra spectral constraints before any new Lean; search current corpus for the unpaid all-integer signed lower mechanism; attack a useful exact source statement on paper; formalize only a dependency-closed nontrivial survivor, then audit leaf/axioms/lint. Two fresh deep searches are running with finite budgets. No full build, numerical experiment, analytic premise or task narrowing.

Cycle14 utility gate rejects automatic formalization of overlapping geometric mass as another restricted diagnostic: its filter repeats half-pole zeros on an infinite frequency lattice, whereas the full target does not. Positive finite-convolution survivor and exact applicability limits recorded. New all-order source conjecture and full paper proof are DIFFERENTIAL-PARITY-CONJECTURE/PROOF.md. Actual F_k=D^(k+2)Phi-D^kPhi/4 has autocorrelation tail sign (-1)^k; theta leading coefficient, complete signed integral and superexponential error are explicitly paid. Odd orders would escape the previous even-source sign obstruction. Targeted search non-partial; novelty unestablished. Lean pending, universal energy bound OPEN.

Cycle14 intermediate verification: shared signed-tail error helper target-cache audit exits0 without warnings. First new scratch audit accepted the full adverse-contribution bound and convolution lower mechanism plus the literal complex Fourier identity; failures were explicit polynomial sign algebra, one absolute-value parse, and beta-reduction/pole rewrites. Corrected with algebra, default limits retained. Second complete audit running, no new leaf installed. Next source mechanism is COMPACT-ODD-SOURCE-CONJECTURE.md: nonnegative cutoff plus exact odd core moment correction, with the entire boundary tail retained; no energy or exact opposite-proportion claim. Follow-up compact-source search partial; retrieved support/derivative bridges do not pay these obligations.
