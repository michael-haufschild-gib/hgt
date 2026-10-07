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
