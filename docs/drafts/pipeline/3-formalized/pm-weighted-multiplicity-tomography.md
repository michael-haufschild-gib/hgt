# Weighted multiplicity tomography of the physical Fermi witness form

- **ID:** pm-weighted-multiplicity-tomography
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route PM; exact unweighted index and general Mellin-exponent removability
- **Statement:** For each intrinsic parameter `0<a<1`, the negative index of the literal weighted dyadic form equals total analytic multiplicity of zeta zeros with `1-a<Re rho<1`.
- **Novelty:** Scoped corpus/public searches found general zero-free-strip and `L^p` receivers but no matching weighted multiplicity index; global novelty unverified.

## Goal

Turn the canonical PM index into a source-based multiplicity profile across vertical thresholds.
At `a=1/2` recover the exact RH obstruction. Identify the regularity wall without assuming a
zero-location theorem. This remains a receiver until an independent weighted source bound exists.

## Gates

- [x] 0 → 1: source-pure definitions and mechanism specified
- [x] 1 → 2: dependency-closed weighted source and analytic proof recorded below
- [x] 2 → 3: all three actual leaves and all 48 declarations audited; global lint exception recorded below
- [ ] 3 → 4: standalone publication and completed novelty review

## Exact proposed definitions

`W_a` consists of continuous complex functions on `(0,1]`, orthogonal to every actual generator
`phi_b`, `b≥1`, and with finite weighted squared norm

`E_a(w)=integral_0^1 t^(2a-1) |w(t)|² dt`.

`q_a(u,v)=integral_0^(1/2) t^(2a-1) u conj(v) - 2^(-2a) integral_0^1 t^(2a-1) u conj(v)`.

Let `M_a` be the extended supremum of finite analytic-multiplicity sums over actual zeta zeros
with `1-a<Re rho<1`. Proved: `ind_-(q_a|W_a)=M_a`, without RH, simplicity or finite-zero premises.

## Mechanism to audit

1. Weighted Cauchy–Schwarz gives Mellin exponent `a` and the boundary estimate
   `witnessMajorant(w,x) ≤ sqrt(E_a(w))/sqrt(2(x-a))`, `x>a`. It also gives ordinary `L¹`
   because `a<1`. Thus the actual correlation remains analytic for `Re s>0`.
2. Every zero jet `t^(conj(rho)-1) log^j(t)`, `j<ord_rho(zeta)`, belongs to `W_a` exactly on
   the required strict integrability side `Re rho>1-a`. Source orthogonality is the same literal
   derivative identity already proved; weighted integrability is a separate obligation.
3. Spurious witnesses remain admitted for every `a>0` and are neutral for `q_a`. Direct power
   integration gives the normalized coupling denominator at the shifted spurious node
   `d_l+1-2a` and numerator `2^(1-2a)c(rho)`, where `c(rho)=2^(-rho)-1/2`.
   Shifted nodes have real part `1-2a`, strictly below every admitted zero `Re rho>1-a`.
4. Divide the logarithmic jet normalization by this numerator. Existing confluent Cauchy
   controllability and the same Hermitian graph completion should produce both signed blocks
   with one slot per multiplicity.
5. Zero correlation jets at all admitted zeros clear all possible left-defect poles in
   `Re z<a`. The already proved general removability theorem, with the estimate in step 1,
   should force self-similarity. The weighted form then vanishes by change of variable.
6. Negative families therefore inject into the admitted multiplicity coordinates. The finite/
   infinite counting split is the same intrinsic argument as in the canonical index theorem.

## Critique and boundaries

- The weight and subtraction coefficient must move together; keeping coefficient `1/2` would
  destroy spurious neutrality and would test a different object.
- For `a>1/2`, admitted zero jets need not be ordinary `L²` witnesses. Do not reuse ordinary
  witness membership there; use the literal source pairing and weighted integrability separately.
- At `a=0`, spurious modes leave the weighted space; that endpoint is not covered by this formula.
- Unconditional Hardy input now gives infinite weighted negative index for every `1/2<a<1`;
  see `3-formalized/pm-weighted-critical-index-saturation.md`. This is saturation above the
  boundary; a jump at `a=1/2` is not claimed because its index is not yet controlled.
- An exact index profile does not supply the source nonnegative-half-mass bound needed for RH.

## Prior research

Corpus query `weighted Fermi multiplicity negative index zero free strip --any --module FermiNyman`
reported `partial: true`. Hits include `no_zeta_zero_of_fermiNymanWitnessLp_selfSimilar`,
`zetaZeroFreeStrip_iff_mellinFermiWitness_selfSimilar`, general removability, and the new canonical
index. No weighted multiplicity theorem surfaced. Public weighted-Nyman/negative-index/inertia
queries found no exact match; absence is not certified.

## Log

- 2026-09-29 — created; no weighted Lean implementation started. Current rank/kernel/source-classification audits take priority.

- 2026-09-30 — resumed from current source: all three prior rank/kernel/classification cards are Stage 3, with recorded actual-leaf/axiom audits. New corpus search returned the same source frontier (`partial: true`, full inventoried source coverage, mostly pending/stale compiler coverage); no source positivity producer appeared. Existing unrelated dirty files preserved.
- Plan: (1) audit weighted admission and exact literal pairing; (2) extend finite multiplicity completion and correlation cancellation; (3) audit actual leaves, axioms, umbrella reachability and formal lint; (4) use the resulting parameter dependence to test a source-bound conjecture. No weighted equality or RH claim before these obligations close. `update_plan` and `multi_tool_use.parallel` are unavailable; this card records the plan and independent tool reads use `Promise.allSettled`.
- Parameter audit: weighted power energy has exponent `2(a+Re rho-1)-1`, so a mode enters exactly at `a>1-Re rho`. At entry its squared norm diverges as `1/(2(a+Re rho-1))`. Thus ordinary continuity of fixed source coefficients cannot by itself keep the index constant across thresholds; a uniform domain/norm estimate is a separate obligation.
- Weighted admission/pairing draft: compiler accepted sharp power integrability equivalence, exact weighted power energy, all-order logarithmic admission, spurious neutrality, conjugate symmetry, weighted integrability and finite-sum algebra. The combined scratch reported only an unavailable nonvanishing lemma in the later signature block; replaced with the locally verified `Complex.cpow_ne_zero_iff`. New actual leaf `FermiNymanWeightedWitness.lean` awaits targeted build/direct audit. A distinct-zero negative-family construction is drafted separately; no weighted index theorem is claimed yet.
- Distinct-zero negative-block paper proof is complete: source-admitted powers couple to neutral spurious modes by the Cauchy matrix with translated nodes `d_l+1-2a`. Separation follows from `Re rho>1-a>1-2a`; source-unit nonvanishing follows from `Re rho<1`. Hermitian graph completion gives `-I_n`. With the corpus's unconditional dyadic Hardy theorem, every `1/2<a<1` admits arbitrary finite negative blocks, hence has infinite negative index. This is an unconditional saturation statement; a jump at `a=1/2` is not asserted without controlling the canonical index. Exact multiplicity equality for all weights remains open.
- Actual weighted source leaf passed targeted `lake --old build +GaloisForLFunctions.RHTower.FermiNymanWeightedWitness:olean` (170s for new leaf; dependency logs replayed). No new-leaf warning/error appeared. Wired into `RHTower.lean`; direct actual-leaf and axiom audits still pending. The distinct-zero construction plus unconditional Hardy saturation scratch is now compiling, sequentially.
- Combined signature/Hardy scratch passed exit 0 without warnings. `FermiNymanWeightedSignature.lean` now records the distinct-zero negative blocks, intrinsic weighted index, exact canonical specialization, and unconditional supercritical infinity; `weightedWitnessNegIndex_boundary_profile` has no hypothesis parameters. Targeted actual-leaf build and final direct/axiom audits are next. This milestone does not close the full weighted multiplicity conjecture or RH.
- Actual signature leaf passed targeted old-mode build (163s new leaf); both new modules are wired. Final direct `lake env lean` on `FermiNymanWeightedWitness.lean` passed exit 0 with empty diagnostics. Signature direct audit is running. Index regeneration completed. `lint --check-generated` exited 1 solely for 14 unrelated unreachable RHTower modules; no finding on either PM leaf. No full/umbrella build or numerical experiment was run.
- Independent producer search completed in 230s with `partial: false`, no unfinished stages/errors, full source inventory, but mostly pending/stale compiler metadata. Reviewed all returned candidate statements and source arguments. Proposed “Dilation inversion symmetry” ingredient uses `SoninL2Model` on all of `L²(ℝ)`, with the amplitude `sqrt(a)`; it does not supply isometry of the compressed PM witness dilation. `EulerDeletionRamareDilationEnergy` retains the moving lower boundary and proves covariance, not a signed source bound. Neither discharges PM half-mass positivity. No independent producer was found among these returned hits.
- Next exact tomography obligation: use `fermiWeightTwist` and `witnessMajorant_le_of_sq` to obtain the general boundary rate; then extend correlation-order cancellation to `1-a<Re rho<1`, weighted normalized log-jet coupling and multiplicity-exact counting. These remain unfinished, as does the independent source estimate required for RH.
- Final signature direct audit passed exit 0 with no diagnostics. Axiom audit of all 42 new declarations plus `exists_riemannZeta_line_zero_dyadic` passed exit 0: only `propext`, `Classical.choice`, `Quot.sound`. Exact capstone type confirms no hypothesis parameters. All 42 names have no duplicate declaration elsewhere in the owned Lean tree. Saturation card promoted to Stage 3. Full weighted multiplicity equality and unconditional RH remain unproved; goal stays active.

- Weighted cancellation continuation: corpus search `weighted Fermi correlation order cancellation --any --module FermiNyman` returned useful source hits with `partial: true` (text/source retrieval interrupted), complete source inventory, mostly pending/stale compiler metadata. Reviewed all 20 candidate and 20 source-argument statements. Draft weighted boundary rate, conjugate Mellin witness, and correlation-order removability passed the first compiler pass except one missing explicit measure annotation in a nonnegative integral. No new source positivity result surfaced. Next: close the weighted jet-kernel upper bound, then multiplicity lower construction.

- Weighted upper-bound scratch passed `lake env lean` exit 0 with empty diagnostics. It proves the boundary rate, correlation-order cancellation, jet linearity, self-similar weighted neutrality, and `weightedWitnessNegIndex a ≤ weightedStripMultiplicityCount a` for `0≤a<1`, including infinite zero sets. New `FermiNymanWeightedCorrelation.lean` awaits actual-leaf build and audit. The lower-bound scratch now derives logarithmic pairings from shifted Mellin transforms; not yet verified.

## Dependency-closed weighted proof audit (2026-09-30)

The source-weight twist `T_a w(t)=t^(a-1/2)w(t)` has ordinary square integral equal to
`E_a(w)`. The existing elementary square-integral majorant applied at `x-a+1/2` gives
`M_w(x) ≤ (1+E_a(w))/(2 sqrt(x-a))` for `x>a`. This weaker constant already meets the
proved general Mellin-removability receiver. For `a<1`, the source pairing is integrable;
its actual correlation density is bounded and vanishes for scales at least one, hence
its Mellin transform is analytic throughout `Re s>0`.

At a possible left-defect pole `z`, the corresponding zero is `rho=1-z`, with
`1-a<Re rho<1`. Vanishing correlation derivatives through order `ord_rho(zeta)-1`
puts numerator order at least denominator order. Thus every such pole is removable,
and the boundary estimate forces `w(t/2)=w(t)`. The identity
`(t/2)^(2a-1)=2*2^(-2a)*t^(2a-1)` then gives `q_a(w,w)=0`. For any negative Gram
family, the form of a coefficient sum is `-sum |c_i|²`; a zero jet packet therefore
forces every coefficient to vanish. Finite-dimensional injection gives the upper
multiplicity bound when the zero set is finite; an infinite zero set has infinite
extended multiplicity count, so the upper bound remains valid without finiteness.

For the reverse inequality, write `delta=2a-1`, `K=2^(1-2a)` and
`d_l(a)=d_l+1-2a`. The cutoff Mellin transforms evaluated at `rho+delta` give the literal
weighted logarithmic pairings. Differentiating the already proved weighted power
pairing yields `D^j[K*c(rho)/(rho-d_l(a))]`. Normalize each jet using derivatives of
`(K*c)^(-1)` and Leibniz's rule. The resulting pairing is exactly
`(-1)^j*j!/(rho-d_l(a))^(j+1)`. The source numerator is nonzero for `Re rho<1`;
node separation follows from `Re rho>1-a>1-2a`, using `a>0`.

Existing confluent Cauchy surjectivity gives finite spurious combinations dual to every
finite admitted multiplicity packet. These combinations are neutral. Hermitian graph
completion with coefficient matrix `(r*I-Q)/2` gives mutually orthogonal positive and
negative identity blocks (`r=1,-1`). Taking the supremum of all finite zero packets
gives the reverse extended-index bound. This proof uses actual source orthogonality,
not a zero-location assumption, and includes repeated zeros. The lower construction
is still under Lean audit; this paper argument is not a claim that its formalization
has passed.

- `FermiNymanWeightedCorrelation.lean` passed its targeted old-mode build (89s for the new leaf), with no new-leaf diagnostics. It is wired into `RHTower.lean`. The combined lower-coupling and exact multiplicity scratch is checking against this built leaf. Endpoint search `self similar weighted integrable vanishing endpoint --any --module FermiNyman` returned useful hits but was partial (text/source stages interrupted), with complete inventoried source coverage and mostly pending/stale compiler metadata. All returned candidate/source statements were reviewed. It exposes the existing `a=0` Mellin growth receiver; no weighted endpoint-vanishing theorem appeared in those hits.

- Full weighted tomography scratch passed exit 0 with empty diagnostics. Actual leaves now comprise `FermiNymanWeightedCorrelation` (24 declarations), `FermiNymanWeightedConfluentCoupling` (12), and `FermiNymanWeightedMultiplicity` (12). All 48 declaration names were checked exhaustively against owned Lean sources: no outside duplicate. All three leaves are wired. The hypothesis-free capstone `weightedWitnessNegIndex_multiplicity_profile` quantifies over every `a∈(0,1)`, with no simplicity or finite-zero premise. Targeted builds and final actual-leaf/axiom audits are in progress; stage promotion awaits them.

- Both remaining actual leaves passed their targeted old-mode build: weighted confluent coupling 174s, weighted multiplicity 13s. All three actual leaves are now in the sequential final `lake env lean` audit, followed by the 48-declaration axiom audit. Initial `lint --check-generated` exited 1 for 21 unrelated unwired modules and concurrent staleness of `LEAN_API.md`/`LEAN_OVERVIEW.md`; no PM finding. Generated indexes will be refreshed once more after source activity is checked.

## Final formal certificate (2026-09-30)

`RHTower.weightedWitnessNegIndex_multiplicity_profile` in
`FermiNymanWeightedMultiplicity.lean` proves, without external premises:

```lean
∀ a ∈ Set.Ioo (0 : ℝ) 1,
  weightedWitnessNegIndex a = weightedStripMultiplicityCount a
```

- `FermiNymanWeightedCorrelation`: 24 declarations, targeted build passed (89s).
- `FermiNymanWeightedConfluentCoupling`: 12 declarations, targeted build passed (174s).
- `FermiNymanWeightedMultiplicity`: 12 declarations, targeted build passed (13s).
- Final direct `lake env lean` on each actual leaf: exit 0, empty diagnostics.
- All 48 declarations audited with `#print axioms` in a separate scratch: exit 0;
  axiom union exactly `propext`, `Classical.choice`, `Quot.sound`.
- Exact capstone type checked; all 48 names checked against owned sources without duplicates.
- All three leaves wired into `RHTower.lean`; generated indexes refreshed.
- Final `scripts/formal_tools.py lint --check-generated`: exit 1 solely for 17 unrelated
  unreachable modules listed below. No stale generated file or PM-leaf finding remained.
  This is a recorded global gate failure, not a claim of a clean global lint run.
- No full/umbrella build, new axiom, proof hole, numerical experiment, heartbeat increase,
  commit or push. Owned scratch files cleaned after recording results.

Global lint exceptions: `CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
`MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
`PrimeSmallDeviationArithmetic`, `SpeiserExactCount`, `ThetaMovingShellFirstOrderPhase`,
`WeilLittleODeviationHarmonicConvergence`, `WeilLittleOVonMangoldtRigidity`,
`ZetaNotchRampMainTerm`, `ZetaNotchRefinedEnvelope`, `ZetaNotchTruncatedDiagonal`,
`ZetaZeroDensityPowerSaving`.

This closes weighted multiplicity tomography. It does not supply the independent source
bound forcing the canonical index to zero. RH remains unproved and the user goal remains
active. Next candidate: `3-formalized/pm-weight-zero-domain-boundary.md`; endpoint domain
classification and its failure to provide uniform positive-weight control.

- Subsequent endpoint audit closed: see the Stage-3 domain-boundary card. The raw-coefficient source test is now closed with a formal positive survivor in `5-failed/pm-raw-mobius-haar-tail-floor.md`; active successor is `1-in-progress/pm-log-smoothed-mobius-haar.md`. RH remains open.
