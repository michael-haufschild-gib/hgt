# Exact first-probe interpolation and mixed-sign convergence obstruction

Status: FORMALIZED. Dependency-closed paper proof, final leaf compile/export,
and all public axiom audits passed on 2026-10-09.

Source policy: our Lean corpus only. No external papers or web searches.

## Corpus audit

- `WeilFinitePanelPositiveCompletion.lean` supplies lift indices N_k strictly
  between exp(2(k+1)) and 2exp(2(k+1)), a positive first-probe slope there, and
  the exact single-spike affine response for arbitrary signed spike size.
- `WeilTailPanelSharpPrefix.lean` supplies exact first-probe finite-head
  invariance through its sharp support boundary, below 2exp(2(k+1)).
- `WeilTailPanelPositiveCompletion.lean` supplies the stabilization/diagonal
  construction for positive completions, but only inequalities, not arbitrary
  exact real histories.
- `WeilLogShiftArithmeticDomain.lean` lifts arbitrary weights to coefficients.
- `WeilLogShiftLocalExcessDomain.lean` and `WeilLogShiftReflection.lean` give
  the two local moment plus one-sided probe-bound criteria.

## Conjecture and paper proof

For any baseline coefficients, base cutoff, and real sequence h, realize
Q_2(base+j+1)=h_j exactly while preserving every coefficient outside the lift
indices and the initial finite head. At stage j change only N_(base+j), using
the nonzero affine slope to solve one scalar equation. Later lift coordinates
lie beyond the entire support of earlier first probes because exp(2)>3.
Each coefficient stabilizes; the diagonal sequence agrees with the completed
stage on the required finite head. Hence every earlier exact equation survives.

For a convergence obstruction choose the baseline lift of
v_n=1/pairedLogKernel(log 2,n). The coordinates N_j+1 lie strictly between
consecutive lift indices (again exp(2)>3), so interpolation leaves them intact.
At these arbitrarily large coordinates the positive-excess potential term is
exactly one. Thus its series is not summable, and neither is the signed series.
Choose h identically zero. All positive integer-cutoff first probes are exactly
zero. If the deficit moment were summable, the existing local-deficit plus
upper-bound criterion would force signed summability, contradiction. Both local
moments therefore diverge despite the bounded (indeed constant) integer probe.

This concerns integer cutoffs. It makes no boundedness claim for intervening
real cutoffs and no assertion about all probe indices simultaneously.

## Positive survivor / no-go closure

Exact arbitrary first-probe histories with preserved off-lift coordinates and
finite head are the positive interpolation theorem. The counterexample is an
application, not the only outcome. No new unproved analytic premises.

## Formal result

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftFirstProbeInterpolation.lean`.

- `weilLogShiftFirstProbe lam k` is the real m=2 probe at cutoff k+1.
- `exists_weilLogShiftFirstProbe_exact_completion`: a signed spike solves one
  first-probe value equation exactly.
- `exists_weilLogShiftFirstProbe_interpolation`: arbitrary exact tail history,
  prescribed initial head, and preservation of all off-lift coordinates.
- `weilLogShiftFirstProbe_surjective`: every real sequence is a first-probe
  integer-cutoff history.
- `exists_weilLogShiftFirstProbe_history_nonsummable`: every such history occurs
  with nonsummable excess and signed potentials at log 2.
- `exists_zero_firstProbe_with_divergent_excess_and_deficit`: the history can
  be identically zero while both local one-sided moments and the signed moment
  fail summability.

This closes the previously unclassified bounded-integer-probe example with
both local moments divergent. Real-cutoff boundedness remains unproved.

## Verification

- Final leaf compile/export: exit 0, no diagnostics. First pass identified one
  affine-response parenthesization mismatch, corrected before final verification.
- All six public declarations: exactly `[propext, Classical.choice, Quot.sound]`.
- Umbrella import wired; index refreshed; all six API entries inspected.
- Global lint: exit 1, seven unrelated modules unreachable from their umbrellas:
  `RHTower.CCMNonnegativeGroundStateRH`,
  `RHTower.PaperCirclePredictionChannelTransport`,
  `HTGeometry.CStarEnvelope`, `HTGeometry.CompactKernelAlgebra`,
  `HTGeometry.CompactKernelL2Representation`,
  `HTGeometry.CompactKernelRankOneDensity`,
  `HTGeometry.RealTranslationCrossedProduct`.
  No error concerns this leaf. These out-of-scope modules were not modified.
- No web, external paper, numerical experiment, new analytic premise/axiom,
  heartbeat increase, umbrella build, commit, push, or subagent.

The failed receiver and its exact interpolation survivor are recorded in
`../5-failed/weil-logshift-bounded-mixed-first-probe-no-go.md`.

## Follow-up: reconstruction conjecture proved

`WeilLogShiftCutoffReconstruction.lean` now proves that the countable mesh
L_n=(log(n+1)-log 2)/2 reconstructs every coefficient at n>=2. Each row sees
exactly the coefficient head through n and has a positive diagonal. Finite-prefix
sample equality iff coefficient equality, full mesh equality iff coefficient
equality, and positive-real-cutoff history equality iff coefficient equality
are formalized. An explicit existence theorem separates identical integer
histories on this finer mesh. See `weil-logshift-cutoff-reconstruction.md`.
Final compilation, all thirteen public axiom audits, and global formal lint
passed for that follow-up. Real-cutoff boundedness of the divergent example
in this card remains unproved.
