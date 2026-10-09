# One moving log-shift probe exposes the summable majorant boundary

- **ID:** weil-logshift-diagonal-moment-limit
- **Stage:** 3-formalized
- **Source policy:** Lean corpus only. No external papers, numerical experiments,
  heartbeat increases, full builds or umbrella builds.
- **Write scope:** new Lean leaf, umbrella import, generated index, this card,
  owned scratch and cross-session memory.

## Context and exact conjecture

Previous turn proved progress: countable log-shift positivity admits an exact
single deficit with finite deficit support and failure of full Weil positivity.
That construction does not settle summable excess. The unrestricted summable-
excess replacement remains open; this increment isolates its majorant boundary
and the signed moment that obstructs a general extension.

Put a(n)=WeilExcess.weilDeviation(lam,n), K=riemannAutocorr, and
Q_k(lam)=Re W_lam(weilTest(f_k,f_k)), where
f_k=logShiftRiemannDifference(k,log(k+2)).

Selected conjecture: for every lam with summable |a|,

    Q_k(lam) -> -4 * sum_n a(n) K(log n).

Consequently eventual nonnegativity of this ONE probe per window forces the
signed K-moment nonpositive. For coefficient majorants lam>=Lambda on n>=2,
summable excess and eventual nonnegativity force exact equality on n>=2.
This removes full Weil positivity and almost all log-shift tests in that sector.

## Attack and corpus audit

- Existing majorant rigidity assumes full Weil positivity; existing countable
  rigidity applies to minorants. Tail completion shows that removing the excess
  bound would make the proposed majorant claim false.
- Exact `logShift majorant` lexical query: zero declarations. Exhaustive source
  search for log-shift moment/diagonal/limit results found no matching theorem.
- Existing kernel machinery supplies pointwise truncation convergence,
  exponential decay, uniform paired-kernel bound 4K(0), and near-radical energy
  decay faster than exp(-2k). Thus no unproved analytic input is needed.
- Verdict: SURVIVES PRELIMINARY ATTACK as a corpus premise reduction and exact
  asymptotic law. External novelty unassessed under the user's source restriction.

## Dependency-closed paper proof

1. k+2<=exp(2k) for integer k>=1 by exp(x)>=1+x. Thus every sufficiently late
   diagonal probe belongs to the original countable panel.
2. The von Mangoldt functional equals the zero-side form. Its norm is bounded
   by (1+sqrt(k+2))^2 times near-radical energy, at most 4exp(2k) times that
   energy for k>=1; the existing uniform energy theorem sends this to zero.
3. The paired arithmetic kernel is
   4K_k(log n)-2K_k(log n+log(k+2))-2K_k(log n-log(k+2)).
   Its first term converges to 4K(log n). The shifted terms tend to zero by
   nonnegativity, K_k<=K and exponential decay, since log(k+2) tends to infinity.
4. Its absolute value is bounded by 4K(0), uniformly in k and n. Summability
   of |a| permits dominated convergence of the arithmetic sum. The exact
   functional decomposition gives the claimed signed limit.
5. An eventually nonnegative real sequence has nonnegative limit, so the
   signed moment is nonpositive. For a majorant, a>=0 and K(log n)>0. The sum
   is also nonnegative; hence every summand, and every a(n), vanishes.
6. Summable raw excess supplies summable |a| in the majorant sector; n<2 is
   removed by the existing guarded deviation definition. Dividing by sqrt n
   is reversible for n>=2. No RH or full-positivity premise enters these steps.
7. The boundary is inhabited: apply the existing prescribed-head completion to
   Lambda plus exp(t)*sqrt(2) at n=2. It preserves that positive excess and
   dominates Lambda everywhere while satisfying every countable log-shift test.
   The new majorant rigidity then proves its excess is not summable. This
   existential sharpness statement adds no analytic premise.

## Work log

- [x] Read objective; classify previous turn as verified progress.
- [x] Audit corpus and attack exact statement.
- [x] Close exact paper proof before Lean implementation.
- [x] Formalize exact limit and majorant consequence; leaf and axiom audits.
- [x] Wire, index, formal lint and promote card.
- [x] All owned jobs terminal; removed all 11 inventoried scratch files and
  verified absence. Recorded `research/weil-logshift-diagonal-moment-2026-10-09`.

**[PAPER PROVED; LEAN VERIFIED]**

## Implemented result and significance audit

Source: `formal/GaloisForLFunctions/RHTower/WeilLogShiftDiagonalMoment.lean`.

- `tendsto_weilLogShiftDiagonalProbe`: exact signed moment limit for summable
  absolute normalized deviation, without any positivity premise.
- `weilLogShiftDiagonal_moment_nonpos`: eventual diagonal positivity forces
  that moment nonpositive.
- `eq_vonMangoldt_of_eventually_diagonal_nonneg_of_summable_excess`: majorant
  rigidity from eventual positivity of one probe per window.
- `weilLogShiftSummableMajorants_subset_exact`: the original countable
  predicate gives this rigidity in the summable-excess majorant sector.
- `exists_weilLogShift_majorant_infinite_excess`: an unconditional existential
  family of strict majorants satisfying every countable test, with any exp(t)
  normalized excess at 2, and non-summable total normalized excess.

This moves the corpus frontier by identifying the exact scalar observable of
escaping log-shift probes and removing full-cone positivity in one existing
rigidity sector. Formalization alone is not a scientific-novelty claim; external
novelty is unassessed under the user's Lean-only restriction. The general
mixed-sign summable-excess replacement is still open and has not been silently
replaced by the majorant claim. Its next obstruction is explicit: a nonpositive
signed kernel moment can coexist with positive and negative deviations.

No work was deferred for effort estimates. The hard remaining question is
whether mixed signs can satisfy the entire countable family with finite excess,
or whether another countable observable rules them out. The next cycle must
attack that exact gap, using the moment law and the earlier finite-deficit
counterfamily, before proposing another rigidity receiver.

## Verification log

- Final leaf check (`lake --old env lean -o ...`) exited 0 with no diagnostics;
  default heartbeat, no full/umbrella build.
- Umbrella import observed exactly once at line 6925.
- Index command exited 0; all six public declarations indexed.
- Scoped whitespace checks: no diagnostics.
- Authoritative formal lint exited 1 on six unrelated unreachable modules:
  `RHTower.StretchedBoseDefect`; `HTGeometry.ApertureConeCalculus`,
  `HTGeometry.ApertureConeWinding`, `HTGeometry.ApertureLogTranslation`,
  `HTGeometry.ApertureOpenHistoryIdeal`, `HTGeometry.BoundaryCoronaCStarAlgebra`.
  No lint error concerns this module.
- Separate public-signature/axiom audit exited 0. All six public declarations
  have exactly `[propext, Classical.choice, Quot.sound]`; no added axiom or
  unproved analytic premise. Every stated signature was inspected.
