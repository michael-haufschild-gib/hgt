# The asymptotic log-shift cone is a signed-potential cone

- **ID:** weil-logshift-asymptotic-potential-cone
- **Stage:** 3-formalized
- **Source policy:** Lean corpus only; no web, external papers, numerical
  experiments, heartbeat increases, full builds or umbrella builds.
- **Write scope:** new leaf, umbrella import, this card, generated index,
  owned scratch and cross-session memory.

## Objective and competing conjectures

Previous turn made verified progress: a moving probe reads the signed kernel
moment, and finite excess gives rigidity for majorants. The unrestricted
mixed-sign summable-excess replacement remains open. Competing possibilities:
all countable tests plus finite excess force equality, or a mixed-sign family
survives. Neither is assumed true here.

The exact obstacle is that a signed moment can be nonpositive without every
deviation vanishing. A finite-support counterfamily would require additional
kernel-shape inequalities not established by the current corpus search. No
claim of such a counterfamily or of kernel monotonicity is made.

## Selected exact conjecture

Let a(n)=WeilExcess.weilDeviation(lam,n) and assume sum |a(n)| is finite.
Let psi=WeilExcess.deviationPotential(lam). For every epsilon>0, eventually
uniformly over the ENTIRE finite panel in window k,

    |Re P_k(lam,m) - 2(psi(log m)-psi(0))| < epsilon.

Consequently the following are equivalent:

1. For every epsilon>0, all sufficiently late finite panels are bounded below
   by -epsilon.
2. psi(0)<=psi(log m) for every integer m>=2.

A strict uniform potential gap gives eventually strictly positive panels;
failure at one m gives a persistent negative witness in every large window.
This reframes the original obstruction as an explicit signed-potential cone;
it does not claim exact positivity in the finitely many initial windows or
settle the mixed-sign summable-excess question.

## Corpus attack

- The diagonal moment law sees only an escaping shift, not the entire panel.
- Existing kernel truncation has a uniform exponential defect bound, while
  the zero-side error tends to zero uniformly for shifts log m<=2k.
- Summable |a| permits an error bound uniform in every shift, including shifts
  that move with k. Pointwise convergence alone would not justify the claim.
- No external novelty claim: external sources are forbidden by the user.

## Paper proof [CLOSED]

1. Existing autocorrelation decay gives constants D,C>=0 with
   |K_k(y)-K(y)|<=D exp(-2(k-1)) exp(-2|y|), hence at most D exp(-2(k-1)).
2. The paired log-shift kernels differ by at most 8D exp(-2(k-1)) uniformly
   in the sample point and shift (coefficients 4,-2,-2).
3. Multiply by |a(n)| and sum. Both paired sums are summable, dominated by
   4K(0)|a(n)|. Their difference has absolute value at most
   8D exp(-2(k-1)) sum |a(n)|, tending to zero independently of the shift.
4. The exact arithmetic functional decomposition writes every panel value as
   its zero-side value minus the truncated paired sum. The full paired sum is
   2psi(0)-2psi(log m), by evenness of K and summable-sum algebra.
5. For log m<=2k, the zero-side norm is at most 4exp(2k) times near-radical
   energy. The existing uniform energy decay sends this to zero. Steps 3-5
   give uniform convergence of the entire expanding panel.
6. If all fixed potential gaps are nonnegative, uniform error<epsilon gives
   the -epsilon panel floor. Conversely, any negative gap at m persists once
   m enters every later panel; choose an error and floor tolerance smaller
   than the gap to contradict asymptotic nonnegativity.
7. A strict uniform gap absorbs the uniform error. A single negative gap
   likewise absorbs it and gives eventual negative values of that fixed probe.

## Work log

- [x] Read objective and classify previous turn as verified progress.
- [x] Inspect mixed-sign obstruction; select exact falsifiable reframe.
- [x] Close dependency-closed paper proof.
- [x] Exact `logShift potential` lexical query returned zero declarations;
  exhaustive targeted source search found no existing panel/potential law.
  Broad kernel search gave no monotonicity theorem supporting the speculative
  counterfamily. Required summability, truncation and filter APIs checked in
  a scratch Lean import (exit 0).
- [x] Formalize and audit exact uniform law and cone equivalence.
- [x] Wire, index, lint and promote card.
- [x] All owned jobs terminal; removed all 10 inventoried scratch files and
  verified absence. Recorded `research/weil-logshift-potential-cone-2026-10-09`.

**[PAPER PROVED; LEAN VERIFIED]**

## Exact implemented API

Source: `formal/GaloisForLFunctions/RHTower/WeilLogShiftPotentialCone.lean`.

- `exists_uniform_truncatedDeviationPotential_error`: exponential potential
  truncation bound uniform over ALL real shifts, without positivity.
- `exists_uniform_logShift_potential_error`: one cutoff bounds the error of
  EVERY probe in EVERY later finite panel by the requested tolerance.
- `WeilLogShiftAsymptoticPositive`: the explicit uniform negative-tolerance
  predicate, with tolerance chosen before the cutoff.
- `weilLogShiftAsymptoticPositive_iff`: exact equivalence with
  psi(0)<=psi(log m) for every integer m>=2.
- `exists_uniform_logShift_positive_of_potential_gap`: a uniform gap delta>0
  yields panel entries strictly greater than delta in every later window.
- `exists_persistent_logShift_negative_of_potential_gap`: one negative gap
  yields the same valid probe, below that negative gap, in every later window.

## Significance and next attack

This is a corpus reframe supported by existing kernel decay, not a claim of
external scientific novelty. It strengthens the diagonal moment result to
uniform control of the expanding panel; pointwise convergence would not suffice.
The exact criterion separates a fixed signed-potential constraint from finite
initial-window errors and from the summability needed for uniform control.

The domain is ABSOLUTE summability of normalized deviation. Summable excess
alone does not supply that domain when deficits are infinite. The general
mixed-sign summable-excess rigidity question remains open, as does construction
of a finite-deviation counterfamily satisfying the original exact predicate.
Neither question has been replaced by the proved asymptotic equivalence.

One next attack is a two-atom signed potential: a deficit at 2 and excess at a
larger integer. To produce a strict potential gap, one would need verified
separation between K(log N) and the finite collection K(log(N/m)). The corpus
search has not supplied the required ratio or shape theorem. Positive K and
coarse exponential decay alone do not prove it. Even a successful strict
potential construction gives only eventual panel positivity; exact initial
windows would still require a separate compatible construction.

No proof work was deferred on effort grounds. The remaining mixed-sign problem
is now specified more sharply; next cycle must attack its ratio/construction
obstruction or find a stronger rigidity mechanism, without assuming either.

## Verification log

- Final leaf check exited 0 without diagnostics, emitted its olean, used
  `lake --old env lean` and default heartbeat. No full or umbrella build.
- Umbrella import observed exactly once at line 6928.
- Index command exited 0 and all six public declarations are indexed.
- Scoped whitespace checks produced no diagnostics.
- Authoritative lint exited 1 on nine unrelated unreachable modules:
  `RHTower.PaperCirclePhaseCancellation`, `RHTower.SincSeparatorMellin`,
  `RHTower.StretchedBoseDefect`; `HTGeometry.ApertureConeCalculus`,
  `HTGeometry.ApertureConeWinding`, `HTGeometry.ApertureLogTranslation`,
  `HTGeometry.ApertureOpenHistoryIdeal`, `HTGeometry.BoundaryCoronaCStarAlgebra`,
  `HTGeometry.ComplexRateGammaIntegral`. No lint error concerns this module.
- Separate import/signature/axiom audit exited 0. Every public signature was
  inspected; all six declarations depend exactly on
  `[propext, Classical.choice, Quot.sound]`.
