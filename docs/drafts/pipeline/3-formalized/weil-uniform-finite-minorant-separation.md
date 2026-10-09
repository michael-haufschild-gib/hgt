# Uniform finite log-shift separation of arithmetic minorants

- **ID:** weil-uniform-finite-minorant-separation
- **Stage:** 3-formalized
- **Type:** QUANTITATIVE STRENGTHENING / uniform finite separating certificates
- **Source:** `formal/GaloisForLFunctions/RHTower/WeilFullConeMinorantRigidity.lean`,
  especially `weilLogShiftMinorants_subset_exact` and its kernel estimates.
- **Write scope:** that existing Lean module, this card, generated index and session memory.
  Preserve existing public statements; maintain one copy of the long arithmetic argument.
- **Source policy:** Lean corpus only. No external papers, web searches or numerical experiments.

## Exact theorem

Write `C = riemannAutocorr 0 > 0` and

`Q(lam,k,m) = Re(weilFullFunctional lam (EF.weilTest f f))`,
where `f = logShiftRiemannDifference (k : R) (log m)`.
This is notation for this card, not an existing Lean declaration.

For every `q : N` and `t : R`, put `n0 = q+2` and `delta = exp(t)`.
Lean proves that there exists `K : N` such that, for every integer `k >= K`,

```
{lam : N -> R |
   (forall n >= 2, lam(n) <= Lambda(n)) AND
   delta <= (Lambda(n0)-lam(n0))/sqrt(n0)}
  is a subset of
{lam : N -> R |
   exists m : N, 2 <= m AND m <= exp(2k) AND
     Q(lam,k,m) <= -(delta*C)/25}.
```

The cutoff depends only on the coordinate and prescribed deficit, never on lam.
Each window contains finitely many probes. The negative margin is uniform over
all admitted minorants and every sufficiently large integer window.
The parameters `q+2` and `exp(t)` encode an eligible coordinate and arbitrary
positive precision without a new unproved premise.

## Paper proof [CLOSED BY SOURCE AUDIT]

1. Obtain L1 such that, for L >= L1, the truncated autocorrelation at zero is at
   least `(24/25)C`, using `exists_truncatedRiemannAutocorr_zero_ge` at C/25.
2. Obtain L2 from `exists_exp_mul_nearRadicalEnergy_le` at `delta*C/100`.
   Both choices are independent of lam. Set
   `K = ceil_nat(max(max(L1,L2), log(n0)/2+1))`.
3. For k >= K and L = k, the source proof's support bounds place n0 in
   `[2, floor(exp(2L))]`. For any admitted lam, let
   `v(n) = (Lambda(n)-lam(n))/sqrt(n)` on n >= 2, zero otherwise.
   Pick a maximizer m in that finite interval. Then `v(m) >= v(n0) >= delta`.
4. The existing transform/zero-side estimate gives
   `|W(f,f)| <= delta*C/25`: the shift multiplier is bounded by `4 exp(2L)`
   and the L2 tail threshold contributes `delta*C/100`.
5. The current proof supplies an exact functional decomposition
   `Q(lam,k,m) = Re W(f,f) + sum F`, and bounds
   `sum F <= 4 A - 2 v(m) K_L(0)` and `A <= (23/50)v(m)C`.
   Hence `sum F <= -(2/25)v(m)C`.
6. Combine these estimates:
   `Q <= delta*C/25 - 2 v(m)C/25 <= -delta*C/25`.
   Positivity of any probe is unnecessary for this estimate.

The source's `hterm_re`, `hsum` and `hFs` establish the exact functional
decomposition: rewrite by `weilFullFunctional_eq_sub`, the von Mangoldt identity,
and `zeta_W_eq_weilFullFunctional`; commute real part with the summable series;
the coefficient series is the negative of `sum F`. Probe positivity is used only
to turn this identity into the old `hmain` inequality, so it can be removed.
The source's `hwin`, `hWnorm`, `hKL` and `hFG'` supply the bounds above. The two
truncation thresholds hold for every larger real L, so one rounded cutoff works
for every subsequent integer window. All source dependencies are proved Lean
results; no full Weil positivity or RH premise enters this argument.

## Corpus novelty audit

- Ran the documented lexical research command for `"minorant" "finite"`, with
  `--module RHTower --per-module 0 --no-refresh --json`. Its declaration hits
  include covariance minorants and the newly added log-shift predicate; the
  lexical response supplies no semantic-coverage certification.
- Exhaustive RHTower text search covered log-shift uses, finite/minorant pairs
  and uniform/deficit pairs. All occurrences of `logShiftRiemannDifference`
  remain in the source module.
- Inspected `WeilPaperCovarianceWindowDuality.lean` and
  `WeilPaperCovarianceDualAttainment.lean` at the affine-minorant definitions and
  finite dual-attainment theorem. They optimize covariance certificates for
  spectral completions; they do not give this uniform arithmetic separation.
- Inspected `WeilWorkDeficitRecovery.lean` and
  `WeilPaperDeficitInverseRecovery.lean` at their definitions and uniform-scale
  statements. They recover spectral zero deficits for a full-positive system,
  with a scale depending on that system. This candidate concerns arithmetic
  minorants and one cutoff uniform over the entire minorant class.
- The countable-rigidity proof itself contains the estimates needed for the
  candidate. The proposed advance is the uniform, finite, negative-margin
  conclusion and its explicit quantifier order. No external novelty claim.

## Consequences and limits

Passing all probes in a sufficiently large single window forces the prescribed
coordinate deficit below delta. Cofinal subsets of integer windows should also
suffice for exact coefficient rigidity. These are consequences to prove after
the separating theorem, not source assumptions.

No claim that Lambda passes the probes, no RH criterion, no full-cone positivity
inference, no quantitative formula for the cutoff. Global minorant bounds remain
in the stated class; replacing them by a finite coefficient block is a separate
possible strengthening, not part of this claim.

## Next steps

- [x] Lean-only corpus search and nearest-result comparison.
- [x] Derive the candidate margin and quantifier order on paper.
- [x] Audit the exact source decomposition and close the paper proof.
- [x] Refactor the arithmetic core once to prove uniform separation; leaf check passed.
- [x] Derive the existing countable-rigidity result without changing its statement; leaf check passed.
- [x] Direct leaf/caller checks, axiom audit, index, reachability, authoritative lint.

**[FORMALIZED]** Uniform separation, the derived countable-rigidity theorem,
both caller leaves and all eight axiom checks pass. The authoritative repository
lint gate reports eight unrelated umbrella-reachability errors, listed below.

## Implementation checkpoint

The source now contains `exists_uniform_logShift_minorant_separation`. Both
truncation thresholds and the cutoff are chosen before quantifying over windows
and minorants. The old positivity-dependent `hmain` is replaced by the exact
functional identity; the final comparison proves the negative margin directly.
The countable inclusion now applies the separator at the logarithm of its actual
positive coefficient deficit. The arithmetic comparison occurs once.
All four prior public theorem statements are byte-identical to the last verified
source, and all code from `weilLogShiftMinorantFiber_iff` onward is unchanged.
No heartbeat override was added. The final direct leaf audit passed with exit 0
and no diagnostics, emitting the updated leaf olean.
Owned scratch files use `/tmp/hgt-weil-finite*`.

The first direct leaf attempt reported coercion errors in the new coordinate
expressions and a hidden-target issue in `exact_mod_cast`. The natural sums are
now explicitly cast to reals, the deficit's conditional is rewritten before
unfolding its coordinate, and the cutoff comparison exposes both real casts.
The functional identity and negative-margin calculation produced no diagnostics
on that attempt. No heartbeat limit changed.
The next attempt reduced this to two tactic-shape issues: beta-reduce the deficit
function with `simpa only`, and remove a redundant step after `rw` closes the
coordinate-gap goal. Both were corrected before the next leaf audit.

## Final verification

- Sequential `lake --old env lean -o <leaf.olean> <leaf.lean>` checks passed with
  no diagnostics for `WeilFullConeMinorantRigidity`, `WeilFullConeRemovedPrimes`
  and `WeilConeOrderComparableRigidity`. No full or umbrella build was run.
- The final `/tmp` axiom audit passed for the new separation theorem, selected-test
  predicate, countable inclusion, coefficient-fiber classifier, old full-cone
  minorant theorem, unchanged RH criterion, and the two affected caller theorems.
  All eight dependency lists are exactly `[propext, Classical.choice, Quot.sound]`.
- `scripts/formal_tools.py index` passed. The new theorem and all five surrounding
  predicate/receiver declarations appear in the generated API index.
- The existing RHTower umbrella imports the modified module exactly once.
- Final source comparison confirms all four prior theorem statements are
  byte-identical to the previous verified source, all code from the coefficient
  classifier onward is unchanged, and the long arithmetic comparison occurs once.
- No new heartbeat override, axiom, proof-debt declaration, numerical experiment
  or external source. Scoped `git diff --check` passed.
- `scripts/formal_tools.py lint` exited 1 solely for these unrelated owned modules
  being unreachable from their theorem-area umbrellas:

```
RHTower.CCMFullGroundZeroSideEigen
RHTower.ChronologicalMobiusEscape
HTGeometry.ApertureConeCalculus
HTGeometry.ApertureConeWinding
HTGeometry.ApertureLogTranslation
HTGeometry.ApertureOpenHistoryIdeal
HTGeometry.BoundaryCoronaCStarAlgebra
HTGeometry.PaperFourierLLogL.Weak.Modular
```

Those modules were not edited for this task. The repository-wide lint gate is not
reported as passing. No commit or push was made.

All ten owned `/tmp/hgt-weil-finite*` scratch files were removed after all jobs
exited and the evidence above was recorded. Absence of matching files was verified.
