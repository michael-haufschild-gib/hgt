# BAG: phase-preserving freezing and complete integer periods

2026-10-06,21az. Two actual producers now pass Lean. No assumed smoothness
or arbitrary-coefficient estimate replaces the original cubic amplitude.

For every actual prime pair p,r in (N,2N], N>1 and logN≥1, one constant C
independent of the pair gives

    ‖A(x)-A(r)e(2pi(p-r)(x-r)/r)‖ ≤ C |x-r|/(N²logN),

for every x in [N,2N]. Freezing retains the recentered phase exactly and
loses no gap factor. The original V/W values, reciprocal and logarithmic
density are retained at r. Factor the amplitude using its actual scaled
logarithmic profile; the corpus's uniform Lipschitz producer controls the
profile difference while the common phase has norm1.

For every real N and all natural M,p,r, Lean also proves the exact identity

    integral_[r-R,r+R] A(r)e(2pi(p-r)(x-r)/r) dx = 0,
    R = Mr/|p-r|.

This statement has no premises. When r=0 or p=r the interval collapses.
Otherwise translate by r and use signed real dilation. With
k=2pi(p-r)/r, the exponential integral is 2 sin(kR), and kR=±2piM.
Both gap signs and all interval endpoints are covered.

## Lean and validation

- `ChiCubicHyperbolicPrimeVariation.lean:632`:
  `exists_chiCubicHyperbolicPrimeAmplitude_freeze`.53 lines appended;
  existing module now684 lines. Foreground final leaf32589 exit0, empty:
  `/tmp/bag-hyperbolic-prime-freeze-02az.log`.
- `ChiCubicHyperbolicPrimePeriods.lean:27`:
  `chiCubicHyperbolicPrimeAmplitude_frozen_period`. New79-line leaf.
  Foreground final leaf54837 exit0, empty:
  `/tmp/bag-hyperbolic-prime-periods-02az.log`.

Both final commands use `lake --old env lean` with explicit oleans.
Freeze axiom/API89494 passed with only standard axioms; all period API
names were verified there. Final imported period/combined axiom90972 passed: both producers use only
propext, Classical.choice and Quot.sound. Its printed period statement has
no premises: `/tmp/bag-hyperbolic-prime-periods-axioms-21az.log`. New period
leaf wired once; existing variation import retained. Index34675 passed;
both new public rows checked. Final lint86341 exited1:367 large-file
warnings and22 unrelated unreachable modules, no finding for these BAG
leaves. Global lint is not clean. Log:
`/tmp/bag-hyperbolic-prime-periods-lint-21az.log`.
No heartbeat override, new axiom, admission, numerical experiment,
subagent, full/umbrella build, commit or push.

## Actual integral assembly still open

Inside a complete cell contained in [N,2N], freezing integrates to
O_M(1/(d²logN)), d=|p-r|. The ordering hole costs O(d/(NlogN)) per
active pair. A new simplification pays its ENTIRE sum with the already
proved actual averaged pair prefix: for L=floor(sqrt(2MN)),

    sum_{d≤L} d P_N(d) ≤ L sum_{d≤L} P_N(d) ≤ C N L²/log²N.

Both orientations therefore cost O_M(N/log³N), negligible at the cubic
scale. This removes the separate per-anchor prime-count obligation for
the hole. The exact support-difference integrals and gap reindexing still
need Lean proofs; no weighted-prefix wrapper counts as their completion.
Band-edge control, aggregate freezing, small-gap integral assembly and
the final epsilon limits also remain. No full cubic/tail or RH proof.
