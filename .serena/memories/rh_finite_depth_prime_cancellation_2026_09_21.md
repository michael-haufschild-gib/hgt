# Finite-depth actual-prime cancellation

RH, exhaustive payment, and bounded critical action remain open. This continues `mem:rh_current_clock_payment_2026_09_21`.

New 532-line module: `formal/GaloisForLFunctions/RHTower/MobiusDivisorFiniteDepthPrimeCancellation.lean`, wired into `RHTower.lean`.

## Checked producer

Line 472, `eventually_exists_mobiusDivisorFiniteDepth_uniform_prime_collar`: for ANY finite prime core P with card > 1 and ANY finite positive integer child field I, there exist c, eta > 0 such that, for every bound B, eventually at EVERY integer M, EVERY nonzero current vector a : I -> Real has a fresh actual prime p > B outside P. For all integers M <= L <= (1+eta)M, sum_r a(r) * mobiusDivisorInterpolatedFibre L (p*r) P empty <= -c * norm(a).

Constants and threshold precede the coefficients. Constants depend on P,I; threshold also depends on B. Coefficients stay fixed on the collar. Fixed source product and logarithmic weights may be absorbed in a. No special preparatory core is required.

Line 262, `mobiusDivisorDelayedProfile_both_signs`: every nonzero finite real combination of H_P(x/r), with positive integer delays r, takes both signs above one. No depth bound is imposed.

## Source proof

Two Euler prime zeros leave a zero at one half after filling the unit pole. The physical Mellin transform of the delayed combination therefore tends to zero from the right. A nonnegative profile would have a strictly positive exponent-one moment, and all moments for exponents in (1/2,1) would be at least as large. The least nonzero delay activates on (r,r+1), establishing strict positivity of that moment. NO absolute convergence at the half boundary is assumed. Continuity follows from the literal integral primitive. A finite cover of the coefficient unit sphere supplies uniform negative source rectangles. PNT windows and narrowed child intervals produce fresh primes and a uniform cutoff collar.

## Whole-route gap

This is a source-direction producer, not complete energy payment. Still missing: quantitative dependence on growing depth/core; actual coefficient evolution; positive quadratic self-cost; newly active coordinates outside the finite projection; omitted-prime debt; intervening original cutoffs and completion. Applying the theorem to P plus an omitted prime does NOT pay that prime's accumulated debt.

Next hard target: a growing-depth batch with a PAID remainder for new coordinates and self-cost, and quantitative source-window supply at the SAME current clock. Prior bounded-depth producer pays delta*M^2; existing depth obstruction leaves old debts of order M^2*log M and forces helper depth at least eta*log M even with forward waiting.

## Audits

Scratch and named leaf build passed without new-module warnings. Four public theorems' compiled axiom audits contain exactly propext, Classical.choice, Quot.sound. Index and whitespace checks passed. Global lint retains four unrelated unreachable-module errors: the LowerWeylRadialDetector, SelfInverseSquarePhysical, SelfMixedCuspFlux leaves of ThetaCuspHawkingBMLiteralCyclicPeierls, and XiHeatCassiniWoldJointDepthMöbiusSourceTransport. All owned processes exited; scratch Lean files removed. Logs: /tmp/hgt-growing-depth-{build,axioms,index,lint}.log.

Own fact log: `docs/drafts/pipeline/1-in-progress/rh-growing-depth-source-facts.md`, with full paper proof and explicit quantifier gaps. Keep one foreground Lean process, use scratch then named leaf build, never full builds or numerical experiments. Do not modify other agents' logs.