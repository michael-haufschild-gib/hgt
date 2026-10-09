# Three-index cancellation and quartic Gram cost

Status: FORMALIZED. Dependency-closed paper proof and exact Lean receivers verified.
Evidence restricted to local Lean corpus and installed Lean/mathlib. No web,
external papers, or numerical experiments.

## Target

Every normalized Gram certificate whose support contains three consecutive
arithmetic indices has cost at least a universal positive constant times n⁴.
Full arithmetic cutoffs inherit this quartic obstruction. Matching upper rates
remain outside this claim.

## Corpus evidence

RiemannAutocorrWeightedTranslation proves exponential envelopes for EVERY fixed
actual riemannKernelDeriv order, and hasDerivAt_riemannKernelDeriv supplies the
actual derivative chain. Existing native autocorrelation integrals are absolutely
convergent. The finite Gram cost/certificate framework and signed-witness method
are verified in WeilLogShiftFiniteClusterCost. No second-difference receiver was
found by the initial local research query or direct autocorrelation source search.

## Paper proof

1. Apply the mean value inequality to every kernel derivative order k, using the
   existing order k+1 exponential bound. This gives
   |Phi^(k)(x+h)-Phi^(k)(x)| ≤ D_k exp(-3|x|)|h| for |h|≤1.
2. Apply the same inequality to Phi(x+h)-Phi(x)-h Phi'(x), bounding its derivative
   by the preceding order-one translation estimate. Obtain a quadratic remainder
   bound D exp(-3|x|)h². Take the real part to obtain the actual real-kernel bound.
3. For a,b≥0 and |u|,|v|≤1 with au+bv=0, the linear terms cancel in
   a(Phi(x+u)-Phi(x))+b(Phi(x+v)-Phi(x)). The remainder is bounded by
   D exp(-3|x|)(au²+bv²).
4. Multiply by Phi(t), integrate at x=t-y with shifts -u,-v, and use the same
   exponential convolution estimate as the first-order translation proof.
   No derivative integral is needed: cancellation happens before integration.
   This gives E exp(-2|y|)(au²+bv²) for the balanced autocorrelation combination.
5. Let d1=log(n+1)-log n and d2=log(n+2)-log(n+1). They are positive and at most
   1/n. Choose a=d2/(d1+d2), b=d1/(d1+d2). Then a+b=1,
   a(-d1)+b d2=0, and a d1²+b d2²=d1 d2≤1/n².
   Apply the balanced bound to both halves of P at center log(n+1), with opposite
   signed offsets. The exponential center factor contributes another 1/n².
   Thus a P_n+(1-a)P_(n+2)-P_(n+1) has a uniform inverse-quartic envelope.
6. On any finite support containing k,k+1,k+2, n=k+2, extend the coefficients
   (a,-1,1-a) by zero. Their sup norm is exactly one. The normalized certificate
   supplies distinct witnesses for this vector and its negative. Each costs more
   than n⁴ after one universal normalization, hence total cost >2n⁴. The cutoff
   range(N+3) contains the last triple N,N+1,N+2.

All differentiability and decay used here come from actual corpus theorems;
no analytic premise is introduced. Barycentric weights handle the unequal
logarithmic spacing exactly; no estimate of its second arithmetic difference
is assumed.

## Work plan

1. Formalize weighted kernel quadratic remainders and balanced autocorrelation.
2. Derive the actual three-index inverse-quartic envelope with one weight per n.
3. Prove arbitrary-support and full-cutoff quartic Gram cost lower bounds.
4. Native leaf builds, all public axiom audits, umbrella wiring, index, lint.

Full research goal remains active.


## Implementation checkpoint

All three planned Lean leaves are authored and wired into the umbrella:
- RiemannAutocorrBalancedQuadratic.lean: four public declarations; native build
  passed without diagnostics. This includes all-order derivative translation and
  quadratic remainder bounds plus real-kernel and autocorrelation balanced bounds.
- WeilLogShiftTripleCancellation.lean: native inverse-fourth envelope, build in
  progress after addressing elaboration errors; no final claim yet.
- WeilLogShiftQuarticClusterCost.lean: arbitrary-support and cutoff receivers
  authored; compile after the native envelope succeeds.

Additional local ingredient discovered: RHTower.log_step_bounds in
LegStripThreshold.lean:755 already bounds log((x+1)/x) between 1/(x+1) and 1/x.
The private native helper now reuses that theorem instead of duplicating it.

Lean elaboration lesson: pointwise function subtraction inside HasDerivAt can
retain mismatched additive-instance expressions. Prove the function equality by
funext/rfl, then use erw to transport the derivative proof. Explicitly setting a
local AddCommGroup instance did not solve it and was removed. Integral linearity
required the same erw transparency adjustment. No assumptions were added.

Final audit prepared at /tmp/hgt-weil-quartic-audit.lean for all seven public
statements and the used local APIs; run only after all native leaves compile.


## Verified completion — 2026-10-09

All four work-plan steps completed. This supersedes the pending statuses in the
implementation checkpoint. Seven public declarations across the three leaves:
1. exists_riemannKernelDeriv_translation_envelope
2. exists_riemannKernelDeriv_quadratic_remainder_envelope
3. exists_riemannKernelReal_balanced_quadratic_envelope
4. exists_riemannAutocorr_balanced_quadratic_envelope
5. exists_pairedLogKernel_triple_inverseFourth_envelope
6. exists_finiteWeilGram_triple_quartic_cost_bound
7. exists_finiteWeilGram_cutoff_quartic_cost_bound

The native envelope chooses one endpoint weight a∈[0,1] per arithmetic index n,
BEFORE the universal sampling variable y. Its coefficients (a,-1,1-a) cancel the
linear logarithmic moment exactly and have sup norm one. The resulting actual
potential is bounded by B exp(2|y|)/n⁴. No sampled-only approximation is used.

One universal B>0 therefore gives totalCost_B >2(k+2)⁴ for every normalized Gram
certificate on every finite support containing k,k+1,k+2. In particular every
certificate on range(N+3) costs more than 2(N+2)⁴. These are lower bounds;
matching upper bounds and optimal constants are not claimed.

Verification:
- All three final native leaf builds exit 0 with no diagnostics.
- All seven public declarations depend exactly on propext, Classical.choice,
  Quot.sound. No new analytic premise, axiom, or admission is used.
- Explicit local mathlib API term checks pass in the same final scratch audit.
- All owned leaves, direct dependencies, and reused LegStripThreshold artifact
  are current. All three leaves wired into RHTower umbrella.
- Index refresh exits 0.
- Authoritative formal lint exits 1 for eight unrelated unreachable modules:
  RHTower.SelbergTransformRealMonotone;
  RHTower.Sieve.UnitBlockFrequencyBounds;
  RHTower.Sieve.UnitBlockFrequencyComparison;
  RHTower.Sieve.UnitBlockFrequencyDecay;
  RHTower.Sieve.UnitBlockPoissonKernel;
  HTGeometry.MonotonePhaseFirstDerivativeTest;
  HTGeometry.QKrawtchoukCompanionTriangular;
  HTGeometry.SmoothPlateau.
  It also reports unrelated proof debt at
  formal/GaloisForLFunctions/RHTower/Sieve/UnitBlockFrequencyDecay.lean:246,
  theorem exists_norm_ubKernelD2_le (sorry). These concurrent files were not edited.
- No owned jobs remain running. No full builds, web, papers, numerics, commits,
  heartbeat increases, or disabled linters.

Logs: /tmp/hgt-weil-balanced-quadratic-build.log,
/tmp/hgt-weil-triple-cancellation-build.log,
/tmp/hgt-weil-quartic-cost-build.log, /tmp/hgt-weil-quartic-audit.log,
/tmp/hgt-weil-quartic-index.log, /tmp/hgt-weil-quartic-lint.log.

## Next conjecture

Do fixed clusters of r+1 nearby arithmetic indices force cost ≥c_r n^(r+2)
for every r, and hence force full-cutoff certificate costs beyond every fixed
polynomial rate? A candidate construction chooses a nonzero coefficient vector
in the kernel of the first r logarithmic-moment rows, then normalizes its sup
norm. With r+1 columns, finite-dimensional linear algebra supplies such a vector;
its l1 norm is bounded by r+1. An ACTUAL order-r kernel Taylor remainder must then
be derived from the corpus derivative chain and used before integration.
No higher-order envelope is assumed or claimed proved here.

Local Mathlib/Analysis/Calculus/Taylor.lean:390-423 was inspected: the theorem
`taylor_mean_remainder_bound` requires ContDiffOn on an interval and a bound on
the (n+1)-st iterated derivative within that interval. These must be discharged
from actual riemannKernelDeriv identities, not added as receiver premises.
Search local corpus before starting this next conjecture. The matching cubic
upper bound for adjacent pairs also remains unresolved in this workstream.

Full research goal remains active; this completes one increment.
