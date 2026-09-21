# Growing-depth source cancellation

Owner: critical-clock product task. Exhaustive payment and RH remain open.

## Frozen producer target [BRIDGE]

Produce both signs, and then fresh actual prime directions, for every
nonzero finite linear combination of delayed components of one actual
processed divisor head. The number and sizes of the delays are unrestricted.
This attacks the finite-dimensional restriction of the existing two-coordinate
clock payment. It does not assume a correlation sign or a paying schedule.

## Source facts proved in Lean

Module: `MobiusDivisorFiniteDepthPrimeCancellation`.

- `divisorCoreMellin_half_eq_zero`: at least two processed prime factors
  leave a zero at one half after filling the unit source's simple pole.
- `mobiusDivisorDelayedProfile_both_signs`: for any finite positive integer
  delay set `I` and nonzero coefficients on `I`, the literal profile
  `sum(a(r) H_P(x/r), r in I)` takes both signs. No upper bound on the
  number or size of delays is imposed. The core can be any finite prime
  set with at least two members; no special preparatory core is required.
- `eventually_exists_mobiusDivisorFiniteDepth_uniform_prime_collar`:
  for every such core and field, there are `c,eta > 0` such that, for every
  prime-exclusion bound `B`, eventually at every original integer cutoff
  `M`, **every nonzero current coefficient vector** `a : I -> Real` has a
  fresh actual prime `p > B`, `p notin P`, satisfying

  `sum(a(r) InterpolatedFibre(L,p*r,P,empty), r in I) <= -c norm(a)`

  simultaneously for every integer `M <= L <= (1+eta) M`.
  The constants and threshold precede the coefficients. Fixed source
  product and logarithmic weights can be included in those coefficients.

## Dependency-closed paper proof

1. Factor the finite Euler multiplier at one processed prime. A second
   prime makes both factors vanish at one half, hence the derivative
   vanishes there. The filled Mellin numerator consequently vanishes.
2. Finite dilation factors the physical Mellin transform into this core
   transform times a finite exponential polynomial. Its right boundary
   limit is zero, using the already proved physical identity for real
   exponents strictly greater than one half.
3. The least delay with nonzero coefficient supplies a whole nonzero
   interval `(r,r+1)`. On that interval its head is the positive unit head;
   larger delays have not activated, and smaller coefficients vanish.
4. If the complete profile were nonnegative, its exponent-one Mellin
   integral would be strictly positive. For exponents between one half
   and one, the integrals are at least as large since the profile vanishes
   below one. The zero boundary limit contradicts this lower bound.
   Negating the coefficients supplies the other sign. No absolute
   convergence at one half is assumed or needed.
5. The source is continuous through all integer activation thresholds,
   by its exact integral primitive. Joint continuity in coefficients and
   child depth gives negative rectangles. A finite cover of the coefficient
   unit sphere gives one positive margin before coefficients are chosen.
6. PNT windows supply actual primes at every sufficiently large integer
   cutoff. Shrinking the child interval leaves a common multiplicative
   cutoff collar. Homogeneity restores arbitrary coefficient magnitudes.

## Whole-route consequence and open quantifiers

Finite-field signed source separation is no longer an obstruction, even
for an arbitrary processed prime core. Prime supply can be chosen uniformly
before the current finite coefficient vector. A prime selected at the
current cutoff retains its signed margin under a genuine cutoff change.

This is a source-direction producer, **not a complete energy payment**.
The coefficients remain fixed on the collar; their actual evolution under
successive insertions and cutoff changes is not yet controlled. Positive
self-energy and source coordinates born beyond the finite field remain
in the full action and have not been discarded.

## Quantifiers that must remain explicit

The constants `c,eta` and prime threshold depend on `P,I`. There is no proved
rate as child depth grows. The theorem cannot be applied at a current clock
whose full active field has outgrown its prime-supply threshold. Applying it
after inserting an omitted prime does not pay that insertion's accumulated
debt. The missing producer must retain new-coordinate and quadratic costs
while accumulating enough signed payment for all intervening cutoffs.

Next hard target: a growing-depth batch identity with a paid remainder for
newly active coordinates, and quantitative source-window supply compatible
with that same current clock. Cumulative payment control, bounded critical
action, and RH are still open.

## Search discrimination

Deep physical-Mellin and cone searches were partially covered; the later
finite-cover method search completed. Retrieved physical transform,
first-activation and compactness lemmas did not supply this producer.
The broad 2026 arXiv search on “controllability” led to
[Li et al.](https://arxiv.org/abs/2605.27117), an AI controllability position
paper. It supplied no mathematical input for arithmetic-source cancellation.

## Audit facts

- Scratch `lake env lean /tmp/hgt-growing-depth.lean`: passed without warnings.
- Named build `lake build GaloisForLFunctions.RHTower.MobiusDivisorFiniteDepthPrimeCancellation`:
  passed; no new-module warnings. Existing dependency diagnostics were replayed.
- All four public theorems' compiled axiom audits contain exactly
  `propext`, `Classical.choice`, `Quot.sound`.
- Module is imported by `RHTower.lean`; source indexes regenerated.
- Whitespace checks passed. Global lint still reports four pre-existing,
  unrelated unreachable modules: `ThetaCuspHawkingBMLiteralCyclicPeierlsLowerWeylRadialDetector`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux`, and
  `XiHeatCassiniWoldJointDepthMöbiusSourceTransport`.
- All owned Lean and search processes exited. Scratch proof files removed;
  audit logs remain under `/tmp/hgt-growing-depth-*.log`.
