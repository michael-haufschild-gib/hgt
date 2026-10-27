# Arithmetic source-work increments pay for annular defects

Status: paper argument complete; individual Lean checks in progress.
Programme: ArithmeticIndexDescent.

## Statement

Let W(R) be the completed damped arithmetic source work, with analytic multiplicity
copies and every exterior interaction retained. For any finite packet P of right-hand
zero copies, 4 <= R <= S,

    sum_{p in P} [h_S(gamma_p)-h_R(gamma_p)] <= W(S)-W(R),
    h_R(t) = R^4/(R^2+t^2)^2.

Consequently, if R <= |gamma_p| <= 2R for every p in P,

    (21/100) card(P) <= W(2R)-W(R).

No RH, finite-energy assertion, source upper bound or negative-index budget is assumed.
The scale and packet restrictions specify the domain of the estimate. The constant
21/100 is sharp for the scalar damping increment on the annulus, not asserted optimal
for the complete arithmetic work.

Two further unconditional conclusions:

- The completed work W is monotone on [4,infinity).
- Either off-line support is finite, or arbitrarily large R have
  W(2R)-W(R) >= 21/100.

For every positive tolerance, the annular payment also holds eventually for the
difference of the two finite tapered Laurent-source works, up to that tolerance.

## Existing inputs and novelty

ArithmeticElectrostatics supplies the reflected energy/cross decomposition, its near-
and far-field estimates, absolute summability at finite damping scale, and the exact
identification with the completed arithmetic Laurent source. RHTower supplies the
unconditional height gap |Im rho|>=4 and finiteness of divisor support in height bands.
ArithmeticIndexDescent supplies the map selecting one multiplicity copy of each zero.

Earlier work detects fixed index witnesses after damping is removed and identifies
bounded total work with finite off-line support. The new estimate controls each scale
increment. Pairwise monotonicity is essential: positivity at two separate scales would
not justify dropping the remaining interactions from their difference. The resulting
local target is cancellation in W(2R)-W(R), rather than a global absolute source bound.

Corpus search found no earlier scale-monotonicity or annular-increment theorem. The
search indexed the new files while this proof was developed, so those self-hits were
excluded from the novelty comparison.

## Paper proof

1. Put v_R(t)=t^2/(R^2+t^2)^3. For a=|t|>=4 and b=|u|>=4, let
   T=a^2+b^2, P=a^2 b^2, Q=R^6-P(3R^2+T),
   S=a^2(R^2+b^2)^3+b^2(R^2+a^2)^3 and
   D=(R^2+a^2)^3(R^2+b^2)^3>0. The difference of the two velocities is
   (a-b)(a+b)Q/D and their sum is S/D. The inequalities
   T>=4(a+b) and a^4+b^4>=2(a+b)T make both S-2(a+b)Q and
   S+2(a+b)Q nonnegative by polynomial expansion. Thus

       2|v_R(t)-v_R(u)| <= |t-u|(v_R(t)+v_R(u)).

2. In the near field, multiply this inequality by the absolute reflected cross term
   and use |(t-u) cross|<=2E. In the far field use |cross|<=E and
   |v_R(t)-v_R(u)|<=v_R(t)+v_R(u). Both give nonnegative reflected work
   for the velocity weights. Since partial_R h_R(t)=4R^3 v_R(t), every actual
   reflected pair-work is monotone on [0,infinity). The actual height gap discharges
   the general kernel's height conditions; strip confinement discharges x^2+y^2<=1.

3. At scales at least four both pair kernels are absolutely summable. Their difference
   is summable and termwise nonnegative. For each right copy p, the four ordered pairs
   in {p,lineConj(p)}^2 have pair work exactly h_R(gamma_p). The quartet map is
   injective across different right copies, including different multiplicity indices
   at one support point. Its finite sum is bounded by the full increment tsum.
   The factor 1/4 in W then gives the weighted packet inequality.

4. The difference h_(2R)(t)-h_R(t)-21/100 has positive denominator
   100(4R^2+t^2)^2(R^2+t^2)^2 and numerator

       (4R^2-t^2)
         [21t^6+294R^2t^4+369R^4(t^2-R^2)+285R^6].

   This is nonnegative for R<=|t|<=2R. Equality holds at |t|=2R. Summing
   gives the annular quantum.

5. The existing compact-taper limit at each of the two scales gives convergence of
   their difference. Every strict lower payment therefore appears in the finite
   completed source differences. No exterior field is truncated.

6. If off-line support is infinite, local divisor finiteness supplies an off-line
   point above any prescribed height. Choose its right-hand critical-line reflection
   copy at the same height and apply the singleton annular theorem with R=|gamma|.
   This proves the arbitrarily-high quantum-increment alternative.

## Lean declarations

`DampingIncrementPositivity.lean`:

- `dampingVelocity_relative`
- `dampingVelocity_work_nonneg`
- `hasDerivAt_heightDamping`
- `reflectedWork_monotoneOn_scale`
- `heightDamping_doubling_gap`
- `heightDamping_doubling_gap_endpoint`

`SourceWorkIncrementsPayForNewZeros.lean`:

- `xiDampedPairWork_monotoneOn`
- `xiDampedSourceWork_monotoneOn`
- `sum_damping_increment_le_sourceWork_increment`
- `annular_zero_copies_paid_by_sourceWork_increment`
- `xiTaperedSourceWork_increment_tendsto`
- `eventually_annular_payment_in_finite_sourceWork`
- `finite_offLineSupport_or_arbitrarily_high_quantum_increments`

All names are in `GaloisForLFunctions.ArithmeticIndexDescent`.

## Exact remaining obstacle

No arithmetic upper bound on these scale differences is proved here. An eventual
uniform bound strictly below the quantum, or a proof that the differences tend to
zero, would exclude all sufficiently high off-line zeros and hence prove finite
exceptionality. The escape alternative identifies this target; it does not select
its finite-support branch. Elimination of a finite remainder is a separate question.
