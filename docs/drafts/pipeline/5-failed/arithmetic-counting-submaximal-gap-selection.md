# Even the maximal prime gap does not select complete Weil positivity

- **ID:** ACP-SUBMAXIMAL-SELECTION
- **Stage:** 5-failed
- **Type:** FALSE IMPLICATION; positive survivor formalized
- **Rejected route:** A fixed positive prime-hyperplane gap, multiplicativity,
  the von Mangoldt absolute majorant and untwisted polar matching suffice for
  complete Weil positivity.
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md

## Exact obstruction

For every `a<2log 2`, a prime `p` gives the completely multiplicative sign
`omega_p(n)=(-1)^v_p(n)` with hyperplane gap at least `a` and

`|sum_{n<=y}omega_p(n)Lambda(n)/n-log y|
 <=log 4+4+2log p/(p-1)`.

Its actual source `lambda_p(n)=omega_p(n)Lambda(n)` satisfies
`|lambda_p(n)|=Lambda(n)` but fails complete Weil positivity. Indeed full-cone
uniqueness would force `lambda_p(p)=Lambda(p)`, whereas these values are
`-log p` and `log p`. The failure has an actual compactly supported `C^2`
test witness in the literal functional, retaining Gamma, both poles and every
prime-power term.

Lean: `near_maximal_gaps_do_not_force_weil_positivity` and
`primeFlip_exists_negative_complete_test` in
`ArithmeticCountingPositivity/NearMaximalGapsDoNotForceWeilPositivity.lean`.

The endpoint is now also ruled out: every prime `p>=11` gives a nontrivial
flip with greatest gap exactly `2log 2`, the same polar matching and an
actual negative complete-Weil test. This is
`maximal_gap_does_not_select_the_source` in
`LargePrimeFlipsAttainTheMaximalGap.lean`, with paper
`../3-formalized/arithmetic-counting-maximal-gap-rigidity.md`.

## Strongest positive survivor

The count retains useful energy rather than merely detecting a failure:

1. Uniformly over all sign gauges and all horizons beyond an
   epsilon-dependent threshold, the retained gap is at least
   `(2log 2)(S_N/H_N)^2`. The geometric projection bound underlying this
   inequality is attained by the projected gauged pole.
2. Negative prime-parity fibres are exactly `p` times positive fibres.
   Their weighted count gives `p(H_N-S_N)=H_floor(N/p)+S_floor(N/p)`.
3. The exact excess over `S_N/H_N=(p-1)/(p+1)` is a positive boundary count
   bounded by `2(1+log p)`. Thus this harmonic ratio has the stated exact
   limit, and the paid gap is `(2log 2)((p-1)/(p+1))^2`.
4. The prime-two flip retains gap `2log 2/9`, although Liouville has no
   positive hyperplane gap. Selectivity against Liouville is therefore
   strictly weaker than selection among multiplicative sources.
5. The exact cutoff is eleven. Every prime-flip gap is at most
   `p log p/(p+3)`, strictly below the maximum for p<11; combined with
   the large-prime theorem, maximal-gap attainment holds iff p>=11.
6. The parity constraint has a complete arithmetic spectral measure:
   squared mass `c_p^2` at the ground and `4c_p^2/phi(p^k)` on each
   positive p-power. Its finite tower approximations have the sharp error
   `4p/((p+1)^2 p^K)` uniformly over every positive integer horizon.
7. The exact greatest single-prime gap is `min(2 log 2,alpha_p)`, with
   `alpha_p` the unique root of its explicit arithmetic secular series.
   For p=2,3,5,7 it is exactly `alpha_p`; every real gap is classified
   by lying below this attained value. Every gap is strictly below
   `p log p/(p+3)`, improving the two-mode upper bound.
8. Every finite prime set has an attained positive greatest gap determined
   exactly by its counted arithmetic secular series. Every submaximal gap
   is its unique interior root. Under proper inclusion of flipped-prime
   sets, equality of gaps can occur only at the maximal value; otherwise
   the larger-set gap is strictly smaller.
9. Above every fixed prime cutoff, the greatest joint gaps tend to zero.
   The proof counts rough conductors in a factorial-step progression and
   retains their divergent reciprocal-logarithmic mass in the exact secular
   criterion. Arbitrarily large primes can therefore each be maximal while
   their joint greatest gap is arbitrarily small and positive.
10. A fixed dyadic probe repairs selection within the finite-prime family:
    the original maximal gap and the untwisted dyadic-response gap jointly
    hold exactly for the empty flip set. Proper inclusion below the ceiling
    makes the second reading strictly decrease for every remaining twin.
11. Added conductor mass Delta bounds the full secular increment and obeys
    `(delta_F-delta_G)(g0-delta_G)<=delta_G delta_F Delta`. This gives a
    uniform squared-loss bound, and an explicit order-1/p loss for the fixed
    dyadic calibration. Every fixed positive tolerance therefore admits
    arbitrarily remote individually maximal prime flips.

12. The exact conductor moment is `sum_(p in F)4p log p/(p^2-1)` and bounds
    the greatest gap by `c_F^2 M_F/(1-c_F^2)` for nonempty F. Elementary
    Mertens bounds consequently give an explicit O_B((log Q)^(-3)) upper
    bound for joint prime-tail gaps, while each finite-stage gap is positive.

13. Reciprocal divisibility mass bounds harmonic correlation and finite-cutoff
    squared error uniformly in the integer horizon, for every prime pattern.
    A geometrically sparse infinite prime set has arbitrarily small mass,
    yielding actual infinite-support signs with every prescribed submaximal
    positive gap. The uniform count supplies the transfer missing from mere
    pointwise cutoff convergence.

14. Stripping any finite prime set has an explicit additive harmonic error
    uniform in the residual infinite sign pattern and integer horizon. The
    cost is at most O(log Q) for primes up to Q. This supplies quantitative
    arithmetic control for simultaneous prime and horizon exhaustion.

15. Every arbitrary prime pattern has its exact Euler-product harmonic
    mean, without any mean-value or summability assumption. Positive
    limiting products pay their squared-density gaps. Vanishing products
    are included by the uniform stripping squeeze; no zero-gap converse
    is inferred.

16. Positive Euler density is exactly the condition for harmonic mean-square
    approximation by finite prime cutoffs. The exact squared distance
    tends to 2(1-c/c_Q); at zero density every fixed cutoff has limit two,
    while cutoffs beyond any fixed integer horizon are exactly equal.

17. Arbitrary prime patterns have exact harmonic Ramanujan coefficients
    with a sharp mass boundary. Their unnormalized conductor weights are
    summable exactly at positive Euler density; the normalized total is
    one there and zero at zero density. Finite divisibility counts identify
    the coefficients as actual mixed harmonic means.

Paper proof: `../3-formalized/arithmetic-counting-pole-angle.md`. Lean survivors:
`eventually_prime_gap_ge_squared_correlation`,
`gaugeWitness_attains_variance_bound`, `prime_parity_pairing`,
`prime_parity_boundary_identity`, `prime_parity_boundary_bounds`,
`primeFlip_harmonicCorrelation_tendsto`, `primeFlip_hasHyperplaneGap`, and
`two_adic_parity_has_gap_but_liouville_does_not`.

All 28 theorems in the four-module contribution have transitive axiom audits
containing only `propext`, `Classical.choice`, and `Quot.sound`. Canonical
source checks and the durable audit report accompany the formalized paper
card. No unproved analytic estimate is stored in the survivor's hypotheses.

Survivors 5 and 6 have dependency-closed proofs and Lean formalizations in
`../3-formalized/arithmetic-counting-small-prime-gap-boundary.md` and
`../3-formalized/arithmetic-counting-parity-spectral-mass.md`. Their three
and eight public endpoints respectively passed canonical source checks
and transitive axiom audits. The combined cutoff equivalence also audits
the imported large-prime endpoint transitively with only standard axioms.

Survivor 7 is proved in
`../3-formalized/arithmetic-counting-small-prime-secular-gap.md` and
`TheParitySecularRootDeterminesTheGap.lean`. Its eight endpoints passed
transitive axiom audits using only standard axioms and a canonical source
check without diagnostics. The adjacent audit preserves the exact evidence.

Survivor 8 is formalized in
`../3-formalized/arithmetic-counting-finite-prime-secular-gap.md`, with
`TheFinitePrimeSecularSignsDetermineTheGap.lean` and
`InteriorSecularRootsForceStrictPrimeGapDecrease.lean`. Their thirteen
endpoints passed standard-axiom and canonical source audits. Earlier
finite-set mass, coordinate and full-resolvent leaves close every input.

Survivor 9 is formalized in
`../3-formalized/arithmetic-counting-prime-tail-gap-collapse.md` and
`PrimeTailExhaustionHasVanishingGreatestGaps.lean`. All five endpoints have
standard transitive axiom audits and a successful canonical source check.

Survivor 10 is formalized in
`../3-formalized/arithmetic-counting-dyadic-gap-selection.md` and
`OneDyadicProbeSelectsTheFinitePrimeSource.lean`. All three endpoints passed
standard transitive axiom audits and a canonical installed-source check.

Survivor 11 is formalized in
`../3-formalized/arithmetic-counting-gap-stability-and-probe-precision.md` and
`ConductorMassBoundsGapLossAndProbePrecision.lean`. Its strongest positive
statement is the mass-based product bound on gap loss, not merely the
negative tolerance conclusion. All seven endpoints passed standard-axiom
and canonical installed-source audits.

Survivor 12 is formalized in
`../3-formalized/arithmetic-counting-finite-prime-energy-moment.md` and
`../3-formalized/arithmetic-counting-prime-tail-gap-rate.md`. Their six
endpoints passed standard-axiom and canonical installed-source audits.
The survivor includes an exact arithmetic moment and quantitative positive
finite-stage bounds, not merely the vanishing conclusion.

Survivor 13 is formalized in
`../3-formalized/arithmetic-counting-summable-prime-exhaustion.md` and
`DivisibilityCountsControlInfinitePrimeFlips.lean`. Its five endpoints passed
standard-axiom and canonical installed-source audits. This proves a uniform
positive counting estimate and infinite-support positive gaps; it does not
assert infinite-gauge optimal-gap continuity or complete Weil positivity.

Survivor 14 is formalized in
`../3-formalized/arithmetic-counting-uniform-prime-stripping.md` and
`PrimeStrippingHasAnAdditiveHarmonicError.lean`. Both endpoints passed
standard-axiom and canonical source audits.

Survivor 15 is formalized in
`../3-formalized/arithmetic-counting-all-prime-pattern-harmonic-density.md`
and `EveryPrimePatternHasItsEulerProductHarmonicMean.lean`. All four
endpoints passed standard-axiom and canonical source audits.

Survivor 16 is formalized in
`../3-formalized/arithmetic-counting-prime-pattern-cutoff-boundary.md`
and `PositiveEulerDensityIsExactlyHarmonicCutoffCompleteness.lean`. All
five endpoints passed standard-axiom and canonical source audits.

Survivor 17 is formalized in
`../3-formalized/arithmetic-counting-infinite-conductor-mass-boundary.md`
and `InfinitePrimeCountsHaveAZeroOrUnitConductorMass.lean`. All six
endpoints passed standard-axiom and canonical source audits.

## New insight and remaining boundary

Counting can pay a selective gap without recovering the source information
needed by the complete form. A transfer using only the prime-hyperplane gap,
even its exact maximum, and leading polar matching cannot be valid for the
whole multiplicative class. The sharp cutoff, complete parity spectral
measure, complete finite-prime classification and strict inclusion law
survive this obstruction, together with qualitative collapse for every
cofinite prime exhaustion. A second, fixed dyadic reading selects the finite
family exactly; its lack of fixed tolerance is now quantified by the
positive mass-based gap-loss bound. Prime-tail collapse now has an explicit inverse-log-cube upper bound.
Every infinite prime pattern now has its exact harmonic mean and paid
squared-density lower bound. Sharp decay, infinite-pattern optimal gaps
and the full producer mechanisms remain open.
