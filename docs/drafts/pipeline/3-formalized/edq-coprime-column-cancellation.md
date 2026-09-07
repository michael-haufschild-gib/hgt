# EDQ complete coprime columns and the exact quadratic tail

Stage: 3-formalized. Unconditional arithmetic estimate; RH remains open.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.

## Arithmetic result

For positive n, complete coprime Möbius inversion gives

`sum_(e|n, gcd(d,e)=1) mu(e) = [every prime dividing n divides d]`.

Consequently, if S(d,R) counts positive integers at most R whose prime factors
divide d, then

`sum_(e<=R, gcd(d,e)=1) mu(e)*floor(R/e) = S(d,R)`.

For every a,b>0, one constant independent of d and R gives
`S(d,R) <= C_(a,b)*R^a*d^b` for positive d,R. The proof uses Rankin's
inequality and the exact finite-prime Euler product. Beyond a fixed prime
threshold each geometric factor is at most p^b; the finite remaining product
is absorbed into the constant. The product of distinct prime divisors divides d.

Define F_A(R) by restricting outer divisors to `A intersect [1,R]`:

`F_A(R) = sum_d mu(d)*floor(R/d) *
          sum_(e<=R, gcd(d,e)=1) mu(e)*floor(R/e)`.

For every epsilon>0, a constant independent of A and R satisfies
`|F_A(R)| <= C_epsilon*R^(1+epsilon)` for every finite A and every R.
Inner Möbius cancellation occurs before absolute values. The support count,
`floor(R/d)<=R/d`, and the harmonic sum prove the bound; three independent
small powers absorb support size and the logarithm. This includes arbitrary
outer cutoffs and outer tails.

## Exact boundary of completion

Let T(R) be the same double sum with **both** divisors restricted to `2..R`.
For every R>0,

`T(R) = R^2 - 2*R + F_[1,R](R)`.

Thus `|T(R)-R^2+2*R| <= C_epsilon*R^(1+epsilon)`. In particular, choosing
any epsilon in (0,1) shows the uncentered tail has a genuine quadratic leading
term. Completing divisor ranges cannot justify imposing a near-linear bound
on the raw complementary double tail. The exact polynomial is indispensable.
No numerical example, computation, or RH hypothesis enters either result.

## Relation to the remaining EDQ target

This is an estimate for the explicit unweighted coprime floor correlation.
It does not identify that correlation alone with the complete EDQ energy.
The actual residue/harmonic compensation and energy weights remain necessary.
For a general cutoff N, completing both divisor ranges leaves a term with
both divisors greater than N. The uniform bound on that **compensated** term,
its dependence on the preserved inner cutoff X, and its literal infinite
tail remain unproved. The cutoff-one identity does not settle growing N.
No route is retired, and no new norm-transfer receiver substitutes for that bound.

## Lean implementation and validation

Module: `GaloisForLFunctions.RHTower.EulerDeletionCoprimeColumnCancellation`.
Namespace: `RHTower.DeletionCoprimeColumn`.
Nine public theorems, two public definitions, and eight private helpers.
Main statements: `exists_supportedCount_le`, `complete_floor_column`,
`exists_floorCorrelation_le`, `unitCutoffDoubleTail_exact`, and
`exists_unitCutoffDoubleTail_remainder_le`.

The complete scratch passed `LEAN_NUM_THREADS=1 lake env lean` without
warnings or errors. The targeted final audit
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionCoprimeColumnCancellation`
built only this new leaf (6.9 seconds), reusing cached dependencies. Its import
is wired into the RHTower umbrella; no umbrella or full build ran.
A separate temporary `lake env lean` audit inspected only the eleven new
public declarations. Each depends solely on `propext`, `Classical.choice`,
and `Quot.sound`; no additional axiom, proof debt, or numerical result occurs.

The corpus indexes were refreshed once. Repository lint ran once and exited 1:
`ChiIncrementDifferenceJets` is unreachable from its umbrella and contains
`sorry` at lines 108 and 109 in `iteratedDeriv_chiIncrement_upper`. These errors
are outside this change; the new leaf has no reported lint error. Existing
large-file warnings and cached dependency diagnostics were not treated as
new proof failures. No computation or full rebuild ran.

Corpus basis: `SmoothPrimeThreeQuarterSigmaBound`,
`SmoothPrimeCoprimeConvolution`, `SmoothPrimeCoprimeLogExpansion`,
`LocalizedReciprocalMoebiusAmplitude`, `DivisorSwap`, `HarmonicLogBound`,
and mathlib's multiplicative-function and finite-prime Euler-product theorems.
The working card is [the direct covariance attack](../1-in-progress/edq-full-covariance-core-attack.md).
