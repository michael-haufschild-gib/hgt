# Exact local positivity phase of the ordinary-floor golden source

- **ID:** biarithmetic-golden-divisor-positivity-phase
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (Lean formalization incomplete)
- **Proof status:** Only statements with completed Lean checks and axiom audits are proved. Paper arguments below are proof plans; every significant claim remains a formalization obligation.
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** For the actual golden inverse coefficients lifted to powers of five and every `t>=0`, every ordinary divisor response lies in `[0,1]` precisely when `t<=1/5`. Within the source's damping interval `0<=t<=1`, every escaping golden lift therefore fails the actual Möbius source's positive-divisor-response constraint.

## Exact divisor response

Let `alpha=(5+sqrt(5))/2`, `beta=(5-sqrt(5))/2`, `a=alpha*t`, and
`b=beta*t`. The checked arithmetic lift has `c_t(1)=1` and
`c_t(5^r)=-(a^r-b^r)/sqrt(5)` for `r>=1`, and is zero off powers of five.
If the exponent of five in a positive integer `n` is `M`, its ordinary divisor
response is therefore exactly

`d_t(n)=D_M=1-(1/sqrt(5)) sum_(r=1)^M (a^r-b^r)`.

Since `0<=b<=a`, this sequence decreases from `D_0=1`; thus every response
is at most one. Every value `D_M` occurs, at `n=5^M`.

## Complete positivity classification

If `a<1`, both geometric series converge and

`lim_M D_M = 1-(1/sqrt(5)) [a/(1-a)-b/(1-b)]
           = (1-t)(1-5t)/[(1-alpha*t)(1-beta*t)] =: L_t`.

The second identity uses only `alpha+beta=5`, `alpha*beta=5`, and
`alpha-beta=sqrt(5)`. The denominator is positive. Moreover `a<1` forces
`t<1/alpha<1`, so the numerator is nonnegative precisely when `t<=1/5`.
Monotonicity gives `L_t<=D_M<=1`. Consequently all responses are nonnegative
exactly for `t<=1/5` within this regime; when `t>1/5`, convergence to the
strictly negative limit supplies a negative response.

If `a>=1`, then `t>0`. Put `e_r=a^r-b^r`. Since `a>=1` and
`a>=b>=0`, the recurrence
`e_(r+1)=a e_r+(a-b)b^r` shows `e_(r+1)>=e_r`. Hence for every
`r>=1`, `e_r>=a-b=sqrt(5)t`, giving the exact finite bound

`D_M <= 1-M t`.

Thus `D_M` tends to negative infinity. This covers the pole `a=1`
without dividing by `1-a`, and supplies a finite negative witness whenever
`M>1/t`. The finite bound strengthens the previous eventual-series argument.

Since `alpha/5<1`, the interval `0<=t<=1/5` belongs to the first regime.
Combining both cases proves the global equivalence for every `t>=0`.
The proof never uses the upper damping bound: `a<1` itself forces `t<1`,
while the finite divergence estimate holds for all `a>=1`. The extended
parameter range is therefore dependency-closed on paper; its use in the
payment comparison remains within `0<=t<=1`, where the source mean is certified.

## Positive survivor and source comparison

The full ordinary divisor-response range has supremum one and infimum `L_t`
when `a<1`. It is bounded precisely in this regime; for `a>=1`, its infimum
is negative infinity. In the positive phase its exact enclosing interval is
`[L_t,1]`, with `L_0=1` and `L_(1/5)=0`.

The actual damped Möbius divisor response is a finite product
`product_(p|n)(1-p^(-epsilon))`, hence lies in `[0,1]` for positive damping.
By the already formalized golden admission threshold, escape requires
`alpha*t>=sqrt(5)`. Such `t` is strictly greater than `1/5`, since
`alpha/5<1<sqrt(5)`. Every escaping ordinary-floor golden lift therefore
fails this local source constraint. Conversely every positivity-compatible
golden lift is paid, because `alpha*t<=alpha/5<sqrt(5)`.

This is a calibration of the specified ordinary-integer lift. It does not
exclude the intrinsic positive Beurling system: that system has different
prime objects, multiplicities, counting measure, and divisor incidence.
Nor does positivity of divisor responses alone prove admission for arbitrary
integer sources. The source constraint separates this golden test family,
not every possible escape family.

## Verification and novelty

The coefficient identity and ordinary-floor admission threshold are already
formalized in `GoldenArithmeticSource.lean` and `GoldenSourceAdmission.lean`.
The remaining argument is a dependency-closed geometric-series proof.
No originality claim is made for partial geometric sums; the programme content
is the exact source-positivity chamber and its distinction from intrinsic
Beurling positivity.
The corpus search for golden inverse divisor-response positivity returned the
existing inverse-coefficient and source-lift theorems, but no sign-phase theorem.
This search is a reuse check, not evidence of external originality.

- [x] Exact paper divisor formula, complete sign classification, and boundedness phase.
- [x] Positive survivor specified; formalization remains required before retiring the escaping-source calibration.
- [ ] Lean divisor enumeration, exact response interval, and divergence at the boundary.
- [ ] Direct checks, transitive axiom audits, and umbrella wiring.

The checked source `BiarithmeticGeometry/GoldenDivisorResponse.lean` contains
the valuation formula, realization of every profile value at a power of five,
monotonicity in the valuation and parameter, and the universal upper bound one.
Its direct check and all five audits passed; its
[stage-3 card](../3-formalized/biarithmetic-golden-divisor-response.md) records that scope.
The unchecked draft `/tmp/BiarithmeticGoldenDivisorPositivity.lean` contains
the exact rational limit and greatest lower bound, finite divergence bound,
full nonnegative-parameter sign classification, and payment of every
positivity-compatible source in the damping interval. These dependent claims
remain unproved until their source check and transitive audits pass.

The positivity draft also explicitly transfers the profile range to actual
positive integer arguments, proves its supremum and infimum, and states
negative-infinity convergence along powers of five and the exact boundedness
phase. These are the existing range claims above; all remain unchecked.
The positive-integer restriction is essential for the infimum statement,
because the separately defined response at zero is zero.
