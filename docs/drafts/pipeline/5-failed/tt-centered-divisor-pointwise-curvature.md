# Pointwise mixed-curvature positivity of the centered divisor forcing

- **ID:** tt-centered-divisor-pointwise-curvature
- **Stage:** 5-failed
- **Type:** FALSIFIED; exact cofactor law formalized
- **Source:** [Route TT](../../../reports/rh-current-frontier-map.md), [working log C31--C33](../1-in-progress/route-tt-unconditional-source-loop.md)
- **Statement tested:** the squared divisor forcing of the actual coefficients `Lambda-1` has nonnegative mixed prime-dilation differences at every coprime cofactor.

## Goal

The attempted producer would supply a local positive decomposition for
the signed variance in working-log C29, hence a candidate route to the
centered TT/T1 covariance bound. Only this pointwise producer is
falsified. Neither C29's aggregate inequality nor RH is falsified.

## Exact source and paper proof

Write `tau(n)=card(divisors(n))` and
`q(n)=log n-tau(n)=sum_(d|n)(Lambda(d)-1)`.
For distinct primes p,q and a positive cofactor m coprime to both, set
t=tau(m) and

```
D_(p,q)(m)=q(p*q*m)^2-q(p*m)^2-q(q*m)^2+q(m)^2.
```

The exact formula is

```
D_(p,q)(m)
 =2*log p*log q-4*t*(log p+log q)-2*t*log m+9*t^2.
```

**[PROVED HERE]** Divisor-count multiplicativity gives counts 2t, 2t,
and 4t at pm, qm, and pqm. Their logarithms add. Substituting these
three values and q(m)=log m-t into D and expanding proves the formula.
The source identity follows from `sum_(d|n) Lambda(d)=log n`.

For a third distinct prime r, t=2, so

```
D_(p,q)(r)=2*log p*log q-8*(log p+log q)-4*log r+36.
```

For every real B and natural cutoff K, choose a prime r greater than
p,q,K and greater than the exponential threshold making the last
expression less than B. Infinitely many primes and monotonicity of log
justify this choice. Hence these literal source curvatures are unbounded
below along prime cofactors. No numerical experiment or unproved
analytic estimate enters the proof.

The one-prime law is also exact: when p does not divide m,

```
q(p^j*m)=q(m)+j*(log p-tau(m)).
```

It follows from `tau(p^j*m)=(j+1)*tau(m)` and logarithm additivity.

## No-go closure

- **Killing theorem:** `xiMassCenteredDivisorMixedCurvature_unboundedBelow` gives arbitrarily negative mixed curvature beyond every cofactor cutoff, for each pair of distinct primes.
- **Strongest positive survivor:** `xiMassCenteredDivisorMixedCurvature_eq` gives the exact law for every positive coprime cofactor, retaining both `tau(m)^2` and `tau(m)*log m`; `xiMassCenteredDivisorForcing_primePow_mul` supplies the complete affine prime-chain law. These identify the source and its curvature, rather than restating the failed sign.
- **New insight:** prime-chain affineness does not yield positive mixed square curvature. The cofactor term can dominate with the opposite sign at arbitrarily large physical indices. A global proof must retain compensation between cofactors and its cutoff weights.
- **Paper status:** dependency-closed proofs above.
- **Lean module:** [XiMassCenteredDivisorMixedCurvature.lean](../../../../formal/GaloisForLFunctions/RHTower/XiMassCenteredDivisorMixedCurvature.lean).
- **Verification:** targeted `lake build --old +GaloisForLFunctions.RHTower.XiMassCenteredDivisorMixedCurvature` and final direct `lake env lean GaloisForLFunctions/RHTower/XiMassCenteredDivisorMixedCurvature.lean` passed without warnings. All six public theorems were audited with `#print axioms` in `/tmp`; only `propext`, `Classical.choice`, and `Quot.sound` occur. The module is imported by `RHTower.lean`, and the formal index was regenerated. Repository `lint --check-generated` exited 1 with twelve other modules unreachable from the umbrella; this module was not reported. No umbrella build was run.

## Remaining hard problem

Prove an upper bound for the full centered TT/T1 covariance, or prove
C29's global signed variance nonnegative with all arithmetic weights
retained. This card establishes neither estimate. RH remains unproved
and unfalsified.
