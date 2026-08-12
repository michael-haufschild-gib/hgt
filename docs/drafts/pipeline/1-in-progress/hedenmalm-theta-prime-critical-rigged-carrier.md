# Hedenmalm theta prime critical rigged carrier

- **ID:** `hedenmalm-theta-prime-critical-rigged-carrier`
- **Stage:** 1-in-progress
- **Label:** `P-G108`
- **Type:** `[THEOREM (LEAN)] [ROUTE-P CARRIER CLASSIFICATION] [PRODUCER NO-GO]`
- **Parents:** `P-G104`, `P-G105`, `P-G106`, `P-G107`,
  `FrankensteinThetaPrimeTranslationPluckerLanding.lean`

## Frozen conjecture

Among radial exponential Hilbert riggings

```text
H_a = L2(R, exp(a |x|) dx),  a >= 0,
```

the simultaneous source requirements

1. every zero-blind possible Xi conormal in `|Im z| < 1/2` is a bounded Fourier--Laplace
   evaluation on `H_a`; and
2. normalized forward prime translation `f(x) -> exp(-L/2) f(x+L)` is contractive for every
   `L >= 0`

force exactly `a=1`. At that critical exponent, the actual theta integer anomaly belongs to the
carrier, every actual Xi conormal is bounded and kills that anomaly, and normalized prime
translation is a contraction with its literal character covariance.

## Complete paper proof `[PROVED HERE]`

The Riesz detector for evaluation at `z` has weighted energy

```text
exp(-a |x| - 2 Im(z) x).
```

It is integrable when `2 |Im z| < a`. Conversely, if `a < 1`, choose
`b=(a+1)/4 < 1/2`; on the negative half-line the detector at `z=b i` grows because
`a < 2b`, hence is not integrable. Uniform zero-blind admission of the full possible Xi strip
therefore forces `a >= 1`.

After conjugating `H_a` to Haar `L2`, normalized translation has squared multiplier

```text
R_a(L,x) = exp(-L) exp(a|x|) / exp(a|x+L|).
```

The reverse triangle inequality gives `R_a(L,x) <= 1` for `0 <= a <= 1`. If `a>1`, evaluating
at `x=-L`, `L>0`, gives `R_a(L,-L)=exp((a-1)L)>1`. Contractivity therefore forces `a<=1`.
Together the two source requirements force `a=1`, and both hold there.

For `a=1`, the existing interval-mass estimate bounds the integer anomaly by
`C_n exp(-|x|)`, so its weighted square is integrable. Its bounded evaluation is the literal
source transform and equals `shiftMultiplier(n,z) XiC(z)`; it vanishes at every Xi divisor.
Conjugation to Haar `L2` constructs the normalized shift as an explicit bounded multiplier and
proves norm at most one plus exact almost-everywhere agreement with physical integer translation.

## Producer falsification and positive survivor

- **Exact killing theorem/mechanism:** critical-carrier contraction controls the character
  `p^(-q)`, not Route P's half-density-normalized character `sqrt(p) p^(-q)`. The missing factor
  is exactly Route P's energy normalization. The admitted detector `z=i/4` lies strictly inside
  the critical strip, yet its Route-P energy is `p^(1/2)>1` for every prime. Thus carrier
  contractivity alone cannot prove the P-G95 inequality.
- **Strongest positive survivor:** the Goldilocks classification `a=1`, an explicit singular
  Hilbert rigging admitting both the physical anomaly and all possible divisor evaluations, exact
  prime covariance on that rigging, and a formal half-density-gap counterexample.
- **New insight:** P-G107's abstract “singular/rigged carrier” is uniquely fixed inside the natural
  radial exponential family. Route P is blocked neither by detector continuity nor anomaly
  admission. Remaining obstruction is a precise extra half-density Ward gain; any next producer
  must arise from source cancellation/quotient geometry and cannot follow from the ambient shift
  norm.
- **Status:** complete paper proof and direct Lean check; exact build, lint, axiom, umbrella audits
  pending.

## Falsifiers

- A value `a != 1` satisfying both quantified requirements kills the classification.
- Failure of the anomaly to lie in `H_1` kills the proposed physical carrier.
- If critical contraction implied prime-normalized energy at every admitted detector, the explicit
  `z=i/4` theorem would be false.

## Gates

- [x] prior Route P, fixed-fibre, Haar-carrier, and cyclicity corpus audited
- [x] conjecture frozen and hostile normalization audit performed
- [x] complete paper proof written
- [x] Goldilocks classification formalized
- [x] critical anomaly admission and divisor annihilation formalized
- [x] bounded critical translation and exact physical covariance formalized
- [x] explicit half-density-gap counterexample formalized
- [ ] external novelty audit complete
- [ ] exact build, lint, axiom, and umbrella audits pass

## Lean status

Umbrella-wired module
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaPrimeCriticalRiggedCarrier.lean` proves the
critical detector, critical anomaly, exact source transform, contractive normalized translation,
literal evaluation covariance, Goldilocks classification, and the admitted `z=i/4` producer
counterexample. Direct `lake env lean` passes.

## Log

- 2026-08-13 — P-G108 conjectured, proved, formalized, and producer interpretation falsified at
  exact half-density normalization.
