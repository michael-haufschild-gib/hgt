# Library ticket: explicit prime--arch circle state and reflected Hankel carrier

- **Date:** 2026-07-15
- **Owner:** unassigned
- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/prime-arch-explicit-circle-state-reflection-law.md`
- **Target areas:** `formal/GaloisForLFunctions/HTGeometry`,
  `formal/GaloisForLFunctions/RHTower`
- **Status:** paper theorem complete; formalization deferred; no build run

## Requested HTGeometry infrastructure

Formalize a reusable circle-density theorem for an absolutely summable real sequence `m : Nat ->
Real` satisfying

```text
m 0 > 0,
2*sum_(n>=1) |m n| < m 0.
```

Construct the continuous even density

```text
w(exp(i*t))=m 0+2*sum_(n>=1) m n*cos(n*t)
```

and prove its two-sided bounds, mass one after normalization, and Fourier identity

```text
integral zeta^k dmu = m k/(m 0).
```

Then construct on `L^2(T,mu)` the multiplication unitary `U`, reflection
`Theta f(zeta)=f(conj(zeta))`, and constant vector `Omega`.  The reusable capstone should be

```text
<Theta U^i Omega,U^j Omega> = m (i+j)/(m 0).
```

For a real polynomial, identify this value with the difference between the squared weighted
cosine and sine norms.  Keep this reflection-polarized form separate from the ordinary Toeplitz
Gram; do not force one scalar kernel to be simultaneously Toeplitz and Hankel.

## Requested RHTower specialization

Use the existing reciprocal-square moment identities and source estimates to prove

```text
(734/819)*primeArchCentralCurvature <= primeArchCircleDensity
primeArchCircleDensity <= (904/819)*primeArchCentralCurvature
```

and the exact normalized reflected-Gram identity for `normalizedPrimeArchMoment`.  Connect it to

```text
primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis
primeArchSourceTraceHankelIntDegreeTwoTailNonnegative_iff_riemannHypothesis
primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis
```

Also formalize the unconditional coefficient inequality

```text
normalizedReflectedValue P
  >= (734/819)*(P.coeff 0)^2
      -(85/819)*sum_(n>=1) (P.coeff n)^2.
```

Its terminal corollary should restrict the integer-polynomial RH criterion to the complementary
tail-dominant cone

```text
734*(P.coeff 0)^2 < 85*sum_(n>=1) (P.coeff n)^2.
```

The formal proof should reuse, rather than duplicate:

```text
summable_xiZeroCopyReciprocalSquare_pow
xiCentralReciprocalMoment_im_eq_zero
normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment
normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm
normalizedPrimeArchMoment_zero_pos
xiZeroCopy_fortyOne_div_two_lt_im_sq
xiThermalNode_pos
xiThermalOrientationTerm_le_one_over_eightyFour_node_sq
```

## Radial Poisson chamber

Formalize the continuous map

```text
r |-> P_r,
P_r(exp(i*t))=(1-r^2)/(1-2*r*cos(t)+r^2)
```

on `[0,2/41]` and the compact convex set of its probability mixtures in `C(T)`.  The RHTower
capstone is

```text
RiemannHypothesis
  <-> primeArchCircleDensity/primeArchCentralCurvature
      belongs to closedConvexHull {P_r | 0<=r<=2/41}.
```

The converse should pass through `PrimeArchMomentRepresentation`; it must not assume an
infinite-support measure because non-strict Hankel positivity already suffices for RH.

## Exact non-implication to retain

Formalize, if useful for API discipline, the family

```text
w_(epsilon,N)(t)=1-epsilon*cos(2*N*t).
```

For `0<epsilon<1`, it is a strictly positive analytic even density, but its reflected quadratic
value on `z^N` is `-epsilon/2`.  This prevents future attempts to derive the RH-bearing reflected
sign from an `L^infinity` coercivity bound or strict Schur contractivity alone.

## Verification constraint

No Lean build, lint, numerical test, or scratch computation was run while producing the paper
theorem, following the active user instruction.  Later verification must use narrow file-level
checks only.
