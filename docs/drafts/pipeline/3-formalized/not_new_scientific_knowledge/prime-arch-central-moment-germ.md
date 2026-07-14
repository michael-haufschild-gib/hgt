# Prime--archimedean central moment germ

- **ID:** prime-arch-central-moment-germ
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The normalized continued prime--Gamma relative trace has centered reciprocal Xi moments as its even Taylor coefficients; consequently, its countable integer-polynomial Hankel positivity implies RH.

## Goal

Eliminate the target-side moment-identification hypothesis from the countable trace--Hankel route. The resulting test values are finite expressions in Taylor coefficients of the fixed continued prime--archimedean source and contain no Xi zero data.

## Theorem

Let
\[
T(z)=-i\left(\operatorname{Flux}_{\infty}\!\left(\tfrac12+iz\right)
      -\frac{\operatorname{archFactor}'}{\operatorname{archFactor}}
        \!\left(\tfrac12+iz\right)\right)
\]
be the continued prime--archimedean relative trace and let
\[
G(z)=-\operatorname{dslope}(T,0,z).
\]
Then, as analytic germs at the origin,
\[
G(z)=\sum_{n\ge 0} M_n z^{2n},
\qquad
M_n=\sum_{\rho}m(\rho)
  \left(-\frac{1}{(\rho-\tfrac12)^2}\right)^{n+1}.
\]
Equivalently, every `M_n` is the complexification of the `n`th real analytic trace moment of `G`.

For `P\in\mathbb R[X]`, define the source Hankel value by pairing the coefficients of `P^2` with these Taylor moments. Lean proves this value equals `xiCentralTraceHankel P`. Hence
\[
\left(\forall P\in\mathbb Z[X],\ Q_{\mathrm{source}}(P)\ge0\right)
\Longrightarrow \mathrm{RH}.
\]

## Positive open core

The constant-polynomial level is now unconditional: `PrimeArchThetaFirstMoment.lean` proves the zeroth source moment is strictly positive from the positive theta-cusp density. The remaining task is to construct a coefficient-linear positive carrier for every polynomial, or equivalently prove the higher logarithmic-cumulant Hankel inequalities. The first nonconstant two-by-two minor is the explicit sixth-order theta-source inequality recorded in `theta-cusp-prime-arch-first-hankel.md`. The moment transport, divisor multiplicities, convergence radius, rational-density reduction, and integer-polynomial reduction require no further hypothesis.

The formalized `xi-endpoint-central-moment-dyadic-bridge` additionally reconstructs every moment
from the raw endpoint reciprocal traces:
\[
M_m=(-1)^{m+1}\sum_{n\ge0}\binom{n+2m+1}{2m+1}2^{-n}T_{n+2m+2}.
\]
Thus the endpoint and central-Hankel carriers no longer have a value-identification gap.  This does
not supply the missing Hankel positivity; it gives a second, explicit raw-trace interface on which
such a source theorem may be proved.

The paper consequence
[`prime-arch-moment-pole-residue-pinch-law.md`](../../2-fully-proven/not_new_scientific_knowledge/prime-arch-moment-pole-residue-pinch-law.md)
regroups this card's reciprocal-square resolvent in the ordinary moment variable.  It proves that
every source pole is simple with residue exactly `-R` times its divisor-fibre multiplicity, and
transfers its position and residue to the exact reflected Bernstein pinch coefficient.  This is
not additional Hankel positivity; it is a separate source-singularity interface into the
meromorphic-collar route.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/PrimeArchCentralMomentGerm.lean`.

Principal declarations:

- `xiCentralMomentPowerSeries_radius_pos`
- `xiCentralMomentGerm_eq_reciprocalSquareResolvent`
- `continuedPrimeArchSourceRelativeTrace_eventuallyEq_logDeriv_XiC`
- `normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm`
- `primeArchSourceMoment_eq_xiCentralReciprocalMoment`
- `xiCentralTraceHankel_eq_primeArchSourceTraceHankel`
- `riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative`

Validation:

- `lake build GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm` passes.
- Public capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1: source-pure statement and exact analytic route
- [x] 1 → 2: complete proof with absolute convergence and germ uniqueness
- [x] 2 → 3: Lean module builds and public axioms are standard
- [ ] 3 → 4: source-side positive-carrier construction
