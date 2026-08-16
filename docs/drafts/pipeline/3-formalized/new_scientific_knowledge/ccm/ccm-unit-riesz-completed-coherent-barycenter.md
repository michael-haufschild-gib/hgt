# CCM unit-Riesz completed coherent barycenter

Status: formalized in Lean 4

## Frontier collision audit

Corpus search was run before proof with `scripts/formal_tools.py research` over completed coherent
responses, prime--polar source vectors, square-root-weighted von Mangoldt prefixes, and negative
half-line source laws.  Existing corpus knows:

- coherent increment Gram kernel and finite prime response;
- exponential polar kernel response;
- completed kernel response with limiting charge
  `criticalMellinChebyshevResolventSource (log N) / 2`;
- non-`L²` no-go for using that nondecaying response itself as HG amplitude; and
- codiagonal/finite-boundary scalar readouts of its charge.

It did not contain a literal signed prime-minus-polar `L²` vector whose matrix coefficients give
the response, nor a pointwise identification of its incoming half with a moving weighted-prime
discrepancy.

Literature audit covered Connes--Consani's scaling-Hamiltonian and Weil-positivity constructions.
Those works motivate the semigroup/coherent representation and positivity target, but do not state
the finite-aperture barycenter or bulk--boundary identity below.  Novelty claim is deliberately
narrow: not Weil positivity, Riesz smoothing, or coherent Gram kernels, but this completed
source-vector realization and its exact two-half-line arithmetic law.

## New object

Let

`v_x(s) = 1_{x<s} exp(-(s-x)/2)`

and `w_p = v_0 - v_{-p}`.  Define the polar barycenter

`P(s) = -(2/3) exp(s)` for `s ≤ 0`, and
`P(s) = (1/3) exp(-s/2)` for `s > 0`.

For integer aperture `N`, define the completed coherent barycenter

`F_N(s) = Σ_{2≤k≤N} (Λ(k)/√N) w_{log N-log k}(s) - √N P(s)`.

The polar term is not an invented profile.  Lean proves the exact source identity

`P(s) = ∫_{p>0} exp(-p) w_p(s) dp`

for every real `s`.

## Exact incoming law

For every `N : ℕ` and `t : NNReal`, set `X = N+2`.  Lean proves

`F_X(-t) = (2/3)√X exp(-t) - (exp(t/2)/X)
             Σ_{2≤k≤X, t<log(X/k)} Λ(k)√k`.

Thus incoming coherent bulk is exactly a moving square-root-weighted Chebyshev discrepancy.  It is
not a positive prime majorant and it retains prime--polar cancellation before squaring.

## Exact outgoing law

On `s>0`, every coherent increment has the common mode

`w_p(s) = exp(-s/2)(1-exp(-p/2))`.

After exact prime--polar completion,

`F_X(s) = (criticalMellinChebyshevResolventSource (log X)/2) exp(-s/2)`.

Consequently

`∫_{s>0} F_X(s)^2 ds =
  (criticalMellinChebyshevResolventSource (log X)/2)^2`.

## Hilbert-space theorem

Lean proves `F_N ∈ L²(ℝ)` unconditionally at every finite aperture and the exact orthogonal
decomposition

`∫_ℝ F_X(s)^2 ds =
  ∫_{s≤0} F_X(s)^2 ds +
  (criticalMellinChebyshevResolventSource (log X)/2)^2`.

This is the positive survivor of the earlier non-`L²` completed-response no-go.  Kernel response is
a matrix coefficient of an actual completed source vector; it is not itself the vector.

## Route impact

- **CCM-FU / CCM-UR:** prime and polar currents now share one explicit signed `L²` source before
  the scalar resolvent is read out.
- **CCM-HG / CCM-GS / CCM-EP:** exact half-line projection provides a source-selected
  operator-valued carrier and orthogonal bulk--boundary order before scalar trace/dephasing.
- **Route O:** supplies an actual arithmetic source vector for any later prolate/common-spectrum
  comparison, but does not discharge cross-spectral ordering.

No RH claim follows from carrier construction alone.

## New hard core exposed

The missing theorem is no longer “construct an `L²` completed carrier.”  It is a quantitative
source-specific order relating outgoing boundary energy to the moving incoming discrepancy without
assuming the RH-equivalent scalar bound.  Equivalently, one must find a non-circular contraction,
reflection, or divisor-preserving dephasing acting on `F_N` before scalarization.

A generic half-line projection is contractive but only proves boundary energy is at most total
energy; without a sharp arithmetic bound on incoming bulk this is insufficient and must not be
counted as route closure.

## Lean artifacts

- `formal/GaloisForLFunctions/RHTower/CCMUnitRieszCompletedCoherentBarycenter.lean`
- umbrella import: `formal/GaloisForLFunctions/RHTower.lean`

Premise-free capstones:

- `unitRieszCompletedCoherentBarycenter_eq_incoming_weightedPrefix`
- `integral_unitExponentialCoherentIncrementState`
- `integrable_sq_unitRieszCompletedCoherentBarycenter`
- `unitRieszCompletedCoherentBarycenter_resolvent_tail`
- `integral_Ioi_sq_unitRieszCompletedCoherentBarycenter`
- `integral_sq_unitRieszCompletedCoherentBarycenter_eq_bulk_add_resolvent`

Exact leaf audit:

    lake env lean GaloisForLFunctions/RHTower/CCMUnitRieszCompletedCoherentBarycenter.lean
    lake build GaloisForLFunctions.RHTower.CCMUnitRieszCompletedCoherentBarycenter

Both passed.  Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.

Global `scripts/formal_tools.py lint` reached this module through the umbrella but exited on two
unrelated concurrently introduced unwired modules, `GaussShiftRatioWeight` and
`XiMassLogSubcausticWindow`; no proof-debt or reachability error named this module.
