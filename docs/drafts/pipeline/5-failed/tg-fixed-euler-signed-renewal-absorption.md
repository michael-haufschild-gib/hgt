# TG: fixed-Euler absorption of the actual signed deficit

- **ID:** TG-C9.23-NG
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement tested:** A fixed positive Euler modulus gives a critical-scale absorption budget for its unchanged signed renewal of the actual Chebyshev deficit.

## Exact killing theorem

`ccmPrimeDeficitEulerSignedRenewal_pole_limit` proves

`R_P D(T)/(T exp(T)) -> (1+gamma) (totient(P)/P)^2 > 0`.

Consequently `ccmPrimeDeficitEulerSignedRenewal_not_exponential_bound`
excludes even an absolute C exp(T) budget. This tests the actual signed
source, with no positivity premise on its values. It does not falsify RH,
native prime-polar energy summability, or adaptive Euler completion.

## Strongest established positive survivor

The entire finite two-label divisor-source quadratic form has the exact
leading coefficient

`(1+gamma) (sum_i v_i exp(-u_i))^2`.

Its normalized limit vanishes exactly on the signed moment-zero subspace;
for logarithmic integer shifts this is the harmonic-neutral subspace.
This is a rank-one classification retaining every pair term, not a
restatement of the obstruction. Paper proof and all seven Lean theorem
certificates are in
`../3-formalized/tg-fixed-euler-signed-renewal-pole.md`.

## New insight and surviving question

The positive rough-renewal kernel introduces a pole on the actual signed
source. Its fixed-modulus action and residual cancel this pole with opposite
signs; neither may be bounded separately at critical scale. The fixed-P
limit supplies no uniform estimate for P depending on T. The established
factorial-half identity is an explicit warning against exchanging those
limits. The remaining problem is genuine adaptive signed cancellation on
the original native covariance, including the harmonic correction.

## Status

Dependency-closed paper proof and Lean proof complete, 2026-10-04.
Leaf final audit and all seven foundations queries pass. Standard foundations
only. Wired and indexed; lint reports 15 unrelated unreachable modules.
No RH proof or falsification is claimed.
