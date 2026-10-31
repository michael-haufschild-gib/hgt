# Three quarters of zeta zeros on the critical line

- **ID:** three-quarters-critical-line-prime-surplus
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../../../reports/review-3110/astra.md, §4
- **Statement:** For every ε > 0, eventually `(3/4 - ε) N(0,T) ≤ N₀(0,T)`, with zeros counted with multiplicity.

## Goal

An unconditional Lean proof of the stated critical-line proportion.

## Arithmetic input

The selected-profile certificate gives
`(29/36 - ε) N(T,2T) - Sᵤ,η(T) + Moff(T,2T) ≤ N₀simple(T,2T)`.
The proposed route requires `Sᵤ,η(T) ≤ (1/18 + o(1)) N(T,2T)` for the same selected profiles, or sufficient control of `Sᵤ,η - Moff`.

## Approach

Retain the signed prime-pair kernel, even-shift parity, and full Ramanujan singular-series main term. Check whether existing source identities control the centered discrepancy at bandwidth `4/3`. Audit all imported arithmetic inputs before using the resulting census.

## Proof status

The report supplies the transfer, not the required surplus bound. No complete paper proof or Lean theorem for the stated proportion is established here.

`zeta_primeCoalescent_certificate_simple_and_offLineMultiple` and `Zeta23.paperInputs_zeta` pass `#print axioms` under `lake --old env lean`: their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The exact split `oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy` leaves `stabilizerDiscrepancyOddCoalSum` uncontrolled. The inspected prime-polynomial mean-square bounds retain a `ψ(X)` term at `X ≍ T^(4/3)`; the inspected higher-moment estimates require total exponent below one. Neither supplies the needed signed estimate. This does not refute the target or its proposed route.
