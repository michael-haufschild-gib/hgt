# Route PM: frequency-gap Abel pairing for the actual phase unitary

- **ID:** pm-ramanujan-band-abel
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean audited)
- **Continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.

## Exact statement

Let h and F be arbitrary complex L2 functions on the frequency line. Suppose the essential support of h stays distance at least d>0 from gamma. Let U_u be the actual corpus phase unitary with multiplier exp(i*tau*u), equivalently `MellinL2.fourierPhaseMulUnitary (u/(2*pi))`. For every delta>0 the scalar phase pairing is integrable on u>0, and

    delta * integral_(u>0) exp(-(delta+i*gamma)*u) <h,U_u F> du -> 0

as delta tends to zero from above. No condition on the actual arithmetic energy, no zero simplicity and no RH premise is assumed.

## Dependency-closed paper proof — [PROVED HERE]

For any f in L1, the joint integrand

    f(tau)*exp(-(delta+i*(gamma-tau))*u)

has modulus |f(tau)|*exp(-delta*u). This product is integrable on (0,infinity) times the frequency line. Fubini and the exact half-line complex-exponential integral give

    integral_(u>0) integral_tau f(tau)*exp(-(delta+i*(gamma-tau))*u)
      = integral_tau f(tau)/(delta+i*(gamma-tau)).

If f vanishes when |gamma-tau|<d, the resolvent denominator has modulus at least d on its support. The absolute value of the last integral is at most ||f||_1/d. Multiplication by delta proves the zero limit by squeezing.

For the stated Hilbert result take f(tau)=conjugate(h(tau))*F(tau). L2 integrability of the pointwise inner product supplies f in L1. The phase unitary's almost-everywhere representative and the literal L2 inner-product formula identify the scalar phase pairing with the preceding inner frequency integral. The same product-integrability theorem gives integrability of the actual scalar phase pairing. The gap condition on h implies the required gap condition on f.

## Contribution and remaining hard problem

This closes the fixed-profile Abel term in the actual moving-band contradiction. The variable-profile remainder, compact nonzero residue test and continuation of the actual tested scale transform remain separate obligations. The small-damping complete signed-energy ceiling and RH remain open.

## Verification status

`PMRamanujanBandAbel.lean` passed the targeted old-mode build (only this leaf built,43 seconds), mandatory final actual-file `lake env lean` with no diagnostics, and all four public axiom queries. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Umbrella wired once. Global lint reports thirteen unrelated unreachable modules and no own finding. No full build, umbrella build, heartbeat increase or numerical experiment was used.
