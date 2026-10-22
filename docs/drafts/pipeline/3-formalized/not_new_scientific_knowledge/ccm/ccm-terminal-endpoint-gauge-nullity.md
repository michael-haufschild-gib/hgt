# CCM terminal endpoint gauge nullity

- **ID:** ccm-terminal-endpoint-gauge-nullity
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE
- **Source:** `CCMActualHeadOutgoingQuantileCompletedCharacteristicSeam.lean`,
  `CCMActualHeadCoherentCompletedGammaProducer.lean`
- **Formal module:** `GaloisForLFunctions.RHTower.CCM.CCMActualHeadOutgoingQuantileEndpointGauge`
- **Labels:** `[BRIDGE] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`

## Goal

Test whether the signed terminal endpoint atom in the completed quantile characteristic source is
a null gauge on the literal physical aperture space. If so, remove completed-error terminal
orientation from the actual source quadratic without claiming pointwise symbol equality.

## Closed theorem package

1. For `f` supported on `[-a,a]`,
   `∫ cos(2*pi*(2a)*xi)|Fourier(f)(xi)|^2 dxi = 0`.
2. Adding any scalar multiple of this diameter cosine to an integrable symbol leaves its quadratic
   average unchanged on the aperture space.
3. The completed quantile symbol is gauge-equivalent to the endpoint-free source
   `∫_[0,2a] exp(h/2)cos(2*pi*h*xi)dh - sum_(n<N)w_n cos(2*pi*log(n)*xi)`.
4. The actual Gamma-wall outgoing producer admits the same exact spectral normal form with this
   endpoint-free source.

All four conjectures are closed in Lean. Supporting declarations also prove integrability,
evenness, the exact finite characteristic discrepancy, and zero-frequency value of the
endpoint-free representative. Nine theorems plus one definition are in the module.

## Exact formal consequence

For the canonical cutoff `N = floor(exp(2a)) + 1`, the actual Gamma-wall outgoing producer equals
the fixed Gamma scalar, higher-Binet energy, polar reserve, and twice the spectral quadratic form of

`J_N,2a(xi) = integral_[0,2a] exp(h/2) cos(2*pi*h*xi) dh`
`              - sum_(n<N) w_n cos(2*pi*log(n)*xi)`.

No terminal completed-error atom remains in this representative. This is an equality in the
physical-aperture quadratic quotient, not a pointwise identity of symbols.

## Lean audit

- `lake env lean GaloisForLFunctions/RHTower/CCM/CCMActualHeadOutgoingQuantileEndpointGauge.lean` — pass.
- Target-only `lake build GaloisForLFunctions.RHTower.CCM.CCMActualHeadOutgoingQuantileEndpointGauge`
  — pass. No umbrella build run.
- `#print axioms` on all nine theorems — only `propext`, `Classical.choice`, `Quot.sound`.
- Forbidden declaration scan — no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- Module wired into `GaloisForLFunctions/RHTower.lean`; umbrella intentionally not built.

## Hostile audit

- Gauge equivalence is equality of quadratic averages on physical aperture heads, not pointwise
  equality of symbols.
- Terminal coefficient may have either sign and still multiplies a null quadratic direction.
- Removing the endpoint atom destroys zero-frequency mass balance pointwise; it is licensed only
  after restricting to the aperture quadratic form.
- Fixed Gamma scalar plus endpoint reserve remains strictly negative; this does not prove source
  positivity.

## Log

- 2026-08-21 — created from exact diameter-autocorrelation nullity found in corpus.
- 2026-08-21 — all four conjectures closed; module audited and promoted to Stage 3.
