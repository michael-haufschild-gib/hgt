# CCM aperture cosine-gauge quotient

- **ID:** ccm-aperture-cosine-gauge-quotient
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE
- **Source:** `CCMActualHeadOutgoingQuantileEndpointGauge.lean`,
  `CCMActualHeadOutgoingQuantileTransportProducer.lean`,
  `CCMActualHeadCoherentCompletedGammaProducer.lean`
- **Formal module:** `GaloisForLFunctions.RHTower.CCM.CCMActualHeadApertureCosineGaugeQuotient`
- **Labels:** `[BRIDGE] [FORMALIZED] [NEW FORMAL SYNTHESIS] [NOT AN RH PROOF]`

## Goal

Upgrade terminal endpoint nullity to the full aperture-null cosine ideal and use the quotient to
identify the coherent corrected CCM average with the endpoint-free outgoing quantile source.

## Closed theorem package

1. For every physical aperture head and every lag `h >= 2a`,
   `integral cos(2*pi*h*xi)|Fourier(f)(xi)|^2 dxi = 0`.
2. If `w` is integrable on `[2a,infinity)`, then the entire exterior cosine transform
   `xi |-> integral_[2a,infinity) w(h) cos(2*pi*h*xi) dh` has zero quadratic average on the
   aperture head.
3. In particular, the exterior decaying first-Binet polar half is an aperture-null gauge.
4. The coherent corrected-symbol average equals the exact endpoint-free outgoing quantile producer:
   fixed Gamma scalar + higher-Binet energy + polar reserve + endpoint-free characteristic average.
5. Canonical reverse-prime control is equivalent to nonnegativity of this endpoint-free expression.

All five conjectures are closed in Lean. Eight theorems and two definitions establish pointwise-lag
nullity, absolute product integrability, arbitrary exterior-weight gauge nullity, the first-Binet
specialization, coherent/outgoing equality, and the RH-bearing canonical-head equivalence.

## Strongest positive statement

For every integrable real weight `w` on `[2a,infinity)`, define

`G_w(xi) = integral_[2a,infinity) w(h) cos(2*pi*h*xi) dh`.

Then every physical aperture head `f` satisfies

`integral G_w(xi) |Fourier(f)(xi)|^2 dxi = 0`.

Thus support geometry produces an infinite-dimensional null ideal of spectral symbols. The terminal
completion atom and decaying first-Binet exterior tail are two members of one gauge quotient.

## RH-facing consequence

For the canonical cutoff `N = floor(exp(2a)) + 1`, the coherent corrected CCM average equals

`2 gammaRate(0)||f||^2 + higherBinet(f) + 4||f||^2`
`  + 2 integral J_N,2a(xi)|Fourier(f)(xi)|^2 dxi`,

where `J_N,2a` is the endpoint-free continuous-minus-prime characteristic symbol. Canonical
reverse-prime control is equivalent to nonnegativity of exactly this expression.

## Lean audit

- Source `lake env lean` — pass.
- Target-only `lake build GaloisForLFunctions.RHTower.CCM.CCMActualHeadApertureCosineGaugeQuotient`
  — pass. No umbrella build run.
- `#print axioms` on all eight theorems — only `propext`, `Classical.choice`, `Quot.sound`.
- Forbidden declaration scan — no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella intentionally not built.

## Hostile audit

- Exterior gauge nullity is head-space support geometry, not pointwise symbol equality.
- Corrected CCM symbol remains negative at zero for small prime-free aperture.
- Fixed Gamma scalar plus polar reserve can be negative; higher-Binet and characteristic terms must
  be controlled jointly.
- The coherent/outgoing equality must not be proved only by naming both sides `sourceQuadratic` if a
  direct quotient mechanism can be formalized.
- This package changes representation of the RH-bearing inequality; it does not prove its sign.

## Log

- 2026-08-21 — conjectured from corpus theorem
  `ccmActualHeadSymmetricAutocorrelation_eq_zero_of_two_aperture_le` and exact Binet split.
- 2026-08-21 — all conjectures closed, audited, and promoted to Stage 3. External novelty not
  claimed; classification is conservative pending dedicated literature comparison.
