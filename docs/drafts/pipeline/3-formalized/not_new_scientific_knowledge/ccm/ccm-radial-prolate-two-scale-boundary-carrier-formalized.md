# The constrained CCM radial-prolate tail has forced inner and outer scales — formalized closure

- **ID:** `ccm-radial-prolate-two-scale-boundary-carrier-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-radial-prolate-two-scale-boundary-carrier.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCMRadialTwoScaleCarrier` (new)
- `GaloisForLFunctions.RHTower.CCMRadialGlobalDefectMass` (new in the companion card)
- `RHTower.RadialLeakageMassNormalization`, `RHTower.RadialLeakageArcsineMeasure` — the leakage
  layer this is built on.
- `RHTower.CCMEndpointResponseConstants` — the source of `(4)` and `(7)` as limit inferences.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(3)` | `norm_sq_twoModeExterior` | the exact orthogonality formula for the two-mode exterior leakage |
| `(8)`, `(13)` | `scaledProfile`, `scaledProfileSq` | the exterior profile at an arbitrary scale; the outer and inner profiles are `α = λ` and `α = λ³` |
| half-line changes of variables | `integral_Ioi_shift`, `integral_Ioi_dilate` | translation and dilation of the ray |
| `(9)`, `(16)` first half | `integral_Ioi_scaledProfileSq` | `∫₀^∞ = α δ/(2\|q(λ)\|²)` exactly, for every positive scale |
| `(10)` | `tendsto_integral_Ioi_scaledProfileSq_outer` | the outer scale normalizes the total mass to `1/(4π)` |
| `(16)` | `tendsto_integral_Ioi_scaledProfileSq_inner` | the inner scale does not: its mass diverges like `λ²/(4π)` |
| `(14)` first half | `scaledProfile_zero` | `I_λ(0) = 1` |
| endpoint slope | `hasDerivAt_scaledProfile` | the slope at scale `α` is exactly `q′(λ)/(α q(λ))` |
| `(11)`, `(12)` | `endpointLogDeriv_eq` | `(κ − c²)/(2λ) = −2π²λ³ + κ/(2λ)` with `c = 2πλ²` |
| `(14)` | `tendsto_endpointLogDeriv_div_cube` | the inner slope tends to the universal `−2π²` |
| `(15)`, `(17)` scale separation | `outerSlope_eq_sq_mul_innerSlope` | the two slopes differ by exactly `λ²` — an identity, not an asymptotic coincidence |

## Axioms

`#print axioms` on all eleven declarations returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The finite-Fourier eigenrelation `(5)` `F(e_{m,λ}) = χ_m e_{m,λ}` inside the band, and the
  fixed-mode ratio `d₀/d₁ = O(λ^{−8})`.
- The constrained-prolate limit `(4)` and the endpoint-response height `(7)`, which appear as named
  hypotheses; both are proved as limit inferences in `CCMEndpointResponseConstants` from their own
  classical inputs.
- The prolate eigenvalue asymptotic `κ_m(c) = O(c)`, which enters `(14)` as the hypothesis
  `κ/λ⁴ → 0`.
- The card's own forward gates: the matched profile and transition law `(17)`, its arithmetic
  correlations, and the true Weil transfer.

## Verification performed

- `lake env lean` on the new module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCMRadialTwoScaleCarrier`: success.
- `#print axioms` on every declaration: clean.
- Umbrella import added.
