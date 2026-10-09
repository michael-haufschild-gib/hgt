# BAG exact signed mixed-profile cancellation

- **Stage:** 3-formalized

Define P(u)=int_0^1 (exp(ut)-1)/t dt with removable endpoint; E(u)=int_0^1 exp(ut)dt;
F(u)=exp(P(u)). The full candidate mixed-frequency source profile has entire
continuation G(u)=F(u)*(E(u)-1)*dslope(E,0,u), equal to F(u)*(1-E(u))^2/u for u!=0.
For every positive real c, G(c+it) is absolutely integrable and its signed
integral over the entire real t-line is zero.

P'(u)=E(u) by differentiation under its actual compact integral; the local
exponential derivative is uniformly dominated. The identities E(0)=1 and
uE(u)=exp(u)-1 give K(u)=uF(u), K'(u)=exp(u)F(u). All functions are entire;
the displayed G continuation removes the apparent pole without an assumption.

On Re(u)<=c, the real part of the defining P integral is bounded by P(c). Thus
norm(F(u))<=exp(Re(P(c)))=:A(c), and norm(K'(u))<=A(c)*exp(Re(u)). Apply the
corpus exponential-half-plane vertical-integral theorem to K'(-z). The integral
of K' along any vertical segment with fixed real part x<=c has norm bounded
independently of its height. On the real segment from x to c the derivative
bound integrates to at most A(c)*exp(c). Consequently K is bounded on this
whole left half-plane. Also norm(E(u))<=exp(max(c,0)). The exact G formula gives
norm(G(u))<=B(c)/norm(u)^2 for every nonzero u in that half-plane.

The latter bound is integrable on every nonzero vertical line: its real
majorant has integral pi*B(c)/abs(a). Entire holomorphy and the inverse-square
horizontal bound discharge the existing VerticalStripContourShift theorem.
Shift the c-line to -X, X>0. The latter integral has norm at most pi*B(c)/X;
letting X grow proves the signed integral is exactly zero.

This proof uses the exact differential identity instead of the initial
oscillatory cosine estimates. Lean production module
ChiRamanujanMixedProfileCancellation (436 lines) passed its foreground
`lake --old env lean ... -o ...olean` audit (13632, empty output).
M1, the identification of G with the actual mixed-
frequency growing labelled source, remains unproved. Physical remainder and
frequency-tail control remain required before any signed axes saving follows.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiRamanujanMixedProfileCancellation` | `criticalExponentialMean_eq_integral`, `criticalEulerExponent_hasDerivAt`, `criticalEulerCarrier_primitive_deriv`, `criticalMixedProfile_differentiable`, `criticalMixedProfile_zero`, `criticalMixedProfile_eq`, `criticalMixedProfile_vertical_integral_zero` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
