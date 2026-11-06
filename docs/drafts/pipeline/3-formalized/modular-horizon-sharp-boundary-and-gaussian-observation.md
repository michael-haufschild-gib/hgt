# Sharp modular resonance boundary and Gaussian observation

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** RH is equivalent to the sharp analytic half-plane of normalized modular scattering; a literal Gaussian observation of the totient echo source preserves every Xi resonance and its multiplicity.
- **Namespace:** `GaloisForLFunctions.BlackHoleRingdown`

## Exact statements

For `z(q)=xiSpectralPoint q`, set `ω_D(q)=-z(q)/2-iD-i/4` and
`r_D(q)=D+1/4+Im z(q)/2`.

1. All normalized frequency poles are exactly `ω_D(q)`, with order
   `-meromorphicOrderAt XiC z(q)`. Analyticity on `Im ω>-a` is equivalent to
   `∀q, a≤r_D(q)`.
2. Reflected rates sum to `2(D+1/4)`; their minimum is
   `D+1/4-|Im z(q)|/2`. Thus `∀q, r_D(q)≥D+1/4` is equivalent to RH.
   The weaker bounds `D<r_D(q)<D+1/2` are unconditional.
3. Multiplication by `exp(-σ ω²)` preserves local analyticity and every meromorphic order.
   One fixed Gaussian probe therefore has the same RH-equivalent analytic boundary.
4. At `2 log c+v`, with `c>0` and `v>0`, the train dominates `(ϕ(c)/c) v^(-1/2)`.
   For all real `A,B,b,T`, some `t>T` satisfies `K(t)-A exp(t/2)>B exp(bt)`.
5. For `σ>0`, the observation `G_σ(t)=∫exp(-σ(t-u)²)K(u)du` converges absolutely. For every
   `a>1/2`, it is at most `exp(at+a²/(4σ)) ∫exp(-au)K(u)du`.
6. For `σ>0` and `Re w>1/2`, its absolutely convergent Laplace transform is
   `(π/σ)^(1/2) exp(w²/(4σ)) Λ(2w)/Λ(2w+1)`.
   Its continued frequency symbol retains every Xi pole with exact multiplicity. The elementary
   normalization factor is analytic and nonzero at those resonances.
7. For `σ>0`, Gaussian convolution of `A exp(bu)` is exactly
   `A sqrt(π/σ) exp(bt+b²/(4σ))`; mean subtraction commutes with observation.

## Lean declarations

Files lie in `formal/GaloisForLFunctions/BlackHoleRingdown/`.

| Module | Main declarations |
|---|---|
| `TheSharpAnalyticBoundary.lean` | `causalSymbol_isPole_iff`, `causalSymbol_resonance_order`, `ringdownRate_reflection_min`, `riemannHypothesis_iff_damping_lower_bound`, `riemannHypothesis_iff_causalSymbol_analytic` |
| `TheProbesPreserveEveryResonance.lean` | `gaussianPulse_transform`, `gaussianResponse_meromorphicOrderAt`, `riemannHypothesis_iff_gaussianResponse_analytic` |
| `TheEchoSpikesAndTheirGaussianObservation.lean` | `echoKernel_sub_mean_exceeds_every_exponential`, `integrable_gaussian_mul_echoKernel`, `gaussianEcho_le` |
| `TheGaussianObservationOfTheEchoSource.lean` | `gaussianEcho_sub_mean`, `laplace_gaussianEcho`, `fourierLaplaceTransform_gaussianEcho`, `gaussianEchoSymbol_resonance_order`, `gaussianEchoSymbol_resonance_isPole` |

## Proof mechanisms and audit

Affine changes preserve meromorphic orders. The shifted Xi numerator is nonzero at every Xi zero.
Functional-equation reflection pairs opposite transverse displacements. Finite support at each
time permits a single positive echo to bound the full train from below. Weighted source mass is
integrable; completing the square bounds each Gaussian observation. Exponential weighting turns
observation into an integrable convolution, so its transform factors exactly.

All four modules compile with `lake --old env lean`; dependency oleans were produced only for
imports needed by the final module. Main-theorem `#print axioms` audits return only
`propext`, `Classical.choice`, and `Quot.sound`.

The [active route](../1-in-progress/physics/thermal-and-black-holes/modular-horizon-sharp-resonance-route.md)
still requires a source-derived sharp estimate. Full time-domain RH equivalence and a full
geometric evolution theorem are not asserted here. No novelty claim.
