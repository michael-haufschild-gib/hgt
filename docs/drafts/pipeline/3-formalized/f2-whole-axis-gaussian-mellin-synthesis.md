# F2 — whole-axis Gaussian Haar and Mellin synthesis

- **Stage:** 3-formalized.
- **Result:** Every Gaussian-regularized CWS coefficient vector synthesizes an actual core function in `L²((0,∞),da/a)`. Its Mellin integral converges on `0<Re u<1` and equals the sum of the individual Mellin integrals.
- **Scope:** Convergence and integral interchange. Coefficient uniqueness and Weil positivity remain separate.

## Proof

Write `y=Im s`, `r=2 Re s`, and use the audited bound
`|core_s(a)|≤K(s)min(a⁻¹,a^(1−r))`, where `K(s)=C(1+y)^N exp(πy/2)`.
Splitting at one gives

`∫₀∞ |core_s(a)|² da/a ≤ K(s)²(1/(2−2r)+1/2)`.

Reflection and the zero-free estimate give `1/(1−r)≤116y`. Hence the Haar norm is at most `11K(s)(1+y)`. The existing Gaussian height summability and `|x_(2s)|≤‖x‖₂` make the sum of the weighted column norms finite. Completeness of `L²` yields a sum; countability and almost-everywhere evaluation of absolutely summable `L²` series identify it with the literal pointwise Gaussian core series divided by `√a`.

For `σ=Re u∈(0,1)`, the endpoint bound implies `|core_s(a)|≤K(s)` below one and `≤K(s)/a` above one. Therefore

`∫₀∞ |a^(u−1)core_s(a)| da ≤ K(s)(1/σ+1/(1−σ))`.

Gaussian height summability again makes the sum of these absolute integrals finite. Bochner integration of the series gives exactly

`Mellin(F_(ε,x))(u)=Σ_s exp(−εy²)x_(2s) Mellin(core_s)(u)`.

For each individual resonance, local integrability and the stronger endpoint powers also make its literal Mellin transform holomorphic on `r−1<Re u<1`.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/GaussianCoreMellinSynthesis.lean`:

- `upperMayerCore_finite_whole_haar_energy`
- `gaussianWholePhysicalColumn_summable`
- `gaussianPhysicalCore_eq_wholeLp_tsum`
- `gaussianPhysicalCore_finite_whole_haar_energy`
- `upperMayerCore_mellinConvergent`
- `gaussianPhysicalCore_hasMellin`
- `upperMayerCore_mellin_differentiableAt`

Final individual `lake --old env lean` audit passed without warnings. All six printed endpoints have only `propext`, `Classical.choice`, `Quot.sound`. Module wired into the umbrella.

[Faithful completion](../1-in-progress/f2-faithful-gaussian-core-completion.md) still requires normal meromorphic convergence and pole extraction.
