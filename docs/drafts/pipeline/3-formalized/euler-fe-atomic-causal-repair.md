# Full causal measures and atomic Gaussian repair

- **ID:** euler-fe-atomic-causal-repair.
- **Stage:** 3-formalized.
- **Type:** LOCAL RECONSTRUCTION AND CONVOLUTION RIGIDITY.
- **Source:** Euler–FE Gaussian source constraint; infinite atomic Euler operators.

## Objects and exact laws

Let `ψ(x)=exp(x/2−πexp(2x))`, `a(x)=πexp(2x)`,
`L=∂x−(1/2−2a(x))`, `r(t)=exp(2t)−1` and `w(t)=exp(t/2−r(t))`.
A positive causal measure is admitted when `∫w dμ<∞`; its total mass may be
infinite. Write `T_μψ(x)=∫ψ(x+t)dμ(t)` and `Q_μ=r_*(w μ)`.
For `a(x)>1`, the complete integrals satisfy

    T_μψ(x)=ψ(x)∫exp(−(a(x)−1)u)dQ_μ(u),
    L(T_μψ)(x)=−2a(x)ψ(x)∫u exp(−(a(x)−1)u)dQ_μ(u).

Equal defects on any interval `(A,B)` with `a(A)>1` imply
`μ|(0,∞)=ν|(0,∞)`. Atomic and singular continuous sources are included.
For countably supported `A,B` and absolutely continuous `K,H`, equal local
defects for `A+K` and `B+H` give `A|(0,∞)=B|(0,∞)` and `K=H`.

The domain contains every causal measure with a convergent Laplace transform
at any real parameter. It is closed under convolution, and
`T_(μ*ν)ψ=T_μ(T_νψ)`. If positive atomic `A` satisfies `A{0}=1`, then

    L T_(A+A*K)ψ = L T_(δ₀+A*H)ψ on (A₀,B₀)
      ⇒ A=δ₀ and K=H.

Here `K,H` are positive absolutely continuous causal measures in the same domain.
Their difference is an arbitrary admitted real signed continuous surgery.
The composed correction theorem concerns positive atomic `A`; the additive
separation theorem also covers differences of two positive atomic sources.

## Proof

Finite causal measures have holomorphic Laplace transforms on the right
half-plane. Local real values determine the transform by analytic uniqueness,
and finite-measure Laplace uniqueness identifies the measure. For a local first
moment on `(a,b)`, tilt by `u exp(−au/2)`. The tilted measure is finite without
an undamped first moment. Its local Laplace values determine it; cancelling the
strictly positive weight on `u>0` recovers the original positive-rate measure.

Gaussian damping and the injective rate chart reduce the actual response and
its derivative to these finite-measure laws. Undoing the chart and positive
damping recovers the original causal measure off zero. Restriction to a
countable carrier and its complement separates atomic and continuous parts.

The identity `r(t+u)=r(t)+r(u)+r(t)r(u)` gives `w(t+u)≤w(t)w(u)` on the causal
semigroup. Product integrability supplies convolution admission and Fubini.
Convolving with an absolutely continuous measure preserves absolute continuity.
Applying source separation to `A+A*K` and `δ₀+A*H` forces `A|(0,∞)=0`.
Causality and `A{0}=1` give `A=δ₀`; the continuous equality becomes `K=H`.

## Lean

Namespace: `GaloisForLFunctions.EulerFETransportTheory`.

| Module | Terminal declarations |
|---|---|
| `TheGaussianRateMeasureIsLocallyVisible.lean` | `restrict_Ioi_eq_of_gaussianMeasureMoment_local` |
| `TheGaussianDefectDeterminesCausalMeasures.lean` | `restrict_Ioi_eq_of_causalGaussianMeasureDefect_local`, `atomic_and_continuous_parts_eq_of_gaussianDefect_local` |
| `AtomicEulerCorrectionCannotRepairGaussianSurgery.lean` | `integrable_gaussianSourceWeight_of_laplace`, `integrable_gaussianSourceWeight_conv`, `causalGaussianMeasureResponse_conv`, `atomic_convolution_repair_is_trivial` |

All three modules pass direct `lake --old env lean` checks; transitive audits
use only `propext`, `Classical.choice` and `Quot.sound`.

## Scope

This closes positive atomic repair of continuous Gaussian surgery. Its positive
survivor is full local source reconstruction and convolution admission, both
paper-proved and formalized. The signed composed extension is proved in
`euler-fe-signed-atomic-gaussian-repair.md`. Neither excludes an exceptional finite layer
of the original ζ or prove same-depth replication, `LinAt C`, or AAL.
