# Universal soft logarithmic confinement limit

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B16, B17; identify the limiting operator behind the confining margin.
- **Statement:** After subtracting `a+log a`, the actual ground energy converges to a fixed half-line logarithmic variational floor. Every minimizing state satisfies `a(W-1)→1`.
- **Status:** No complete paper proof or contribution claimed.

## Corpus connection

`gammaHardyPhaseRate_eq_log_reference_fourier` decomposes the actual Gamma symbol into `log(1+(2πξ)²)/2`, the scalar `archLogScalar`, and the Fourier transform of an integrable even kernel. `SuzukiSmallApertureGroundAsymptotic` transfers a uniformly controlled rescaled form to an actual Rayleigh infimum on a fixed interval.

The strong-confinement route supplies a different geometry: actual half-line minimizers have bounded `a(W-1)`. Rescaling by `x=-au` suggests a linear confining potential `8x`. The global affine variational comparison supplies both secant bounds for the minimizing exponential mass.

## Candidate limiting form

Use real unit-mass profiles `f` supported in the positive half-line, extended by zero, with finite absolute logarithmic Fourier energy and some positive exponential square moment. This domain is invariant under every positive dilation. Set

`Q(f)=archLogScalar+∫ log|2πξ|·|Fourier(f)(ξ)|² dξ+8∫₀∞ x f(x)² dx`.

Let `μ` be its Rayleigh infimum. The proposed limit is `λ(R)-a(R)-log a(R)→μ` as `a(R)→∞`. The scalar normalization here comes from the literal corpus symbol decomposition; no alternative Gamma normalization is assumed. No attainment of the limiting infimum is part of this claim.

## Missing proof inputs

1. Verify the dilation-stable domain and prove that its normalized Rayleigh set is nonempty and bounded below. A fixed trial enters the actual domain after sufficient compression; a rescaled actual minimizer retains a positive, possibly smaller, exponential moment.
2. Control the rescaled Fourier mass near frequency zero uniformly from the bounded physical first moment. Pointwise high-frequency symbol convergence alone is insufficient.
3. Show that the complete prime and pole terms vanish uniformly on the concentrating minimizing profiles. The existing ratio-independent remainder bound is only `O(1)`.
4. Pass both variational inequalities between the actual and limiting forms. For the upper bound each fixed trial suffices; for the lower bound use the uniformly controlled first moment of rescaled actual minimizers. The fixed-interval Suzuki argument does not supply this half-line tail control.

## Consequence of the proposed limit

For fixed `b>1`, comparing the minimizer at strength `a` with the floors at `ba` and `a/b` gives

`log b/(b-1)+o(1) ≤ a(W-1) ≤ log b/(1-1/b)+o(1)`.

Letting `b↓1` would give the exact virial scale. This consequence requires the proposed convergent renormalized energy, not merely its boundedness.
