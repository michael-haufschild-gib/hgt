# Overlap Gram smoothing needs a prime-defect corrector

- **ID:** overlap-gram-defect-corrector
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For every fixed `c>1`, eventually in `N`, `D_N(x,Gx)+τ D_N(x-Gx)` is nonnegative for every vector exactly when `τ≥1/4`. At equality its kernel is the one-dimensional inverse image of the arithmetic pole line under `I+G`.

`G` is the normalized physical mass Gram of the actual tilted unit spline at width `w=c/N`. `D_N(x,y)` is the bilinear prime-power edge energy; `D_N(x)=D_N(x,x)` and `b_n=1/sqrt(n)` on `1≤n≤N`.

## Proof

The prime defect vanishes exactly on `span(b)`. Indeed, orthogonal subtraction of the pole leaves the defect unchanged (`poleDefect_horizonPoleProjection`), and the uniform prime-defect spectral gap (`exists_poleDefect_ge`) forces a zero-defect orthogonal component to vanish. Conversely every edge of `b` vanishes.

The normalized Gram is positive semidefinite: its quadratic form is the integral of the squared atomic test divided by the positive one-atom mass. Thus `I+G` is injective, hence bijective in finite dimension.

The uniform density is strictly positive inside its support. Induction through convolution proves that its `(n+1)`-fold convolution is positive on `(-(n+1),n+1)`: the two open support intervals overlap whenever the argument is in this interval. Consequently the tilted unit spline is nonnegative everywhere and positive on `(0,1)`. Its width-`w` autocorrelation is positive for `|s|<w`, since both factors are positive at `(w-s)/2` and on a neighborhood of that point.

Choose `N≥3` such that `c/N<log 2` and `N/(N-1)<c`. The first atom is separated from all others, so `(Gb)_1=b_1=1`. The last two atoms overlap, since `log(N/(N-1))≤1/(N-1)<c/N`. Every Gram entry is nonnegative and the diagonal is one; the positive last off-diagonal entry gives `(Gb)_N>b_N`. Hence `Gb` is not proportional to `b`. Both inequalities hold eventually for each fixed `c>1`.

Let `u` be the unique solution of `(I+G)u=b`. It cannot belong to `span(b)`, since that would force `Gb` into the same line; thus `D_N(u)>0`. Because `Gu=b-u` and every pole edge vanishes,

`D_N(u,Gu)=-D_N(u)`, and `D_N(u-Gu)=4D_N(u)`.

Therefore this single vector gives the value `(4τ-1)D_N(u)`, negative for every `τ<1/4`. Conversely the exact edgewise identity

`D_N(x,Gx)+(1/4)D_N(x-Gx)=(1/4)D_N(x+Gx)`

proves nonnegativity for `τ≥1/4`. At equality, zero energy means `(I+G)x∈span(b)`, equivalently `x∈span(u)`.

## Scope

This rules out positivity of a proposed Gram-smoothed arithmetic reserve, not positivity of the complete Weil form. The correction coefficient is sharp; no uniform lower bound on the negative eigenvalue is asserted. A useful signed Weil reserve must account for the correction and its changed ground vector.

The negative-eigenvector conductor bound, growing-family signed residual estimate, and physical synthesis estimate remain open.

## Lean proof

[OverlapGramSmoothingNeedsAQuarterDefectCorrection.lean](../../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/OverlapGramSmoothingNeedsAQuarterDefectCorrection.lean):

- `poleDefect_eq_zero_iff_horizonPoleVector`: exact arithmetic kernel.
- `correctedOverlapDefect_eq`: the signed square completion.
- `eventually_normalizedTiltedGram_does_not_preserve_pole`: literal Gram ground-line failure.
- `eventually_correctedTiltedOverlapDefect_nonneg_iff`: sharp `1/4` threshold.
- `eventually_correctedTiltedOverlapDefect_ground_line`: exact corrected kernel and its strictly positive unsmoothed defect.

Direct Lean check passes. All audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
