# F2 — uniform spectral bounds for physical cores

- **Stage:** 3-formalized
- **Result:** There are `C≥0`, `N∈ℕ` such that every upper Mayer resonance `s` satisfies
  `|mayerPeriodCore_s(a)| ≤ C(1+Im s)^N exp(π Im s/2) a^(−Re s)` for every `a>0`.
- **Purpose:** Control spectral height and cusp energy together, enabling Gaussian synthesis of actual PM cores with window coefficients.

## Proof

Set `w=2s`, `r=Re w∈(0,1)`. Gaussian sum/integral comparison and theta reciprocity give
`|θRay(t)|≤min(1,t^(−1/2))/2`.
Consequently

`I(r)=∫₀∞ t^(r/2−1)|θRay(t)|²dt ≤ 1/(2r)+1/(2(2−r))`.

Scaling the second theta square by `a²` contributes `a^(−r)`. Weighted Cauchy–Schwarz in the existing exact theta-core integral yields

`|fieldCore_w(a)| ≤ (1/r+1/(2−r)) a^(−r/2)/|Γℝ(w)|`.

The absolute central Cauchy moment is at most `2/|averagingFactor(w)|`: after removing that normalization, its density is at most one below `t=1` and at most `t^(−2)` above it. Thus the actual convolution retains the decay. Gamma recurrence gives

`Γℝ(w) averagingFactor(w)=π^((1−w)/2)Γ((w+1)/2)/w`,

hence the explicit strip bound

`|mayerPeriodCore_s(a)| ≤ 2(1/r+1/(2−r))|w|π^((r−1)/2)|Γ((w+1)/2)|^(−1)a^(−r/2)`.

Every nontrivial zero has ordinate at least four. The two-sided zero-free region gives `1/(2 Re s)≤58 log(2 Im s)≤116 Im s`. Also `1/(2−2 Re s)≤1`, `|2s|≤2(1+Im s)`, and the real power of `π` is at most one. The reciprocal Gamma bound on `1/2<Re(s+1/2)<1` supplies a polynomial times `exp(π Im s/2)`. Combining these bounds proves the result.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/PhysicalCoreSpectralBounds.lean` contains the exact strip bound and the uniform resonant bound. Final individual `lake --old env lean` audit passed without warnings. `mayerPeriodCore_spectral_bound` and `upperMayerCore_growth_bound` have only `propext`, `Classical.choice`, `Quot.sound`. Module wired into the umbrella.

This proves a growth estimate, not complete Weil positivity. [Gaussian physical synthesis](f2-gaussian-physical-core-synthesis.md) now supplies convergence and the vanishing-damping Weil limit.
