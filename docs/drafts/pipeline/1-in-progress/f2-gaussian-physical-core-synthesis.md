# F2 — Gaussian synthesis of the physical core packets

- **Stage:** 1-in-progress
- **Question:** Do the actual PM core packets with CWS window coefficients admit Gaussian-regularized infinite sums in a physical cusp norm, with the complete Weil form recovered as regularization vanishes?
- **Required output:** Convergence of the actual core functions, retaining the existing coefficient reflection and boundary correction. No new positivity premise or coefficient-defined replacement norm.

## Candidate estimate

For `w=2s`, `0<r=Re w<1`, use the Gaussian-ray identity

`fieldCore_w(a) = (2/Γℝ(w)) ∫₀∞ t^(w/2−1) θRay(t) θRay(a²t) dt`.

The Gaussian sum/integral comparison suggests
`|θRay(t)| ≤ min(1,t^(−1/2))/2`.
For `a≥1`, split the integral at `a^(−2)` and `1`. The three contributions give a bound

`|fieldCore_w(a)| ≤ (1/r + 1/(1−r) + 1/(2−r)) a^(−r) / |Γℝ(w)|`.

Reciprocity controls `a≤1`. The two absolute Cauchy moments then give a spectral bound for the physical period core. Gamma strip estimates and the actual zeta zero-free region should bound its coefficient on resonances by a polynomial times an exponential in height. Every positive Gaussian damping would dominate that growth.

A second estimate targets synthesis directly: weighted Cauchy–Schwarz gives

`|fieldCore_w(a)| ≤ (1/r + 1/(2−r)) a^(−r/2) / |Γℝ(w)|`.

Indeed `∫₀∞ t^(r/2−1)|θRay(t)|² dt ≤ 1/(2r)+1/(2(2−r))`, and scaling the second square contributes `a^(−r)`. The Cauchy kernel has absolute central moment at most `2/|averagingFactor(w)|`, uniformly for `0<r<1`. This bound retains enough cusp decay for Haar square energy and avoids a denominator at `r=1`.

The Gamma recurrence cancels the two normalizations exactly:

`Γℝ(w) averagingFactor(w) = π^((1−w)/2) Γ((w+1)/2) / w`.

Thus the candidate period-core bound is

`|core_s(a)| ≤ 2(1/r + 1/(2−r)) |w| π^((r−1)/2) |Γ((w+1)/2)|^(−1) a^(−r/2)`.

On `0<r<1`, the real power of `π` is at most one and the remaining Gamma argument stays in the fixed strip `1/2<Re z<1`. Only the left-edge factor `1/r` needs the zero-free region when summing resonances.

## Gates

1. Verify and formalize the Gaussian-ray bound and the explicit field estimate.
2. Prove the spectral bound for actual resonances, including parameters near both strip edges.
3. Prove convergence of the actual Gaussian-damped window core sum and the vanishing-damping Weil-energy limit.

The existing finite-word decay theorem proves admission separately for each parameter. It supplies no uniform spectral bound. No claim of completed-form positivity follows from regularized convergence alone.
