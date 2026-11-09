# Joint height and damping control of the full Gaussian finite part

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Euler–FE conditional prime-discrepancy calculus.

## Target

Put `G_s(y)=ΣΛ(n)n^(−s)e^(−yn²)−∫₁∞v^(−s)e^(−yv²)dv`,
`B_s(y)=Σρ ½Γ((ρ−s)/2)y^(−(ρ−s)/2)`, and `A(s)=1/s+Γℝ′/Γℝ(s)`.
For each `σ₀,δ>0`, seek a constant `C` such that

`|G_s(y)+B_s(y)−e^(−y)(A(s)−ξ′/ξ(s))| ≤ C y(1+y)(1+log Im s)`

for `y>0`, `σ₀≤Re s≤1`, `Im s≥4`, and distance at least `δ` from every
actual zero. Both prime and zero sums must remain infinite and multiplicity-exact.
The resulting error divided by `1+log Im s` should converge uniformly to zero
as `y→0⁺`; absolute convergence holds along every such path with `y log Im s→0`.

The actual `¬AAL` finite exceptional layer supplies `1/2<σ<1` and `H>0`
such that this estimate and uniform limit hold throughout
`σ≤Re s≤1`, `Im s≥H`, while an actual zero remains strictly right of `σ`.

## Proof mechanism

Two incomplete-Mellin recursions bound each Gamma-subtracted germ error by
`(2y+2y²)/(|ρ−s||ρ−s+2|)`. Since `0<Re s≤1` and `0<Re ρ<1`,
`|ρ−s|≤3|ρ−s+2|`. The full squared-resolvent sum is `O_δ(1+log Im s)`:
split at ordinate distance one, use the local zero count on the near part,
and the proved full far-field inverse-square bound on the complement.
Combine this with the height-uniform archimedean error and the exact
Gaussian explicit formula.

Absolute admission of all complex-observation Gamma modes follows from two
Mellin recursions for the paired germs, square summability of the translated
resolvent, and the summable paired partial fractions. Thus subtraction of
the entire Gamma field is legitimate. For the `¬AAL` specialization, choose
`σ` between a finite-exception cutoff and one exceptional zero, then take `H`
above every exceptional ordinate. Horizontal and vertical separation give
the required fixed distance from every zero.

## Scope

This would control the full renormalized current jointly in both parameters.
It neither bounds the unsubtracted Gamma modes nor supplies height replication.
Formalization: `EulerFETransportTheory/TheFullGaussianCurrentAtEscapingHeights.lean`.
Lean verification is pending.
