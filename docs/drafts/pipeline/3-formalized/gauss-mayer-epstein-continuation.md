# Continued Epstein-to-Mayer Cauchy transform

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 2–4.
- **Source chamber:** [quadratic averaging](gauss-mayer-quadratic-averaging.md).

## Statement

For `Re w>0`, `w≠2`, the independently Poisson-defined rectangular field
and normalized Cauchy kernel satisfy

```text
E_w(y) = π^(w/2) Λ_y(w/2)/(2Γ(w/2)),
K_w(t) = [2Γ((w+2)/2)/(√π Γ((w+1)/2))]
         t(1+t²)^(-(w+2)/2),
K_w *_M E_w(a) = Φ_w(a).
```

The actual integral converges absolutely and is holomorphic in `w` for
every `a>0`. The equality with the actual Mayer scattering period holds
on its disc segment `a∈[1/2,7/2]`, including at `w=1`.

## Proof

The independent weak functional-equation pair gives the actual heat expansion

```text
Λ_y(w/2) = ∫₁∞ t^(w/2−1)(θ_y(t)−1) dt
         + y^(-1)∫₁∞ t^(−w/2)(θ_(1/y)(t)−1) dt
         − 2/w + 2/(y(w−2)).
```

Gaussian monotonicity, Poisson duality, and scalar theta Mellin integrability
bound the field locally uniformly by `C y^(1−η)` for `y≥1`, with `0<η<1`.
Height reciprocity `E_w(y)=y^(−w)E_w(1/y)` and the two Cauchy norm bounds
`1` and `t^(−Re w−2)` give, after splitting at `t=a`,

```text
|q_w(t)E_w(a/t)| ≤ C a^(1−η)t^(−1+η)             (t≤a),
|q_w(t)E_w(a/t)| ≤ C a^(−Re w−1+η)t^(−1−η)      (t≥a).
```

The spectral exponents cancel exactly at infinity. The remaining height
coefficient is locally bounded, so these powers give an integrable uniform
majorant. Measurability follows from the actual Gaussian tails. Dominated
holomorphic integration and the identity theorem on the punctured
half-plane extend the certified source-chamber equality. The Gamma
normalization is holomorphic and nonzero throughout that domain.

## Lean certificates

All modules are in `RenormalizedIntersectionTheory`:

| Module | Main declarations |
|---|---|
| `GaussMayerEpsteinReciprocity` | `reciprocity`, `differentiableAt_epsteinField` |
| `GaussMayerEpsteinHeatBounds` | `originalHeatWeight_integral_le`, `dualHeatWeight_integral_le` |
| `GaussMayerEpsteinHeatRepresentation` | `epsteinLambda_heat_expansion`, `norm_epsteinField_le` |
| `GaussMayerEpsteinHeightGrowth` | `locally_uniform_height_growth` |
| `GaussMayerEpsteinHeightMeasurability` | `measurable_epsteinField` |
| `GaussMayerEpsteinEndpointBounds` | `small_endpoint`, `large_endpoint`, `averagingFactor_ne_zero_halfPlane` |
| `GaussMayerEpsteinIntegral` | `average_integrable`, `differentiableAt_average` |
| `GaussMayerEpsteinContinuation` | `average_eq_period`, `cauchyKernel_epstein_integrable`, `differentiableAt_convolution`, `cauchyKernel_epstein_period` |

Direct Lean checks passed. Audited transitive dependencies use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

This identifies the canonical Mayer period with an actual independently
continued Epstein integral. It does not classify every eigenspace,
construct the full Hermitian form, or exclude off-line scattering poles.
For nonreal `w`, the kernel retains a variable complex phase.
