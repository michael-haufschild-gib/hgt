# Actual Epstein-to-Mayer Cauchy transform

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 2–4.

## Statement

For `Re w>2`, define the independently Poisson-constructed rectangular field
and normalized Cauchy kernel by

```text
E_w(a) = π^(w/2) Λ_a(w/2)/(2Γ(w/2)),
K_w(t) = [2Γ((w+2)/2)/(√π Γ((w+1)/2))]
         t(1+t²)^(-(w+2)/2).
```

For positive `a`, the convolution is absolutely convergent and

```text
K_w *_M E_w(a) = ζ(w)(1+a^(-w))+2C_w(a),
C_w(a) = Σ_{m,n≥1}(ma+n)^(-w).
```

On the actual disc segment `MayerScatteringPeriod.periodSegment`, the
right side is the actual scattering period `Φ_w(a)`. The input is the
independent Epstein field, not a function defined by this identity.

## Proof

For one quadratic lattice term, the increasing chart
`v=(at−b/t)/(a+b)` and the involution `t↦b/(at)` give

```text
(1+t²)(b²+a²t²)=t²[(at−b/t)²+(a+b)²],
1/(1+t²)+ab/(a²t²+b²) = (dv/dt)/(1+v²).
```

Even Cauchy integration therefore evaluates the single-term average as
`[√π Γ((w+1)/2)/(2Γ((w+2)/2))](a+b)^(-w)`.
Its norm integral is the real-parameter integral at `Re w`. The resulting
linear-lattice bounds are Barnes-summable, justifying the sum/integral
exchange and proving `K_w *_M Q_w=C_w`, where
`Q_w(a)=Σ_{m,n≥1}((ma)²+n²)^(-w/2)`.

The independent Epstein lattice series splits into two axes and four
quadrants, giving `E_w(a)=ζ(w)(1+a^(-w))+2Q_w(a)`.
The kernel's Mellin moments at zero and `w` are both one: even Cauchy
integration proves the first, and half-line inversion proves the second.
Thus convolution preserves both axes and yields the stated period.

## Lean certificates

All modules are in `RenormalizedIntersectionTheory`:

| Module | Main declarations |
|---|---|
| `GaussMayerQuadraticAveraging` | `quadraticIntegrand_integrable`, `quadratic_integral` |
| `GaussMayerQuadraticCone` | `summable_quadraticCone`, `cauchyKernel_convolution_integrable`, `cauchyKernel_convolution` |
| `GaussMayerEpsteinQuadrants` | `epsteinField_eq` |
| `GaussMayerCauchyMoments` | `cauchyKernel_mellin_zero`, `cauchyKernel_mellin_spectral` |
| `GaussMayerEpsteinPeriod` | `cauchyKernel_epstein_integrable`, `cauchyKernel_epstein_period` |

Final direct Lean checks and all 28 axiom audits passed. Dependencies use
only `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

The [continued transform](../1-in-progress/gauss-mayer-epstein-continuation.md)
requires further height bounds and holomorphic parameter integration.
No full eigenspace classification or Hermitian form follows here. For
nonreal `w`, the Cauchy kernel has a variable complex phase.
