# The logarithmic causal kernel is a positive probability density

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The explicit causal kernel `v(x)=R exp(-bx)+∫₁∞ρ(t)exp(-tx)dt` for `x>0`, zero otherwise, is positive, continuous and decreasing on the positive half-line. Its Laplace transform is `κ(s)⁻¹` for every `s>0`, and `∫ℝv=1`.

## Proof

The bounded positive cut density gives an integrable exponential mixture at
each positive point. Integrating first in `x` gives `ρ(t)/(s+t)`;
the proved Stieltjes integrability therefore supplies joint integrability.
Fubini and the exact Stieltjes representation identify the Laplace transform.
As `s↓0`, the positive weighted kernels increase to `v`, and `κ(s)→1`.
Fatou proves integrability; monotone convergence fixes the total mass at one.
Local exponential domination proves continuity. Every exponential in the
positive mixture decreases, so `v` decreases.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicCausalKernelIsAPositiveProbabilityDensity.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `integrable_logarithmicLaplaceMixture`
- `logarithmicCausalKernel_laplace`
- `logarithmicCausalKernel_mass_one`
- `continuousOn_logarithmicCausalKernel`
- `antitoneOn_logarithmicCausalKernel`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
The normalized renewal mass and Green operator identity remain on the
[half-line kernel card](the-half-line-logarithmic-green-kernel.md).
