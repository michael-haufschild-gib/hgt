# Exact theta factorization and arithmetic spectrum of the Mayer core

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3.

## Target

Let `R(t)=(θ(t)−1−t^(−1/2))/2` for the actual Jacobi Gaussian count.
Let `F_w` be the actual Epstein field after subtracting its two zeta axes
and reciprocal scattering powers, as in the
[finite-energy core](gauss-mayer-finite-energy-scattering-core.md).
Then

```text
M R(u) = Γ_R(2u) ζ(2u),                 0<Re u<1/2,
F_w(a) = [2/Γ_R(w)] ∫₀∞ t^(w/2−1) R(t)R(a²t) dt,
M F_w(u) = Γ(u/2)Γ((w−u)/2)ζ(u)ζ(w−u)/Γ(w/2).
```

The core identity holds for `a>0`, `0<Re w<2`, `Im w>0`.
The last identity holds for `Im w>0`, `0<Re u<1`, and
`0<Re(w−u)<1`, equivalently
`max(0,Re w−1)<Re u<min(Re w,1)`.
All displayed Mellin integrals converge absolutely on these domains.

## Proof mechanism

Almost everywhere on positive heights,
`2R = modifiedEvenKernel − 1_(0,1) − t^(−1/2)1_(1,∞)`.
The modified kernel has an entire Mellin transform. The two explicit
power integrals recover completed zeta, including the cutoff correction
at `t=1`.

Put `P_a(t)=R(t)R(a²t)` and `f_a(t)=P_a(t)−1/4−1/(4at)`.
Theta inversion gives `P_a(1/t)=(t/a)P_(1/a)(t)`. Thus `f_a` forms a
weight-one functional-equation pair with root number `1/a` and both
constant terms `−1/4`. Its rapid decay beyond that constant follows from

```text
4(P_a−1/(4at)) = (θ(t)θ(a²t)−1) − (θ(t)−1) − (θ(a²t)−1)
                 − a⁻¹t⁻¹/²(θ(t)−1) − t⁻¹/²(θ(a²t)−1).
```

For `Re w>2`, `Im w>0`, the five source Mellins identify the pair's transform with
`Γ_R(w)F_w(a)/2`. Holomorphic continuation in the upper half-plane and
restoration of the explicit cutoff powers identify the actual correlation
integral on `0<Re w<2`. The Gamma normalization remains valid at zeta zeros.

Finally, the correlation is multiplicative convolution of `R` with
`t ↦ (t⁻¹)^(w/2)R(t⁻¹)`. The substitution `a ↦ a²` contributes `1/2`,
cancelling the core's prefactor `2`. The two ray transforms give the two
zeta factors, and the powers of π cancel to the stated Gamma quotient.

## Boundary

This identifies the actual canonical core's arithmetic Mellin spectrum.
Full Mayer eigenspace classification, the required Hermitian form, and
exclusion of off-line scattering resonances remain open.

## Lean certificate

All modules lie in `RenormalizedIntersectionTheory/`:

- `GaussMayerThetaRay.lean`: `MayerThetaRay.thetaRay_hasMellin_completed`
  and `thetaRay_hasMellin`.
- `GaussMayerThetaProduct.lean`: `MayerThetaProduct.productFEPair`
  and `thetaProduct_hasMellin`.
- `GaussMayerThetaCore.lean`: `MayerThetaCore.core_theta_hasMellin`
  and `core_theta_integral`.
- `GaussMayerCoreMellin.lean`: `MayerCoreMellin.core_hasMellin_gammaR`
  and `core_hasMellin`.

The direct production checks pass; all 15 audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.
