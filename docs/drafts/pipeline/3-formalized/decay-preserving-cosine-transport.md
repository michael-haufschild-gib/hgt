# Decay-preserving logarithmic transport of cosine transforms

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** Argon §4.1.
- **Parent:** [Finite aperture transport](../1-in-progress/odd-stabilizer-finite-aperture-transport.md).

## Statements

For a C⁴ window Ω supported in `[a,b]`, integrate the following moments over
`[a−1,b+1]`: `M₀=∫|Ω|`, `M₁=∫|tΩ|`, `D₄=∫|Ω⁽⁴⁾|`, and
`D₁=∫|(tΩ)⁽⁴⁾|`. Then

`Ωhat′(θ)=−∫tΩ(t)sin(θt)`,
`|Ωhat′(θ)|≤M₁`, and `|Ωhat′(θ)|≤D₁/|θ|⁴` for θ≠0.

For `0<x≤1`,

`|Ωhat(log(1+x))−Ωhat(x)|≤min(M₁x²,16D₁/x²)`.

For every T,m>0 and every finite positive even-frequency lattice,

`Σ_{r=1}^R |Ωhat(2r/m)|≤2m(M₀/T+T³D₄)`.

The mass bound has no additive window-height term. The phase bound preserves
decay away from the central Fourier lobe, removing the global Lipschitz loss.

## Proof

Differentiate under the compact integral. Apply fourth-order integration by
parts to `tΩ`. The logarithmic frequency belongs to `[x/2,x]`, and its shift
from x is at most x². The mean-value inequality therefore gives both phase
bounds. Combine zeroth and fourth moments with a reciprocal-square envelope.
The positive lattice telescopes:

`Σ_{n<R}(1+α(n+1))⁻²≤1/α`, α>0.

## Lean

`TransThresholdPairCorrelation/CosineTransformLogarithmicTransport.lean`:
`hasDerivAt_cosTransform`, `abs_deriv_cosTransform_le_fourth`,
`abs_deriv_cosTransform_le_mass`, `abs_cosTransform_log_sub_linear_le`,
`sum_inverse_square_affine_le`, `abs_cosTransform_le_mass`,
`sum_abs_cosTransform_even_lattice_le`.

All seven audits use only `propext`, `Classical.choice`, `Quot.sound`.
The final direct leaf check passes.

## Remaining gap

Literal stabilizer transport must retain the square-root pair weight, taper,
finite aperture and upper endpoint. Global model calibration and the actual
signed prime-minus-model estimate remain open.
