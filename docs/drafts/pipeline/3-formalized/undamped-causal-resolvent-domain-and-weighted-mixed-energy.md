# Undamped resolvent admission and exact weighted mixed energy

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** B104; actual boundary-resolvent tests.
- **Status:** All three modules passed Lean; imports wired.

Write `C_{a,b}f` for convolution with `π exp(-(πa+2πib)t) 1_{t>0}`,
and `W_x f(u)=exp(-πxu)f(u)`. Here Γ denotes `EF.gammaBracket`.

## Statements

1. If f is measurable, vanishes on `[0,∞)`, `W_{4/π}f∈L²`, and its Laplace
   value at `2πib` is zero, then `C_{0,b}f∈L¹∩L²`.
2. If `W_xf∈L²` and `a+x>0`, the real mixed integrand is integrable and
   `∫ Re(conj(W_xf) W_x(C_{a,b}f)) = (a+x) ∫ |W_x(C_{a,b}f)|²`.
   This includes the undamped case `a=0`, `x>0`.
3. If H is continuous and `(1+|r|)|H(r)|≤M` for every real r, then
   `|H(r)|² Γ(r)` is integrable.

## Proof mechanisms

A zero Laplace coefficient removes the positive resolvent tail. On the
negative half-line the exponential weight dominates the ordinary square
norm; the verified half-pole admission law at zero then gives L¹.

Expanding the exact reflection norm identity gives the resolvent mixed
term. Modulation preserves it, and exponential weighting shifts the rate
from a to `a+x`. For Gamma admission, the square-root Gamma bound supplies
an integrable `(1+|r|)^(-3/2)` majorant.

## Lean

All modules lie in `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/`.

- `UndampedCausalResolventBasicDomain`: `undampedCausalConvolution_memLp_and_integrable`.
- `CausalResolventMixedEnergy`: `integral_weighted_modulatedCausalConvolution_mixed_energy`.
- `GammaIntegrabilityFromLinearFourierDecay`: `integrable_gammaEnergy_of_linear_decay`.

Imaginary-axis nonvanishing remains conjectural. It still needs the neutral
moment law, actual resolvent Fourier decay, and symmetric arithmetic
mixed-term cancellations.
