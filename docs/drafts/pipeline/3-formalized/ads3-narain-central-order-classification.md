# Central vanishing orders of the averaged Narain transform

- **ID:** W11-NJ
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Exact mean regularization](ads3-narain-average-principal-part.md)

## Theorem

Put `c=2−4 Re ξ′(1)`, `Y*=exp(c)` and `κ=(logDeriv ξ)″(1)`.
Write `T_Y(u)=filledNumeratorMean Y u`, and take the removable value
at zero in `D_Y=T_Y/u`. For every positive height `Y`, `T_Y` is entire
and odd, while `D_Y` is entire and even. The physical Mellin variable
is `s=1/2+u`.

- `T′_Y(0)=√Y(c−log Y)`.
- `κ` is real and strictly negative.
- `T'''_(Y*)(0)=8√Y*(2−κ)≠0`.
- `ord₀ T_Y=1+2·1_{Y=Y*}` and `ord₀ D_Y=2·1_{Y=Y*}`.

For the actual averaged continuation `M_YZ`,

`M′_YZ(0)=4√(YZ)(c−log Y)(c−log Z)`,

`ord₀ M_YZ=1+2·1_{Y=Y*}+2·1_{Z=Y*}`.

Thus its central order is exactly one, three or five. It is simple
precisely when neither height is exceptional, and has order five
precisely when both are exceptional. No zero-free hypothesis is used.

## Proof

The xi functional equation exchanges the two terms of `T_Y` with a
minus sign. Differentiation at zero, together with `ξ(0)=ξ(1)=1/2` and
`ξ′(0)=−ξ′(1)`, gives the first jet. Schwarz symmetry makes `ξ′(1)` and
`κ` real. The unconditional strict concavity theorem for
`w↦Re(ξ′/ξ)(1/2+w)`, evaluated at `w=1/2`, gives `κ<0`.

The reflected expression
`T_Y(u)=√Y[G_Y(−u)−G_Y(u)]`, where
`G_Y(u)=(1−2u)exp(u log Y)ξ(1+2u)`, gives the cubic jet. At `Y*`,
its ordinary xi derivatives combine into `8√Y*(2−κ)`. Oddness kills
the second jet, so the exceptional order is exactly three. Dividing
by `u` gives the two possible orders of `D_Y`.

Near zero, the actual continuation factors as
`M_YZ(u)=u D_Y(u)D_Z(u)U(u)`, where
`U(u)=[2(1+2u)ξ(1+2u)(u−1/2)²]⁻¹` is analytic and `U(0)=4`.
Product differentiation gives the first averaged jet; additivity of
analytic vanishing orders gives the classification.

## Lean

Modules under `ArithmeticScatteringHolography/ModularBootstrap`:
`NarainCentralSymmetry`, `NarainCentralCurvature`, `NarainCentralLogJet`,
`NarainCentralCubicJet`, `NarainCentralExceptional`, `NarainCentralOrders`,
`NarainMeanCentralJet`, `NarainMeanCentralOrders`.

Endpoints: `analyticOrderAt_filledNumeratorMean_zero`,
`analyticOrderAt_dividedFilledNumeratorMean_zero`,
`narainMellinMean_deriv_zero`, `analyticOrderAt_narainMellinMean_zero`,
`narainMellinMean_central_simple_iff`,
`narainMellinMean_central_order_five_iff`.

Eight direct module checks and 21 endpoint axiom audits passed; dependencies
use only `propext`, `Classical.choice`, `Quot.sound`. Umbrella imports wired.

## Unproved refinement

The proposed local zero-height curve is
`log Y(u)=[log(1+2u)−log(1−2u)+log ξ(1−2u)−log ξ(1+2u)]/(2u)`,
with removable value `c` and proposed expansion
`log Y(u)=c+(4/3)(2−κ)u²+O(u⁴)`. This suggests real splitting for
`Y>Y*` and imaginary splitting for `Y<Y*`. Analytic extension, local
inversion in `u²`, and the complete local zero classification remain
unproved. These are target-numerator zeros; central cancellation does
not remove arithmetic resonance poles.

## Gates

- [x] 0 → 1: exact jets and unconditional curvature input audited.
- [x] 1 → 2: dependency-closed central classification.
- [x] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
