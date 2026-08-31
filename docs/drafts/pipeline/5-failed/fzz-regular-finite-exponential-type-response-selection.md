# FZZ regular finite-exponential-type response selection

- **ID:** FZZ-P-FET-SELECTION-FAILED
- **Stage:** 5-failed
- **Type:** route-class no-go
- **Route:** FZZ-P regular type-normalized complex-order response selection

## Retired claim

Use entireness, the complete Schwarzschild response jet, and a global finite-exponential-type
condition to select the physical complex-order response and feed it into the FZZ Ward-orientation
chain toward RH.

## Exact obstruction

The canonical physical continuation is

`P(z) = regularizedRiemannZeta(z + 2)`.

Every Xi divisor point `rho` in the critical strip transfers to `rho - 2` with exactly the same
analytic multiplicity. Consequently

`xiZeroCount T ≤ divisorMass(P, closedBall(0,T+2))`.

Unconditional Riemann--von Mangoldt growth is of size `T log T`, while every nonzero entire
finite-exponential-type function has only linear divisor mass. Thus `P` has no finite exponential
type. Independently, entireness plus the full response jet never identifies a unique entire
continuation. The proposed regular finite-type selector therefore both fails to identify in the
ambient entire class and excludes the intended physical carrier from its restricted class.

Lean capstone:
`RHTower.fzz_regularFiniteTypePhysicalResponse_route_noGo`.

## Positive survivor

The obstruction exposes an exact categorical lower-growth law: any regular entire category that
contains the physical response must accommodate divisor mass at least `xiZeroCount T` in radius
`T+2`; in particular its admissible growth cannot have finite exponential type. The sharp surviving
regular scale is maximal order one, compatible with `exp(O(r log r))`, not `exp(O(r))`.

Paper proof and Lean theorem both retain all multiplicities and use neither RH nor zero simplicity.

## Remaining distinct branches

- maximal order-one response categories at the `r log r` scale;
- singular or non-entire complex-order responses;
- deformation of the physical source/category before response interpolation.

This card does not retire those branches.
