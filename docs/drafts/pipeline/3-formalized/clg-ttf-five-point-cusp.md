# Actual theta five-point coalesced cusp

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every critical aperture `0<a<1/2`, there exists `δ>0` such that the actual center-mixed theta Gram matrix on `0,h,2h,3h,4h` is positive definite whenever `0<|h|<δ`.
- **Capstone:** `RHTower.exists_thetaCuspCenterMixedGramFiveEquispaced_posDef_punctured` in `ThetaCuspCenterMixedFivePointCusp`.

## Dependency-closed proof

Write `Jk` for the literal kth center derivative at zero. Use central finite-difference coordinates of orders `0,1,2,3,4`. The even coordinates have orders `0,2,4`; the odd coordinates have orders `1,3`. Every nonzero spacing gives an invertible coordinate map. An exact quadratic-form identity identifies the original sample matrix with its normalized form.

Taylor's theorem and exact stencil moments show that the normalized entries converge to

```text
[J0,    0, J2,    0, J4]
[ 0,  -J2,  0,  -J4,  0]
[J2,    0, J4,    0, J6]
[ 0,  -J4,  0,  -J6,  0]
[J4,    0, J6,    0, J8].
```

The four even stencils have coefficients `(-2,2,0,0,0)`, `(6,-8,2,0,0)`, `(-20,30,-12,2,0)`, and `(70,-112,56,-16,2)` on the samples `f(0),...,f(4h)`, divided by `h²,h⁴,h⁶,h⁸`. The three odd-block stencils have coefficients `(1/2,0,-1/2,0,0)`, `(-1,1/2,1,-1/2,0)`, and `(5/2,-2,-2,2,-1/2)`, divided by `h²,h⁴,h⁶`. Odd center jets vanish by source evenness. All required lower stencil moments vanish exactly, and the leading moments identify the displayed derivatives. No order-twelve smoothness or determinant Taylor expansion is needed.

The source supplies `J0>0` and `J2<0`. Existing strict fourth and second--sixth Hankel laws supply `J0*J4−J2²>0` and `J2*J6−J4²>0`. The new literal rank-three mixture supplies the even three-by-three determinant. Completion of squares makes both limiting parity blocks positive definite. The corpus's entrywise matrix-limit theorem then makes the normalized sample form positive definite near zero. Exact congruence returns positivity to the literal sample matrix.

`FivePointFiniteDifferenceCusp` proves the generic C8 result. `ThetaCuspCenterMixedFivePointCusp` discharges every source and regularity input using the actual density, including the existing shared seventh/eighth jet chain.

## RH scope

Global native D1, actual rank-three center mixing, and the equispaced five-point cusp are closed. This theorem concerns a punctured local chamber for five equispaced samples. General configurations, higher packet ranks, theta-specific source-to-divisor incidence, and cofinal no-escape remain before all-packet Weil positivity and RH.

## Verification

- Scratch and production checks passed with `lake env lean` for both new modules. Only their needed oleans were produced.
- The new physical capstone uses only `propext`, `Classical.choice`, and `Quot.sound`; no numerical certificate or added axiom is used.
- New modules are imported by their area umbrellas. No umbrella or full build was run.
- Duplicate seventh/eighth jet declarations in the preceding mixture module were removed in favor of the existing four-point source chain; that affected module passed a direct recheck.
- Public declaration-name scan found no remaining duplicate names outside the six new modules.
- Formal lint passed and corpus indexes were refreshed after the final module changes.
