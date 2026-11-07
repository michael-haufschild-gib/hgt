# Arithmetic Auxiliary Dynamics programme

- **ID:** AAD
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0611/obstacles-summary.md, the field section "If positivity, Weil positivity and spectral methods are excluded"
- **Statement:** how the rational integers force zeros of ζ by construction and transport, with no sign.

## Goal
Develop the field: objects, tools, answers to its questions. Lean folder `formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/`, umbrella `ArithmeticAuxiliaryDynamics.lean`, foundational document `ArithmeticAuxiliaryDynamics/README.md`.

## Status
All results below are Lean theorems, unconditional. Paper targets are closed.

- Scale: floor `c₁/(√K (1+log K))` (`exists_half_floor`); `K^{-a}` reads `Re ρ ≤ 1−a`; rates for all `a<1/2` give RH; `a>1/2` impossible. Peak law `w ≤ 100 (1+log K)² (K T + m)`.
- Construction: VK rate on polynomial alphabets (`hasRate_vk`); RH gives every `a<1/5`, strip `Θ` gives `a<(1−Θ)/(3−Θ)` (`hasRate_of_zeroFree_sharp`); polynomial rate ⇔ strip.
- Exact LP duality, extremal fake prime measure and its distance from the pronic one (`exists_extremal_bracket`).
- Parity: factor 2 is one Hecke factor; parity neutral producers at the Mertens level (`hasParityNeutralRate_vk`, `exists_hasParityNeutralRate_rpow_iff`).
- Curves: linear stencil window is `|a| ≤ q+1`; purity is the upper bound for curve and twist (`isPure_iff_upper_bound`).
- Ledger ladder: order law for all analytic `f`, generating function, twin gap.
- Transport: phase returns exist; a bounded one at a zero gives infinitely many zeros; one at each zero gives AAL (`asymptoticAbscissaLaw_of_boundedReturns`).
- Tools: multiplicity and zero estimates on the gauge torus, Siegel with parity, effective Kronecker, Hurwitz limit set in the torus, transport count, return exponent.

## Open core
Certificate of a rate not through `M(x)`; exponent under RH in `[1/5, 1/2]`; parity through the primes; arithmetic input for a nonlinear ledger (RigidArithmeticOfCuts); bounded phase returns at a zero; Stepanov's twist over `ℤ`; explicit extremal measure.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven (programme stays open on the core above)
- [ ] 2 → 3  formalized
