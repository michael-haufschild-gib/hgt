# Cesàro power-schedule no-go

- **ID:** cesaro-power-schedule-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `squarefree-convolution-half-cesaro-source-criterion.md`
- **Status:** `[PROVED HERE] [LEAN-PROVED] [NOT RH]`

## Statement

At real `sigma>1/2`, canonical convolution-half partial sums admit no bound `O(N^alpha)` when
`0≤alpha<1-sigma`. Consequently, at `sigma=6/11`, no scheduled Cesàro family is locally bounded if
its certified pole amplification dominates `N^rho` for some `6/11<rho≤1`.

## Proof

A partial-sum bound with exponent `alpha<1-sigma` and polynomial Abel summation continue the
coefficient half into a half-plane containing `s=1`. Squaring on the Euler chamber and analytic
uniqueness force the zeta residue unit at one to vanish, contradiction.

For Cesàro means, amplification `N^rho` would give `C_N=O(N^{-rho})`. Exact discrete
differentiation gives raw partial sums `D_N=O(N^{1-rho})`. If `rho>6/11`, then
`1-rho<5/11=1-6/11`, contradicting the first theorem.

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroPowerScheduleNoGo.lean`.

Verification on 2026-09-04: direct check pass; targeted build `13049/13049`; principal axiom audits
only `propext`, `Classical.choice`, `Quot.sound`; umbrella import wired.

## Positive survivor

Every live schedule must avoid all certified power exponents strictly above `6/11`. The canonical
iterated-log schedule does. Exact endpoint `rho=6/11` and subcritical schedules remain outside this
argument.
