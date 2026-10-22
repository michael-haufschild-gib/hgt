# Chiral nodal determinant center-curvature law

- **ID:** `ccm-chiral-nodal-determinant-center-curvature`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** matched oriented characteristic cocycle × chiral nodal source shear × wall-light jets × determinant curvature
- **Lean module:** `GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseProjectiveGaugeNodalCenterCurvature`
- **Statement:** Every actual prime-power nodal source-shear determinant has a double spectral-center zero and strictly negative second derivative; every nonempty finite direct sum inherits the same strict curvature and a local nonpositive determinant chamber.

## Goal

Supply a premise-free chamber seed for the operator-derived determinant line. Prior source-shear
work read signed source orientation at each frequency but did not choose either side of the nodal
wall. This theorem forces the center side from actual prime-polar geometry, without Xi divisors,
zero placement, Weil positivity, or RH.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module, direct check, exact leaf build, axiom audit
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## The law `[LEAN-PROVED]`

For one matched atom, define

```text
C_n(x) = ∫_0^rho A cosh(r/2) (2 - 2 cos(2πrx)) dr,
P_n(x) = ∫_0^rho 2 A sinh(r/2) sin(2πrx) dr,
S_n(x) = cos(2π log(n)x) C_n(x) + sin(2π log(n)x) P_n(x).
```

The chiral nodal source-shear determinant at unit shear is

```text
D_n(x) = -2 gauge(n)^2 S_n(x).
```

Lean proves

```text
D_n(0) = 0,
D_n'(0) = 0,
D_n''(0) = -2 gauge(n)^2 K_n,

K_n = Q_n + 4π log(n) M_n,
Q_n = ∫_0^rho 8π² r² A cosh(r/2) dr,
M_n = ∫_0^rho 4π r A sinh(r/2) dr.
```

For every actual prime-power label, mass matching gives `rho > 0`, hence `Q_n > 0`; the
oriented characteristic theorem gives `M_n > 0`; prime-power arithmetic gives `log n > 0`; and
projective gauge is nonzero. Therefore `K_n > 0` and `D_n''(0) < 0`.

For any nonempty finite packet of labeled prime powers, the direct-sum determinant response has
curvature equal to the sum of these strictly negative atom curvatures. Its center is a local
maximum with value zero, so the determinant is locally nonpositive.

## Main Lean declarations

- `ccmActualHeadMatchedCosinePhaseFirstJet`
- `ccmActualHeadMatchedCosinePhaseSecondJet`
- `ccmActualHeadMatchedCosinePhaseQuadraticMoment`
- `hasDerivAt_ccmActualHeadMatchedCosinePhaseProfile`
- `hasDerivAt_ccmActualHeadMatchedCosinePhaseFirstJet`
- `ccmActualHeadMatchedCosinePhaseQuadraticMoment_pos_of_weight_pos`
- `ccmActualHeadMatchedOrientedPhaseSymbolRealFirstJet`
- `ccmActualHeadMatchedNodalSourceFrequencyCurvature`
- `deriv_deriv_ccmActualHeadMatchedOrientedPhaseSymbol_re_zero`
- `ccmActualHeadMatchedNodalSourceFrequencyCurvature_primePower_pos`
- `deriv_deriv_det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_zero`
- `ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingCurvature_primePower_neg`
- `ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_primePower_isLocalMax_zero`
- `eventually_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_primePower_det_nonpos`
- `deriv_deriv_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse_zero`
- `ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerCurvature_neg`
- `ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFinitePrimePowerResponse_isLocalMax_zero`

## New scientific knowledge

Positive Fock geometry preserves source magnitude but loses ordering; the chiral exterior
extension restores orientation; source shear reads that orientation as spectral flow. This module
adds a fourth layer: reflection-center parity transmutates the signed spectral-flow function into a
strictly signed curvature. The preferred determinant chamber therefore exists before any global
RH-bearing sign theorem.

The exact coefficient has two independent positive channels:

1. intrinsic polar spread `Q_n` from the even characteristic component;
2. anchor–orientation interference `4π log(n) M_n` from the odd component.

Neither channel alone describes the determinant curvature. Their forced sum is the source-native
Frankenstein mechanism.

## Frontier effect

Remaining obstruction is no longer local chamber selection. It is global propagation and counting
of later determinant crossings away from the reflection center. This is the correct interface for
the corpus Krein crossing, quantized Stokes, and distributional source-reconstruction mechanisms.
No global propagation, absence of later crossings, or RH is claimed here.

## Verification

- scratch: `lake env lean /tmp/CCMNodalCenter.lean` — PASS
- direct source check: `lake env lean GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedPhaseProjectiveGaugeNodalCenterCurvature.lean` — PASS
- exact leaf build: `lake build GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseProjectiveGaugeNodalCenterCurvature` — PASS
- axiom audit: only `[propext, Classical.choice, Quot.sound]`
- umbrella import added to `GaloisForLFunctions.RHTower`
- global `formal_tools.py lint`: new module clean; command remains red only because ten unrelated pre-existing Connes/Chen modules are unreachable from `RHTower`
- no umbrella/full build run

## Log

- 2026-08-21 — broad search across CCM, Route-L reconstruction, Hilbert curvature, quantum metric, Stokes, exterior source, and failed-route obstruction corpus.
- 2026-08-21 — conjecture C1 passed symbolic scratch proof; atom and finite-packet laws formalized.
- 2026-08-21 — direct check, exact leaf build, and axiom audit passed; promoted to stage 3.
