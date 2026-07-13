# Integral jet quadratic incidence

- **ID:** `integral-jet-quadratic-incidence`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]`, `[FORMALIZATION]`, not new scientific knowledge
- **Lean:** `formal/GaloisForLFunctions/RHTower/IntegralJetQuadraticIncidence.lean`
- **Route:** `../../1-in-progress/quadratic-reflection-anomaly-rh.md`

## Statement

Constant-coefficient evaluation descends canonically from `Z[X]` to the integral local divisor-jet
ring `Z[X]/(X^m)` for `m >= 1`.  Squaring this integer defines

```text
Q_m(J) = coeff_0(J)^2.
```

For the source-defined completed symmetric Euler--Maclaurin contour boundary,

```text
Q_m(completedSEMContourBoundaryZ) = completedSEMContourIndexZ^2.
```

For every dominating SEM split this is both `zs.length^2` and
`analyticOrderAt(xi,rho).toNat^2`.

## Formal declarations

- `coeffZeroRingHomInt`
- `jetCoeffZeroRingHomInt`
- `integralJetQuadraticIndex`
- `integralJetQuadraticIndex_completedSEMContourBoundaryZ`
- `integralJetQuadraticIndex_eq_splitCount_sq`
- `integralJetQuadraticIndex_eq_xiOrder_sq`

## Scope

This closes the source-to-local-square bridge without reducing modulo a finite exponent.  It does
not distinguish a critical-line fixed zero from an off-line free reflection orbit: both have the
same positive local square.  Therefore the remaining RH-bearing object is necessarily a nonlocal
equivariant fixed-point subtraction with coherent finite-window assembly and a source-only
annihilation theorem.

The bridge is a routine consequence of the existing integral jet and contour-winding machinery;
it is not claimed as new scientific knowledge.
