# Theta C5 adaptive residual reserve

- **ID:** CLG-TTF-C5-adaptive-residual-reserve
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** adaptive-reserved seam no-go and exact completed likelihood lift

## Exact statement

Define the omitted third-channel residual

```text
R(u,t) = 5 t^2 [a (n-Z) - c s],
```

where `a` is completed first displacement jet, `n` is exact second mixed likelihood jet, `Z` is
adaptive master curvature, `c` is third likelihood displacement jet, and `s` is completed
centre-action jet. Then, identically,

```text
full completed compensation = adaptive reserved compensation + R.
```

On the structural physical tail `0<t<u`, `A(u)>=6`, one has `R>0`. Consequently full compensation
is positive exactly when

```text
adaptive reserved compensation > -R.
```

## Dependency-closed proof

Expanding full and lower velocity-slope numerators cancels every atom and lower likelihood channel:

```text
P_full-P_lower = t^2 (a n-c s).
```

The adaptive margin restores `5t^2 aZ`, so subtraction gives the displayed identity by ring
algebra.

For positivity, source theorems give `a>0`, `s>0`, `c<0`, and strict adaptive cooling `Z<n`.
Therefore both `a(n-Z)` and `-cs` are positive. Multiplication by `5t^2>0` proves `R>0`.
Rearranging the exact identity gives the equivalence.

## Research consequence

This is positive salvage from the adaptive-reserve no-go. Global positivity of the adaptive margin
is false and unnecessarily strong. Exact remaining direct-C5 condition is residual-aware domination
`adaptive > -R`; the source supplies a strictly positive cancellation channel which cannot be
discarded before taking the seam limit.

No numerical value or sampled sign occurs in proof.

## Gates

- [x] dependency-closed paper proof
- [x] Lean formalization and axiom audit
- [x] frontier integration

Lean module:
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5AdaptiveResidualReserve`.
Direct Lean and exact target build pass. Main theorem axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.
