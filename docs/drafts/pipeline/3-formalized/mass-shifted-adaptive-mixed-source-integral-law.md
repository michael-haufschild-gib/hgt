# Mass-shifted adaptive mixed source integral law

- **ID:** `mass-shifted-adaptive-mixed-source-integral-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT ARITHMETIC SOURCE CAPITAL
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`

## Conjecture loop

1. Pointwise cofinal divergence of `y^2 J_n(y)` itself contradicts finite source capital.
   **False:** divergence may concentrate into arbitrarily narrow mass spikes.
2. Source integrability requires a separate continuity theory for varying orthogonal data.
   **False:** literal action is nonnegative derivative of negative cumulative flux. Mathlib
   derivative-integrability theorem supplies interval and improper integrability directly.
3. Finite interval accounting loses an unknown endpoint remainder at infinity. **False at fixed
   degree:** dimensionless flux has exact weight two and finite arcsine recession, hence actual
   cumulative flux tends to zero.

## Paper theorem

Let `J_n(sqrt y)` be literal drift-removed adaptive mixed/completed `P^sharp` source action formed
from current actual admission at physical mass `y`, and let `F_n(y)` be cumulative Jacobi flux.
Inside every positive chamber,

```text
F_n'(y) = -J_n(sqrt y),        J_n(sqrt y) > 0.
```

Therefore, with no added integrability premise,

```text
integral_[a,b] J_n(sqrt y) dy = F_n(a) - F_n(b),
abs (F_n(b) - F_n(a)) = integral_[a,b] J_n(sqrt y) dy.
```

Dimensionless flux obeys exact dilation

```text
F_dim(w,n) = w^2 F_n(w^2),
```

and fixed-degree dimensionless recession is finite, so `F_n(y) -> 0`. If one positive block
persists on `[a,infinity)`, then

```text
IntegrableOn (fun y => J_n(sqrt y)) (a,infinity),
integral_(a,infinity) J_n(sqrt y) dy = F_n(a).
```

This is exact fixed-degree source tightness and sharp integral Lipschitz equality for producer
itself—not orientation, observation, or fixed linear reporting.

## Honest residual

Fixed-degree source capital is now closed exactly. It does not sum over moving degrees. Along
intrinsic parabolic frontier staircase, unresolved quantities are entry flux `F_n(a_n)` and
degree-uniform width/rate of renormalized source spikes. Need diagonal boundary-flux summability,
anti-spike propagation for `y^2 J_n(y)`, or an exact inter-degree cancellation of tail budgets.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceIntegralLaw
```

Capstones:

- `integral_literalMassSourceAction_eq_flux_drop_of_posDef`;
- `abs_flux_drop_eq_literalMassSourceAction_integral`;
- `integral_literalMassSourceAction_lt_currentFlux_of_terminalChamber`;
- `dimensionlessCumulativeJacobiFlux_eq_square_mul_actual`;
- `tendsto_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_zero`;
- `integral_Ioi_literalMassSourceAction_eq_currentFlux`.

Direct `lake env lean` and targeted module build pass. Axiom audit of all ten public theorems
reports only `propext`, `Classical.choice`, and `Quot.sound`. Module is umbrella-wired. No
computation, RH premise, representing measure, fixed reporter, orientation map, reflection
aggregation, continuity assumption, integrability assumption, or added axiom is used.
