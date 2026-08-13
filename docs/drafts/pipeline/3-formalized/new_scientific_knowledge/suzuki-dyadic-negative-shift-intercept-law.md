# Suzuki dyadic negative-shift intercept law

- **ID:** `suzuki-dyadic-negative-shift-intercept-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SOURCE-ASYMPTOTIC CONSUMER
- **Scientific status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOT RH]`
- **Paper parent:**
  `./suzuki/suzuki-neumann-dominated-shift-cone-obstruction.md`
- **RH used:** no
- **Computation used:** no

## Exact theorem

For real normalized source edge jet `q(lambda)` with finite limit `ell` as
`lambda -> -infinity`, define affine zero-intercept

```text
Phi(alpha,beta)
  =(beta*q(alpha)-alpha*q(beta))/(beta-alpha).
```

On dyadic negative shifts `alpha=-2L`, `beta=-L`, `L != 0`, exact algebra gives

```text
Phi(-2L,-L)=2*q(-L)-q(-2L).
```

Both arguments tend to `-infinity`, hence

```text
Phi(-2L,-L) -> ell,  L -> +infinity.
```

If `ell=0`, strict corpus theorem

```text
Re (XiC''(0)/XiC(0)) < 0
```

implies every sufficiently large dyadic intercept is strictly above Xi curvature.  Such pairs
therefore fail necessary central residue condition for normalized scalar Herglotz quotient.

## Lean

Module:
`formal/GaloisForLFunctions/RHTower/SuzukiLargeNegativeShiftCentralFlux.lean`.

Declarations:

```text
suzukiRealAffineZeroIntercept_neg_two_neg_one
tendsto_suzukiDyadicNegativeShiftIntercept_atTop
eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept
eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept_of_tendsto_zero
```

## Honest boundary

Lean proves exact affine/asymptotic consumer.  Paper parent separately derives actual source limit

```text
q_norm,lambda^EG -> (2a)^(-1) integral_0^(2a) g(t)dt
```

from Suzuki's restricted resolvent and distributional endpoint source.  That concrete operator
instantiation is not yet represented in Lean.  No theorem here assumes or concludes RH.

## Positive survivor

Auxiliary shifts are not harmless gauges.  Any scalar jump proof must construct a source-selected
pair outside Neumann-dominated negative escape cone, then prove central threshold and full Pick
kernel for that selected pair.

## Gates

- [x] exact dyadic affine identity
- [x] limit transfer from `atBot` to `atTop`
- [x] strict Xi-curvature eventual obstruction
- [x] direct Lean check
- [ ] formalize concrete Suzuki restricted-resolvent edge limit
- [ ] construct nonescaping source-selected shifts
- [ ] RH
