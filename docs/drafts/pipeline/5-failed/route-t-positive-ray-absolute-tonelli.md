# Route T positive-ray absolute Tonelli

- **ID:** `T-C5b.1`
- **Stage:** 5-failed
- **Type:** NO-GO + POSITIVE SURVIVOR (Lean)
- **Source:** ../1-in-progress/route-t-required-residual-continuation.md · C5b.1
- **Failed claim:** The positive-normal Borel carrier can be reconstructed at critical half depth
  by sourcewise absolute Borel--Laplace Fubini under Route T's critical mesh energy.

## RH chain tested

```text
local source-marked Borel germ
  -> positive-ray atomwise absolute Fubini [DISPROVED HERE]
  -> upper-half residual reconstruction
  -> zero Stokes jump
  -> required residual regularity
  -> RH.
```

## Exact obstruction

For the positive real second-factorial kernel `Phi(r)=sum_k r^k/(k!)^2`, positivity and
monotonicity make every adjacent source difference have fixed sign at boundary point `x=0`.
For every `y>=0` and source `N`, Lean proves

```text
integral_0^infinity exp(-t)
  |R_N (Phi(h_N y t)-Phi(h_(N+1) y t))| dt
  = |R_N| exp(y h_N) (exp(y delta_N)-1).
```

The right side is exactly the norm of the upper-Hardy residual edge. Therefore, for `0<y<=1`,
summability of integrated absolute positive-ray Borel masses is equivalent to the corpus upper
residual variation at height `y`. At `y=1/2`, that variation and critical mesh energy cannot both
be summable. The proposed Tonelli passage is therefore incompatible with the rest of Route T.

## Positive survivor

`[LEAN-PROVED]` The exact integrated-mass identity and its summability iff are retained. They give
a sharp design constraint: C5b must sum lateral cancellations or a renormalized Wold/mesh
decomposition before source absolute values. Better raw majorants cannot repair this route.

## Formal certificate

Module:
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelUpperTonelliNoGo.lean`.

Principal declarations:

- `secondFactorialBorelRealKernel_mono`
- `integral_norm_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom_zero`
- `summable_integral_norm_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom_zero_iff`
- `not_summable_integral_norm_upperRaySourceLaplaceAtom_zero_and_criticalEnergy`

Direct `lake env lean` and targeted module build pass. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`. Module is wired into the RHTower umbrella; umbrella build was
not run.

## Consequence

Retire only the absolute-Tonelli subroute. C5b itself survives in the narrower form: construct a
source-faithful lateral or renormalized positive-normal continuation whose cancellation occurs
before absolute integration, then identify its Stokes jump with the forced Wold residue.

## Log

- 2026-08-29 — exact obstruction and positive survivor formalized; subroute retired
