# Hedenmalm--Sonin Cartan/Weyl escape reconstruction

- **Label:** `P-G131`
- **Route:** P
- **Parents:** `P-G129`, `P-G130`, `RouteRHyperbolicGaugePolarReductionNoGo`
- **Status:** theorem proved in Lean; umbrella integration complete

## Conjecture tested

P-G130 retires regular holomorphic scalar cancellation because the required modulus has a cusp.
Test strongest survivor: the cusp is not intrinsic to pre-scalarized source data but arises by Weyl
reduction of two reciprocal holomorphic orientation legs,

```text
C(z)=(exp z, exp(-z)),
min(||C_+(x)||,||C_-(x)||)=exp(-|x|).
```

Then identify this construction with Burnol's literal forward/inverse Mellin characters and recover
P-G129 completed radial work from its lower gain.

## Scientific decision gate

- **Success:** reinterpret scalar Sonin escape as Weyl-chamber quotient of an actual holomorphic
  determinant-one source pair.  This retains orientation before scalarization and identifies exact
  remaining source law as neutral-Cartan saturation, not analytic scalar cancellation.
- **Failure:** rank-two survivor is only abstract; reject unless it lands on Burnol's literal
  characters and actual Xi source work coefficient-exactly.
- Constructing `(exp z,exp(-z))` alone counts as theatre.  Actual Burnol fibre equality and completed
  radial-work reconstruction are mandatory.

## Prior-research audit

- 2026-08-13 — Route-R hyperbolic gauge already carries reciprocal weights `(+1,-1)` and preserves
  split pairings, but no module identifies its complexification with actual Burnol Mellin
  characters or the Sonin escape cusp.
- 2026-08-13 — P-G129 proves local work is squared Sonin Lyapunov escape; P-G130 proves exact scalar
  analytic cancellation impossible.  These leave vector-valued orientation as strongest survivor.

## Conjecturing log

- 2026-08-13 — C1 proved in scratch: `C` is entire, determinant one, and restricts on the real axis
  to the literal Route-R gauge orbit of `(1,1)`.
- 2026-08-13 — C2 proved in scratch: lower Cartan gain is `exp(-|Re z|)`; Weyl reduction, and only
  that reduction, creates the nondifferentiable cusp.
- 2026-08-13 — C3 proved in scratch: Burnol orientation pair equals
  `C(log(r)*(w-1/2))`, is entire in `w`, and has determinant one.
- 2026-08-13 — C4 proved in scratch: on actual oriented Xi support its lower gain is
  `exp(-log(r)*lambda(q))`, and completed radial work is squared normalized negative log lower gain
  times literal completed first-divided Xi energy.

## Verification log

- 2026-08-13 — Direct foreground check passed:
  `lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmSoninCartanWeylEscapeReconstruction.lean`.
- 2026-08-13 — Imported by `GaloisForLFunctions/RHTower.lean`.
- 2026-08-13 — Exact module build passed:
  `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmSoninCartanWeylEscapeReconstruction`
  (`12958/12958`).
- 2026-08-13 — Axiom audit passed for every new theorem; dependencies are exactly `propext`,
  `Classical.choice`, and `Quot.sound`.

## Result and pivot

- Vector-valued survivor exists and is already present in Burnol's actual dilation characters.
  Scalar cusp is exact Weyl quotient of regular source data.
- This is not yet producer: determinant-one Cartan flow permits arbitrary off-wall rapidity.  New
  input must force **neutral Cartan saturation** (lower gain one) on actual co-Poisson annihilator
  fibres before Weyl reduction.  Search next for source pairing, determinant, or exterior-square
  law that fixes both product and sum/trace; determinant alone is identically one and powerless.
