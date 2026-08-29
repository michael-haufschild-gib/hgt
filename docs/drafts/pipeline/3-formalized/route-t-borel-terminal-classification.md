# Route-T positive-Borel terminal classification

- **ID:** `route-t-borel-terminal-classification`
- **Stage:** 3-formalized
- **Route:** T / C5b
- **Status:** unconditional closed Lean theorem, parameterized by already-isolated critical mesh
  energy in its RH equivalence

> Superseded on 2026-08-29 by
> `route-t-borel-terminal-unconditional-classification`, which removes the critical mesh-energy
> premise through ordered-to-natural Wold interpolation.

## Corpus origin and RH chain

Corpus research combined four existing results:

1. finite Borel Abel transport identifies the raw/renormalized difference exactly as
   `R_N exp(-i h_N(x+i y))`;
2. RH gives every strict half-rate bound for the centered ordered Wold residual;
3. an eventual residual rate `c` makes raw residual edges absolutely summable at each `a<c`;
4. cofinal raw-edge absolute convergence below `1/2`, plus critical mesh energy, forces RH by
   analytic ODE uniqueness.

This gave the conjecture and complete chain

```text
terminal decay at every strict y
  -> choose a < c < 1/2
  -> |R_N| exp(c h_N) -> 0
  -> eventually |R_N| <= exp(-c h_N)
  -> absolute raw-edge convergence at i a
  -> cofinal source-strip analyticity
  -> Route-T ODE uniqueness + critical mesh energy
  -> RH.
```

The reverse implication follows from the corpus RH-to-Wold strict half-rate theorem.

## Formal theorem

Under `Summable xiHeatCassiniPrimeGapCriticalEnergy`, Lean proves both

```text
RH iff forall 0 < y < 1/2, |R_N| exp(y h_N) -> 0
```

and its literal finite-current form

```text
RH iff forall x and 0 < y < 1/2,
  finiteRenormalizedCurrent_N(x,y) - finiteRawEdgeIntegral_N(x,y) -> 0.
```

The second statement uses the actual positive-ray Borel integral and finite
Wold–mesh–holonomy current, not an auxiliary coefficient model.

## New knowledge and route consequence

Separate removal of positive-ray terminal flux over the whole strict sub-half sector is not a
preparatory analytic estimate: it is exactly RH-strength once the independent mesh-energy channel
is present. This retires the terminal-first lateral plan. Any noncircular survivor must identify
or regularize terminal plus edge current jointly, retaining possible Stokes charge until final
landing.

Primary-literature searches through 2026-08-29 found classical RH bounds and sign/correlation
criteria for Mertens errors, but no prime-edge Wold Borel carrier, finite Abel terminal, or this
terminal/finite-current RH classification.

## Lean audit

- Module:
  `formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelTerminalClassification.lean`
- Direct `lake env lean` elaboration: passed.
- Single targeted `lake build` audit: passed.
- Umbrella: wired into `GaloisForLFunctions.RHTower`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Formal lint: no new banned construct or reachability error; unrelated existing umbrella debt
  remains elsewhere.
