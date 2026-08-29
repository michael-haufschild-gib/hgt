# Route-T positive-Borel terminal height controls Xi zero width

- **ID:** `route-t-borel-terminal-width-bound`
- **Stage:** 3-formalized
- **Route:** T / C5b
- **Status:** unconditional closed Lean theorem

## Corpus origin and full chain

Corpus research combined the new ordered-to-natural terminal transport with the existing
inverse-Abel and square-window zero-width machinery. For one fixed `0<c<1/2`, the conjecture was

```text
|R_k| exp(c h_k) -> 0
  -> every ordered/natural residual rate a<c
  -> theta and psi exponent 1-a
  -> Chebyshev source width 1/2-c
  -> XiZeroHalfPlaneBound (1/2-c).
```

For each source-spectrum epsilon, Lean chooses `a<c` close enough that `1-a` lies below
`1-c+epsilon`; no uniform endpoint constant is assumed.

## Formal theorem and consequence

Lean proves

```text
terminal decay at height c
  -> ChebyshevErrorPowerSpectrum (1/2-c)
  -> XiZeroHalfPlaneBound (1/2-c).
```

Thus positive-Borel height has exact geometric meaning: every gained terminal height removes the
same amount of admissible transverse Xi-zero width. The strict-sector RH classification is the
limit case `c -> 1/2`; a partial terminal estimate cannot be treated as analytically neutral.

This one-height implication is strengthened to an exact all-width equivalence in
`route-t-borel-terminal-width-spectrum.md`: decay at every strict height below
`1/2-alpha` is equivalent to `XiZeroHalfPlaneBound alpha`.

## Novelty audit

Primary-literature searches through 2026-08-29 found classical generalized von Koch bounds and
recent criteria for weighted Mertens error signs/correlations, but no Wold prime-edge Borel
terminal or theorem converting one terminal height into an explicit Xi zero half-plane width.

## Lean audit

- Module:
  `formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelTerminalWidthBound.lean`
- Direct `lake env lean` elaboration: passed.
- Single targeted `lake build` audit: passed (`12539/12539`).
- Umbrella: wired into `GaloisForLFunctions.RHTower`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
