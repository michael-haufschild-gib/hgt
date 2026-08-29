# Route-T exact Wold Borel terminal-height spectrum

- **ID:** `route-t-borel-terminal-width-spectrum`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** T / C5b
- **Statement:** For every `0 ≤ alpha < 1/2`, Xi zero width `alpha` is equivalent to decay of
  exact ordered Wold Borel terminal at every positive height `y < 1/2-alpha`.

## Goal

Identify exact geometric information carried by positive-Borel terminal heights, including
partial off-line progress and RH endpoint `alpha=0`.

## Corpus origin and full RH chain

`scripts/formal_tools.py research` exposed all route links except forward arbitrary-width
arithmetic transport and exact endpoint closure:

```text
XiZeroHalfPlaneBound alpha
  -> ChebyshevErrorPowerSpectrum alpha
  -> |theta(x)-x| = O_delta(x^(1/2+alpha+delta))
  -> centered weighted-Mertens decay x^(-(1/2-alpha-delta))
  -> natural Wold residual decay at same rate
  -> ordered Wold residual decay in prime-log height
  -> terminal decay for every 0<y<1/2-alpha.

terminal decay for every 0<y<1/2-alpha
  -> one-height Chebyshev width 1/2-y for cofinal y
  -> ChebyshevErrorPowerSpectrum alpha at exact endpoint
  -> XiZeroHalfPlaneBound alpha.
```

Endpoint recovery chooses terminal height as function of requested Chebyshev epsilon. No boundary
terminal decay at `y=1/2-alpha` is assumed. At `alpha=0`, theorem specializes to unconditional
RH classification.

## Formal result

- `WoldResidualBorelTerminalSpectrum alpha`
- `xiZeroHalfPlaneBound_iff_woldResidualBorelTerminalSpectrum`
- `riemannHypothesis_iff_woldResidualBorelTerminalSpectrum_zero`

Module:
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelTerminalWidthSpectrum.lean`.

## Novelty audit

`[SOTA, checked 2026-08-29]` Targeted primary-literature search found current work on
zero-free-region/PNT-error transfer (Broucke, arXiv:2507.13780), mean Mertens-error RH criteria
(Zhao, arXiv:2411.18903), and correlations of weighted prime-counting errors
(Bhattacharya--Martin--Simpson, arXiv:2507.13504). Searches for Wold/RH prime residuals and Borel
terminal/Mertens criteria returned no relevant source. No audited source states a Wold
prime-edge terminal-height spectrum or its exact complementarity with Xi zero width. Classical
von Koch, Abel summation, and prime-power correction are ingredients; exact Route-T composition
and terminal-spectrum invariant are new.

## Lean audit

- Direct `lake env lean`: passed.
- Single targeted `lake build`: passed (`12540/12540`).
- Umbrella: wired into `GaloisForLFunctions.RHTower`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.

## Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-29 — corpus-derived conjecture, paper chain, Lean proof, targeted audit completed.
