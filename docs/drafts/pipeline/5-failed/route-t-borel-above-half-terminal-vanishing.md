# Route T: above-half Borel terminal vanishing

- **ID:** `route-t-borel-above-half-terminal-vanishing`
- **Stage:** 5-failed
- **Route:** T2, C5b.2
- **Status:** retired by unconditional Lean no-go

## Failed conjecture

Continue the source-marked Borel germ in a sector wider than the physical half strip, prove its
finite source cutoffs converge there, then restrict the resulting lateral sum to
`0<Im z<1/2`.

## Obstruction

Finite Borel Abel transport proves that the renormalized cutoff minus the integrated raw edge
cutoff is exactly

```text
R_N exp(-i h_N(x+i y)),
```

whose norm is `|R_N| exp(y h_N)`. If this tends to zero at any `y>1/2`, it yields an eventual
residual bound `|R_N| <= exp(-y h_N)`. Corpus sharp half-density theorem proves every such rate
impossible. Therefore a source-faithful wider-sector construction cannot have the required
terminal landing.

## Positive survivor

Strict sub-half strip is sharp maximal possible sector. Within it, finite Borel cutoffs land
exactly on finite `Wold - logMesh - holonomy` currents at `s=-y+i x`; only terminal-flux control
and lateral-limit identification remain. This survivor is formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelAbelRenormalization.lean`.

