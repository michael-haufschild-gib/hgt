# Actual distant-pair comparison under width changes

## Target

For actual continuous profiles `f,g` supported in `[0,w]` and `s>w`, prove

```
abs(atomCrossTerm(f,s)-atomCrossTerm(g,s))
  <= archLevyDensity(s-w)*L1(f-g)*(L1(f)+L1(g)).
```

The proposed transfer to fixed smooth-profile dilations is a normalized bound
`C_phi*(w-v)*(1/s+1)` when `0<v<=w<=3v/2` and `w<=3s/4`. For integer pairs at
distance at least two, `v=1/N` and `w=c/N`, `c<=3/2`, this would be a small
multiple of the reciprocal-log-gap row. Existing top-mass payment then turns
the whole distant-pair change into `C_phi*(c-1)*(D_N+mass)`.

## Mechanism

The actual autocorrelation difference has absolute integral at most
`L1(f-g)*(L1(f)+L1(g))`. Fubini is justified by the integrable envelope
`(|f|+|g|)(u)*(|f|+|g|)(u+z)`. The separated shifted cross integral has bounded
density `archLevyDensity(s-w)` on its entire support. Actual smooth dilation
supplies the small absolute-mass difference; no cancellation estimate is
assumed.

## Inputs and status

Searches188-191,196-197; actual SSHA pairing source and the existing scalar
density bound were read. The displayed corpus leads contain generic
convolution integrability but no matching source comparison. Formalization
is in progress. Genuine adjacent overlap still uses the cancelled mixed Robin
calculus, not this separated estimate.
