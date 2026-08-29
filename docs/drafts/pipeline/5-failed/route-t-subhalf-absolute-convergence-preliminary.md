# Failed Route T subroute: strict-sub-half absolute convergence as preliminary input

Status: `RETIRED AS A SHORTCUT`

## Proposed shortcut

First prove absolute convergence of raw residual edges for every `0 < y < 1/2`, then use the
result to construct continuation and finally prove RH.

## Obstruction

Under critical prime-gap energy, that whole-strip absolute-convergence statement is itself
equivalent to RH. It cannot reduce proof burden before the RH step.

## Positive survivor

RH implies every strict half-power Wold residual rate, every strict-sub-half Borel terminal
vanishes, and raw/Abel-renormalized finite prescriptions asymptotically coincide. This gives the
sharp positive-sector necessity theorem and fixes the maximal sector boundary together with the
previous above-half no-go.

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelSubhalfClassification.lean`.

