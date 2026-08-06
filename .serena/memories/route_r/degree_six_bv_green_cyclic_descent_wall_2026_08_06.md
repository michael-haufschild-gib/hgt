# Route R degree-six BV--Green cyclic descent wall (2026-08-06)

Formalized in `formal/GaloisForLFunctions/RHTower/RouteRDegreeSixBVGreenPhysicalCyclicDescentWall.lean`, imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Unconditional source result
For diagonal coefficient `d_k(T)=(T e_k)_k`, the explicit reader
`tau_6=(5/6)d_1+d_6` satisfies:
- `tau_6(Q)=1`;
- `tau_6(S_6^* Q S_6)=1/6`;
- `tau_6(Q S_6 S_6^*)=1/6`;
- hence `tau_6(B_6)=0` for the literal degree-six Hochschild boundary `B_6=[S_6^*,QS_6]`.
Every linear reader cyclic on that exact pair kills `B_6`.

## Exact classifier
`RouteRDegreeSixBVGreenPhysicalCyclicDescent rho` means existence of a normalized pair-cyclic source reader whose boundary value equals Route R's fixed reflected physical marginal. Lean proves:
- physical cyclic descent iff fixed reflected boundary is zero;
- iff `Re rho=1/2`;
- iff the explicit Hodge-mate coefficient is zero;
- globally iff `RiemannHypothesis`.

Thus source Hochschild presentation, cyclic reader, normalization, and source annihilation are closed. Missing producer is only coefficient-faithful equality between source cyclic quotient and fixed same-fibre physical marginal. This is RH-equivalent and cannot be supplied by definition or generic cyclicity.

## Conjectures falsified
Ordinary/singular trace, twisted/KMS cyclicity, paired Gamma orientations, resolved Hellinger absorption, composite 6=2*3 curvature, integral Cartier lattice, linear mixed-dagger exactness, and completion/Hodge without independent co-closedness. Details in `docs/drafts/pipeline/1-in-progress/route-r-degree-six-bv-green-physical-cyclic-producer.md`.

## Verification
- `lake env lean GaloisForLFunctions/RHTower/RouteRDegreeSixBVGreenPhysicalCyclicDescentWall.lean`: pass.
- targeted `lake build`: pass.
- capstones use only `[propext, Classical.choice, Quot.sound]`.
- no forbidden declarations.
- repo lint only failed on unrelated concurrent unwired modules; new module is wired.
