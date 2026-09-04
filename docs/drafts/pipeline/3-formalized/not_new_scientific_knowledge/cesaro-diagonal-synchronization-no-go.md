# Cesàro diagonal synchronization no-go

- **ID:** cesaro-diagonal-synchronization-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `squarefree-convolution-half-cesaro-source-criterion.md`
- **Status:** `[PROVED HERE] [LEAN-PROVED] [NOT RH]`

## Statement

The canonical Cesàro-smoothed convolution-half sequence cannot be locally bounded after coupling
arithmetic cutoff `N` to Cayley pole-factor degree `N`.

## Proof

Write `D_N` for the raw convolution-half Dirichlet polynomial and
`C_N=N⁻¹∑_{M<N}D_M` for its Cesàro average. Exact finite algebra gives

\[
  D_N=(N+1)C_{N+1}-NC_N.
\]

At `boundaryExteriorPoint=6/11`, the degree-`N` pole factor has norm at least `5^(N-24)` for
`N≥24`. If the pole-cleared product were locally bounded, then

\[
  5^{N-24}|C_N|\le K.
\]

Since `N≤24·5^(N-24)`, both `N|C_N|` and `(N+1)|C_{N+1}|` would be bounded by `24K`. The discrete
derivative identity would make every raw `D_N(6/11)` eventually bounded, contradicting
`not_eventually_bounded_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint`. `[PROVED HERE]`

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroDiagonalNoGo.lean`.

Main theorems:

- `natCast_mul_squarefreeHalfCesaroSum`;
- `squarefreeHalfDirichletPartialSum_eq_cesaro_discreteDerivative`;
- `no_poleClearedFirstTraceCesaroLocallyBounded`.

Verification on 2026-09-04: direct check pass; targeted build `13030/13030`; axiom audit only
`propext`, `Classical.choice`, `Quot.sound`; umbrella import wired.

## Positive survivor

This argument closes diagonal and any comparably fast pole-degree synchronization, not Cesàro
averaging itself. A decoupled cofinal degree schedule `κ(N)` can evade the discrete-derivative
contradiction only when `N / 5^(κ(N)-24)` is not eventually bounded. This points to genuinely slow
pole schedules as next exact class.
