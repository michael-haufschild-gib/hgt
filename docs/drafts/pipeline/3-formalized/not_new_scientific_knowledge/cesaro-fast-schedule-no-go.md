# Cesàro fast-schedule no-go

- **ID:** cesaro-fast-schedule-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `squarefree-convolution-half-cesaro-source-criterion.md`
- **Status:** `[PROVED HERE] [LEAN-PROVED] [NOT RH]`

## Statement

Let `κ : ℕ → ℕ`. If there are constants `B ≥ 0` and `N₀` such that, for every `N ≥ N₀`,

\[
  24\le κ(N),\qquad N\le B\,5^{κ(N)-24},
\]

then the canonical pole-cleared scheduled Cesàro approximants are not locally bounded on
`rightHalf`.

## Proof

At `boundaryExteriorPoint=6/11`, certified pole amplification and assumed local boundedness imply
that `N‖C_N(6/11)‖` is eventually bounded. The exact discrete derivative

\[
  D_N=(N+1)C_{N+1}-NC_N
\]

then makes the raw convolution-half Dirichlet partial sums `D_N(6/11)` eventually bounded. This
contradicts their unconditional arithmetic unboundedness.

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroFastScheduleNoGo.lean`.

Main theorem: `no_poleClearedFirstTraceCesaroScheduledLocallyBounded_of_fast`.

Verification on 2026-09-04: direct check pass; targeted build `13032/13032`; axiom audit only
`propext`, `Classical.choice`, `Quot.sound`; umbrella import wired.

## Positive survivor

The obstruction closes every schedule whose certified base-five boundary amplification dominates
the arithmetic cutoff. A live schedule must be cofinal but fail this dominance. The canonical
iterated-log schedule provably does so; its local boundedness remains open.
