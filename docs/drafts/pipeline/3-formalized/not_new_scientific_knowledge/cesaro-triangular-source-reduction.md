# Cesàro triangular source reduction

- **ID:** cesaro-triangular-source-reduction
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `squarefree-convolution-half-cesaro-source-criterion.md`
- **Status:** `[PROVED HERE] [LEAN-PROVED] [NOT RH]`

## Statement

Canonical convolution-half Cesàro averages have exact triangular form

\[
 C_N(s)=\frac1N\sum_{n<N}(N-n-1)a_n n^{-s}.
\]

If any cofinal Cayley pole-degree schedule makes the pole-cleared Cesàro family locally bounded on
`rightHalf`, then `C_N(6/11)→0`.

## Proof

Finite induction reverses the nested cutoff sums and counts term `n` exactly `N-n-1` times. At
`6/11`, cofinality sends the certified lower bound `5^(κ(N)-24)` to infinity. Local boundedness of
the pole-cleared product therefore squeezes the schedule-independent source norm to zero.

## Lean formalization

Modules:

- `formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroWeightedIdentity.lean`;
- `formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroVanishingNecessity.lean`.

Verification on 2026-09-04: direct checks pass; targeted builds `12848/12848` and `13043/13043`;
axiom audits only `propext`, `Classical.choice`, `Quot.sound`; umbrella imports wired.

## Positive survivor

Schedule tuning is secondary. One arithmetic statement now decides all cofinal schedules:
`¬ Tendsto (fun N => squarefreeHalfCesaroSum N boundaryExteriorPoint) atTop (𝓝 0)` closes the whole
class. Corpus presently has no asymptotic theorem for this exact coefficient mean.
