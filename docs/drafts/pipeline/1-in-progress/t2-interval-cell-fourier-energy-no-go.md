# T2 interval-cell Fourier-energy no-go

## Status

Formalized and audited in Lean. T2's generic cardinality-only `L²/L⁴` repair is retired.

## Corpus-derived conjecture T2-ICF1

For the consecutive selected-cell packet `range n`, Maynard's literal fourth-moment count satisfies

`3 * RStar(range n) = 2 * n^3 + n`.

Hence its cubic normalization tends to `2/3`, and for every proposed quadratic cardinality constant
`C` there is an interval packet with `RStar > C * n^2`.

## Proof chain being tested

The proposed T2 repair was:

cardinality-only generic `L²/L⁴` saving on every low-shell selected-cell packet
`=>` subcubic `RStar` control
`=>` common-mode low-shell bad-set saving
`=>` prime-gap moment exponent below `3/2`
`=>` cancellation-first control of the unsplit terminal-plus-edge current
`=>` zero Wold residual terminal width
`=>` RH via `riemannHypothesis_iff_woldResidualBorelTerminalSpectrum_zero`.

T2-ICF1 kills the first arrow: consecutive cells are admissible generic packets and have exact
cubic energy. No cardinality-only rearrangement of the existing `L²/L⁴` interface can supply the
needed power saving.

## Positive survivor

T2 is not retired. A viable producer must add arithmetic information absent from cardinality and
generic moments: a selected-cell/bad-set theorem excluding or defeating interval packets, together
with cancellation-preserving target-reciprocal localization before terminal and edge terms split.

## Proved Lean theorems

- `maynardNatRStar_range_eq_sum_squares`
- `three_mul_maynardNatRStar_range`
- `three_mul_maynardRStar_intervalCells`
- `tendsto_maynardRStar_intervalCells_div_cube`
- `exists_intervalCells_maynardRStar_gt_quadratic`
- `not_exists_uniform_quadratic_bound_maynardRStar_intervalCells`

## Evidence

Conjecture was derived after corpus searches locating:

- `maynardRStar`, `maynardRStar_sandwich`;
- `maynardNatRStar_eq_maynardRStar_map`;
- `integral_norm_four_maynardUnitCellMellinPacket_le_rstar`;
- `card_pairs_diff_eq` and `energy_le_cube`;
- `riemannHypothesis_iff_woldResidualBorelTerminalSpectrum_zero`.

No numerical or computational result is used in the proof.
