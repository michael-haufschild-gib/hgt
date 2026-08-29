# T2 interval-cell Fourier-energy no-go

- **ID:** T2-ICF1.NG
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.RHTower.Sieve.MaynardIntervalCellCubicEnergyNoGo`
- **Corpus sources:** `MaynardAdditiveEnergy`, `MaynardSpatialMellinL4`, `DifferenceEnergyBound`, `FieldOneFiniteCyclicFourierParseval`, `XiHeatCassiniWoldResidualBorelTerminalWidthSpectrum`

## Killed RH chain

The rejected T2 repair was:

cardinality-only generic `L²/L⁴` saving on every low-shell packet
`=>` subcubic `RStar` control
`=>` common-mode low-shell bad-set power saving
`=>` prime-gap moment exponent below `3/2`
`=>` cancellation-first control of the unsplit Wold terminal-plus-edge current
`=>` zero residual terminal width
`=>` RH via `riemannHypothesis_iff_woldResidualBorelTerminalSpectrum_zero`.

Lean kills the first arrow. Consecutive frequency cells are legitimate generic packets, but their
pair-sum multiplicities are triangular and have exact cubic fourth-moment energy.

## Exact obstruction

For `S_n = range n`, the pair-sum fibre at `k` has cardinality

- `k+1` for `k<n`;
- `2n-1-k` for `n<=k<2n`;
- `0` afterward.

Therefore

`3 * maynardRStar(S_n) = 2*n^3+n`.

After the canonical natural-to-integer cell embedding, Lean also proves

`maynardRStar(S_n)/n^3 -> 2/3`.

For every natural constant `C`, some interval packet satisfies

`maynardRStar(S_n) > C*n^2`.

Hence no uniform quadratic cardinality ceiling exists. More importantly, exact cubic saturation
shows the present generic moment interface contains no subcubic power saving to be rearranged out
of cardinality alone.

## Positive survivor

Route T2 itself remains live only through a different producer. It must use arithmetic structure
that excludes or defeats interval packets: an all-shell selected-cell/bad-set estimate, paired with
cancellation-preserving target-reciprocal localization before terminal flux and edge/mesh terms are
split. Further generic `L²/L⁴` manipulation is retired.

## Main Lean theorems

- `maynardNatRStar_range_eq_sum_squares`
- `three_mul_maynardNatRStar_range`
- `three_mul_maynardRStar_intervalCells`
- `tendsto_maynardRStar_intervalCells_div_cube`
- `exists_intervalCells_maynardRStar_gt_quadratic`
- `not_exists_uniform_quadratic_bound_maynardRStar_intervalCells`

## Novelty boundary

Additive-energy/Fourier-fourth-moment identities and triangular convolution of an interval are
classical separately. Novelty claim is the exact formal identification with the corpus's literal
Maynard `RStar` interface and the resulting decisive T2 route classification. No numerical search,
prime-gap computation, or zero data enters the Lean proof.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/Sieve/MaynardIntervalCellCubicEnergyNoGo.lean`: passed.
- Umbrella import added to `GaloisForLFunctions/RHTower.lean`.
- `lake build GaloisForLFunctions.RHTower.Sieve.MaynardIntervalCellCubicEnergyNoGo`: passed (33s; one targeted module build; 9397 jobs).
- Axiom audit of exact triangular energy, integer-cell transport, cubic limit, explicit ceiling violation, and universal no-go: `propext`, `Classical.choice`, `Quot.sound` only.
