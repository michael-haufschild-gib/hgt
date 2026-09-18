# HB-B2 complementary-rate current intertwiner

- **ID:** hb-b2-complementary-current
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** rh-current-frontier-map.md · HB-B2 boundary obligation
- **Statement:** The existing opposite-branch `traceFlux`, and any lift proved to preserve its clock, cannot realize the one-branch B2 contact current.

## Exact killing mechanism

The same-rate scalar Peierls pairing is biquadratic in its two source
amplitudes and antisymmetric, hence vanishes after polarization.  The only
complementary source-rate choice has
`physicalRate q true + physicalRate q false = -6`, while a literal B2 contact
has clock `2 * physicalRate q branch`.  Equality would force `q = 1/2`,
contradicting the corpus's nonreal Xi-zero support.  Existing
`traceFlux_physical_step` independently gives the same fixed `exp(-6T)`
opposite-rate clock.

## Strongest positive survivor

**Clock dichotomy.** Every literal two-source Peierls candidate is either
same-rate and identically zero, or complementary-rate and fixed at clock `-6`.
Neither can be identified with a nonzero one-branch B2 contact at clock `2s`
without an impermissible clock change.

## Consequence

This kills the tempting `traceFlux`/opposite-branch shortcut only.  It does
**not** establish a time-translation law for the full two-event causal Peierls
pair, hence does not kill every complementary B2 realization.  The next hard
theorem is precisely that full-pair clock law; no map may assume it.

## Lean status

`ThetaCuspHawkingBMLiteralCyclicPeierlsClockDichotomyNoGo.lean` passes direct
`lake env lean` audit.  Its targeted `lake build` was stopped after 30 seconds
because Lake replayed a large graph; module is intentionally not wired until
that final audit can run within the no-long-build rule.  The same-rate
amplitude proof is source-complete but awaits its direct dependency build.
