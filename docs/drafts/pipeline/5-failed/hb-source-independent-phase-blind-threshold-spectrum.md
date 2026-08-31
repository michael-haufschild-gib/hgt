# HB source-independent phase-blind threshold spectrum

- **ID:** HB-PHASE-BLIND-THRESHOLD-FAILED
- **Stage:** 5-failed
- **Type:** route-class no-go
- **Route:** HB regular peripheral spectrum with source-independent zero mode

## Retired claim

Complete the HB radiative `++` response using arbitrary strictly damped finite-variation modes, an
arbitrary `L¹` real-axis branch-cut continuum, and one source-independent threshold/zero-frequency
atom, then use late-time extinction to obtain fixed-clock covariance and RH.

## Exact obstruction

The two physical half-turn seed sectors may have unrelated transient measures, densities, carrier
types, and damping profiles. Each transient still vanishes at late time, leaving its threshold atom.
If both completed pole numerators cancel, cubic AIME phase covariance forces the exact law

`zeroMode(-A) - zeroMode(A) = 2 * AIME(A)`.

For every nonzero seed and every Xi divisor copy, `AIME(A) ≠ 0`. A source-independent or half-turn-even
threshold atom has zero left side and is therefore impossible. This uses neither RH nor zero
simplicity and permits damping accumulating at zero.

Lean capstone:
`RHTower.d4BMPassivePeripheralSpectralPhaseBlindThresholdCancellationRouteKilled`.

## Positive survivor

A viable regular threshold completion must carry a nonzero odd cubic source charge. Its two
half-turn threshold coefficients must differ by exactly twice the physical AIME numerator. Merely
adding zero-frequency spectral mass is insufficient; the atom must be source-adapted and
phase-sensitive.

Distinct survivors are:

- a zero mode with the forced cubic phase transformation;
- singular non-Rajchman peripheral spectrum;
- infinite-variation spectral completion.

This card does not retire those classes or the full HB route.
