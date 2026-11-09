# Smoothed torsion locking and the discriminant defect

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B129, scalar locking of the actual Abel torsion energy with the smoothed archimedean Green energy.

## Exact target

For a real compactly supported C² profile `g`, put copies at `log n` with coefficients `x_n`, below the atom spacing. Let `f` be this packet and `M=∫g²`. Use the actual torsion channel `M·torsionForm(ρ,S,x)` and the actual smoothed archimedean channel `∫archDamped(r,u)·autocorr(f,u)du`.

Conjecture: a scalar locking normalized to Weil's form at degree one has limit

`weilQuad(f) − M Σ_n x_n² selfIntersection(n)`.

Consequently it cannot reproduce Weil's form on all smoothed probes: identical translated profiles at degrees 1 and 4 have equal Weil energy but limiting locked energies differing by `−M log 2`. This tests B129 on source-compatible smooth probes where the existing prime bridge is exact. It does not identify an unspecified alternative torsion smoothing with this channel.

## Proof obligations

1. Derive the archimedean renormalized limit for autocorrelations of actual C² compact probes, including its identification with the Lévy energy.
2. Construct a probe-independent admissible scalar locking and calculate its limit using the actual torsion form.
3. Prove the discriminant defect for every separated packet, and impossibility of simultaneous Weil limits at degrees 1 and 4 for every scalar locking.
4. Identify the correction forced by the defect and its relation to the existing spacing regulator. Do not count reformulations of the atomic anomaly as separate contributions.

## Corpus inputs

- `SurfaceOfSpecZ/TheArchimedeanSelfEnergyIsLogarithmic.lean`.
- `ArithmeticIntersectionTheory/TheHeckeCocycleOfRenormalization.lean`.
- `ArithmeticElectrostatics/TheStabilityLawAtAtomicResolution.lean`: exact packet mass and prime form below the spacing.
- `SpacingScaleHarmonicAnalysis/WeilsFormIsContinuousInTheLevyNorm.lean`: actual Weil form and translation invariance.

**Status:** conjecture; no new theorem verified; B129 not marked solved.
