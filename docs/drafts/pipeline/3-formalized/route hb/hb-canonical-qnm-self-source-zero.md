# Canonical QNM self-source zero law

- **ID:** HB-CQ-SS0
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/rh-current-frontier-map.md · HB literal QNM-value/extinction edge
- **Statement:** `physicalSelfSourceCoefficient q = 0` implies `canonicalQNMValue q br side amp = 0` for every literal branch, QNM side, and amplitude.

## Goal

Give a source-fixed necessary zero locus for the literal HB QNM receiver. This is non-circular: it uses only the metric cutoff, its retained corner, and the already-defined QNM limit; it invokes neither RH nor a left-channel equality.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, exact attack path.
- [x] 1 → 2  fully-proven: complete paper proof below; no mathematical dependency open.
- [x] 2 → 3 formalized: unconditional Lean proof (see "Formalized (2026-09-27)").
- [ ] 3 → 4  publication-ready.

## Proof `[PROVED HERE]`

Fix `q, br, side, amp` and write `P = physicalSelfSourceCoefficient q`; suppose `P = 0`.
For nonreal `w` with `-2 < Re w` and any `0 < e < 1`, `tortoiseOf e < 0`. On the open interval from `tortoiseOf e` to `0`, `outerDensity_decomposition` writes the literal outer density as a sum whose two terms each contain `P`; hence its interval integral is zero (endpoints are null). `greenCoefficient` and `forcingCoefficient` are respectively explicit multiples of `P`, so `canonicalMetricCutoff q br amp w e = 0`.

Such `e` are eventually all points of the positive cutoff filter. Therefore the defining `limUnder` gives `canonicalRadialValue q br amp w = 0`. Independently, `continuedCornerAmplitude` is definitionally `P * greenHorizonAmplitude`; it and its frequency derivative are zero. Every summand of `physicalCornerCandidate` is consequently zero. Thus `canonicalAction q br amp w = 0` throughout that nonreal half-strip.

`physicalFundamentalFrequency q side` lies in this strip and has nonzero imaginary part. Its punctured neighborhood remains in the strip, so the defining QNM `limUnder` of `canonicalAction` is zero. This is the stated result.

## Whole-route consequence

In the strict-right chamber, the existing angular theorem rewrites the premise as
`xi(5q/2-1)=0 ∨ xi(q/2)=0 ∨ xi(3q/2)=0`. Hence a source-fixed identification of the literal QNM receiver with unit left-source extinction must either respect this affine zero locus or be disproved by it. This does not prove RH: the still-open hard arrow is QNM finite value ↔ canonical left-source extinction.

## Lean target

`RHTower.D4BMOriginalCanonicalAction.canonicalQNMValue_eq_zero_of_physicalSelfSourceCoefficient_eq_zero`

Proof architecture: `outerDensity_decomposition` → `intervalIntegral.integral_congr_uIoo` → cutoff `limUnder`; unfold `continuedCornerAmplitude` for corner zero; use the QNM-strip neighborhood and second `limUnder`.

## Formalized (2026-09-27)

`RHTower.D4BMOriginalCanonicalAction.canonicalQNMValue_eq_zero_of_physicalSelfSourceCoefficient_eq_zero`
(`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCanonicalQNMSelfSourceZero.lean`), with the
steps of the paper proof as separate lemmas: `canonicalMetricCutoff_eq_zero_of_…` (every cutoff
`0 < e < 1` vanishes: `outerDensity_decomposition` on `uIoo (tortoiseOf e) 0`, both counterterm
coefficients carry `P`), `canonicalRadialValue_eq_zero_of_…`, `physicalCornerCandidate_eq_zero_of_…`
(the corner amplitude is the zero function), `canonicalAction_eq_zero_of_…` (on `-2 < Re w`).
No hypothesis beyond `physicalSelfSourceCoefficient q = 0`.  Axioms
`[propext, Classical.choice, Quot.sound]`.  The former missing-olean block no longer exists.
