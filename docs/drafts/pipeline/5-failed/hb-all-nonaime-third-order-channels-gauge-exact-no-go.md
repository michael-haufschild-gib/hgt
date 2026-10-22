# HB all-non-AIME third-order channels gauge-exact no-go

- **ID:** HB-ANTCGE-NG
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · HB `DYN ORIENT LAND`
- **Statement:** At critical-line unit BM incidence with nonzero absorbed seed, the charge-orthogonal stationary cascade, second-harmonic cascade, and direct third variation cannot all be exact under the linearized Einstein--Teukolsky operator.

## No-go closure

- **Exact killing theorem/mechanism:** `d4EinsteinThirdOrder_unitBMTarget_of_criticalLine_forces_nonexact_channel`. BM incidence forces the aggregate non-AIME resonant projection to `-AIMENumerator`, which is nonzero for nonzero seed; a left resonant state annihilates every channel in `range L`.
- **Strongest positive survivor:** `d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine`. This is an exact value law, not only a nonvanishing obstruction: the aggregate non-AIME cokernel pairing is fixed uniquely by the source-derived AIME numerator.
- **New insight:** A successful literal HB producer cannot gauge away all non-AIME third-order dynamics. It must generate a genuine cokernel class in the charge-orthogonal stationary, second-harmonic, or direct-third-variation sector, with aggregate left projection exactly cancelling AIME on every critical fibre.
- **Status:** Dependency-closed paper proof and Lean proof in `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMThirdOrderCokernelNecessity`; targeted build and axiom audit pass. Formalized survivor card records literature audit.

## Log

- 2026-08-28 — all-non-AIME gauge-exact route retired; exact forced projection and cokernel trichotomy preserved.
