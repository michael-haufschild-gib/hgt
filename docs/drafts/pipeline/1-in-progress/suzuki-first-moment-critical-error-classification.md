# Suzuki first-moment critical-error classification

- **ID:** CCM-FU-FM-CE
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Classify bounded central unit-Riesz source, hence linear Suzuki curvature first moment, as RH plus bounded square-root-normalized Chebyshev error on natural apertures.

## Goal
Kill or validate the proposed CCM-FU first-moment producer. Chain: central bound ↔ first-moment bound → triangular-curvature bound → RH.

## Facts
- `weightedFirstMomentLinearBound_iff_rh_and_psiRemainderSquareRootBounded` gives first moment ↔ `RH ∧ |ψ(M)-M|=O(√M)`.
- `xiDyadicBandReciprocalPhase_cofinally_unbounded` proves unconditional cofinal unboundedness of Hilbert-rotated reciprocal Xi dyadic packets: Riemann–von Mangoldt band mass `≫T log T` gives packet mass `≫log T`, preserved by simultaneous recurrence.
- Hardy–Littlewood gives `ψ(x)-x=Ω±(√x log log log x)`.

## Status
Classification and spectral amplification are Lean-complete. Remaining Lean no-go gap: constant-`L¹` smooth dyadic bandpass explicit-formula weld from bounded normalized Chebyshev error to the reciprocal Xi packet.
