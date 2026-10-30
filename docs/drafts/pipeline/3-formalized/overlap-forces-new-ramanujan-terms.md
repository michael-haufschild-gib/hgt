# Exact overlap loss and crossings of the separated reference

- **ID:** overlap-forces-new-ramanujan-terms
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3.
- **Statement:** Every nonpolar Ramanujan reference energy is `E_m(c)=E_m(1)-log c`;
  its negative range is exactly `c>exp(E_m(1))`.

The self finite part is `log(1/(2πc))+β(φ)/∫φ²`. Only conductor one receives
the pole shift. Subtracting the value at `c=1` therefore leaves `-log c` for
every `m≠1`. Exponentiation gives the exact crossing. For any finite conductor
set `S`, taking `c=exp(1+Σ_(m∈S)|E_m(1)|)` makes every nonpolar member negative.

The actual normalized archimedean self-energy retains this scalar loss without
requiring separated atoms. For a nonzero smooth profile supported in `[0,1]`
and `0<c≤N`, its Robin remainder has absolute value at most
`(exp(1/2)/2)c/N`, by the existing dilation estimate followed by division by atom mass.

This classifies continuation of the separated reference formula. It does not identify
that formula with actual quasimode energies beyond separation, or assert a negative
eigenvalue of the complete matrix. New overlap and non-ratio prime terms remain present.

Lean: `GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/OverlapForcesNewRamanujanTerms.lean`.
Main declarations: `completeWeilAdjunctionEnergy_eq_at_one_sub_log`,
`completeWeilAdjunctionEnergy_neg_iff`,
`exists_overlap_all_nonpolar_reference_energies_negative`, and
`abs_completeWeilSelfError_le_of_width_le_one`.
Kernel check and three transitive axiom audits passed with only
`propext`, `Classical.choice`, `Quot.sound`; final direct audit is pending.
Imported by the RenormalizedArithmeticPotentialTheory umbrella.
