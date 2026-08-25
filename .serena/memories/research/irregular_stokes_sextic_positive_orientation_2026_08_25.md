# Sixth cold Malgrange orientation (2026-08-25)

Formalized unconditional positive orientation of sixth prime/Gamma wall Malgrange target.

Module: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallSexticMalgrangePositiveOrientation.lean`.

Main chain: Schwarz-pair height gap gives `‖xiZeroCopyReciprocalSquare q‖ < 231/9769`; hence `xiShiftAbsoluteMass 5 ≤ (231/9769)^4 * xiShiftAbsoluteMass 1`. Power-two sector law gives `(41/42) * xiShiftAbsoluteMass 1 ≤ normalizedPrimeArchMoment 1`, and existing source bound gives `normalizedPrimeArchMoment 1 < 17/200000`. Triangle inequality gives `normalizedPrimeArchMoment 5 ≤ xiShiftAbsoluteMass 5`. Exact rational separation plus `1/25 < normalizedPrimeArchMoment 0` proves `normalizedPrimeArchMoment 5 - normalizedPrimeArchMoment 0^6/32 < 0`, hence `0 < -60*(...)`, matching all-order cold law at `n=5`.

New declarations: `norm_xiZeroCopyReciprocalSquare_lt_twoHundredThirtyOne_over_nineThousandSevenHundredSixtyNine`, `xiShiftAbsoluteMass_five_le_radius_pow_four_mul_one`, `normalizedPrimeArchMoment_five_le_xiShiftAbsoluteMass_five`, `normalizedPrimeArchMoment_five_sub_zero_pow_six_div_thirtyTwo_neg`, `routePPrimitiveGammaJuliaStokesPrimeGammaWallColdSixthMalgrangeTarget_pos`.

Card: `docs/drafts/pipeline/3-formalized/route-p-prime-gamma-wall-sixth-malgrange-positive-orientation.md`.

Targeted direct Lean check passed. All five declarations use only `[propext, Classical.choice, Quot.sound]`. No umbrella build/lint sweep. Literature audit found general Malgrange/JMU and irregular tau machinery but no completed-Xi sixth cold sign; absence recorded only as inference.