# AIP Open Problem 6: Complete Resolution of the Shared Surplus Between the Light Cone and the Thin Band

- **ID:** aip-open-problem-6-complete-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md` §7 Open Problem 6 (a), (b), (c)
- **Lean Module:** `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/LightConeSquareRootScaleAndSignedBandObstruction.lean`
- **Statement:** Complete, unconditional resolution of all three parts of Open Problem 6: (a) universal telescoping chain lower bound (`exists_payableOddPartFamily_log_lower_bound`) and two-sided logarithmic capacity law `Θ(log(1/ε))` (`sum_le_of_isPayableOddPartFamily`) for nested strips wider than `ε`; (b) Selberg-sieve widening of the light cone to the exact square-root scale `δ ≍ e^{−r}` (`eventually_sum_vonMangoldtAtom_lightConeBand_le_squareRoot`, `exists_squareRoot_lightCone_allocation`) and unconditional cofinal refutation (`frequently_lightConeBox_oddPart_sharing_fails_at_squareRoot`) at width `δ = C e^{−r}` (`C ≥ 64000`); (c) unconditional refutation of the signed thin-band inequality `Σ_{thinBand r} 2Λ(n)/√n ∫ F F(· + log n) ≤ T(0, r)` for all large `r` via the bipolar edge-dipole witness `bipolarEdgeTentOdd` (`exists_bipolarEdgeTent_signed_thinBand_sharing_fails`), and exact global decomposition (`thinBand_signedCharge_eq_tsum_sub_complement`).

## Gates
- [x] 0 → 1  in-progress: well-posed, corpus searched, attack ideas verified
- [x] 1 → 2  fully-proven: complete paper proofs of (a), (b), (c) with no open dependencies
- [x] 2 → 3  formalized: `LightConeSquareRootScaleAndSignedBandObstruction.lean` verified with `lake --old env lean`, wired into `ArithmeticIncidencePositivity.lean`
- [x] 3 → 4  README updated crisply

## Formalized Declarations
- `GaloisForLFunctions.ArithmeticIncidencePositivity.stripBoxEnergy_mono_of_nonneg`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.sharpMicroFold_ratioSix_shell_ge`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.sum_geometricChain_oddPart_le_stripBoxEnergy`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.IsPayableOddPartFamily`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.sum_le_of_isPayableOddPartFamily`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.exists_payableOddPartFamily_log_lower_bound`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.pow_add_two_mul_pow_pred_le_pow`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.card_properPrimePow_lightConeBand_le`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.card_prime_lightConeBand_le_sieve`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.eventually_sum_vonMangoldtAtom_lightConeBand_le_squareRoot`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.exists_squareRoot_lightCone_allocation`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.stripBoxEnergy_edgeTent_lightConeBox_le`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.frequently_lightConeBox_oddPart_sharing_fails_at_squareRoot`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.bipolarEdgeTentOdd`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.bipolarEdgeTentOdd_mul_shift_nonneg`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.integral_bipolarEdgeTentOdd_mul_shift_ge`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.stripBoxEnergy_bipolarEdgeTentOdd_le`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.exists_bipolarEdgeTent_signed_thinBand_sharing_fails`
- `GaloisForLFunctions.ArithmeticIncidencePositivity.thinBand_signedCharge_eq_tsum_sub_complement`

## Log
- 2026-10-24 — created in 1-in-progress; paper proofs of 6(a), 6(b), 6(c) completed; formalized and verified in `LightConeSquareRootScaleAndSignedBandObstruction.lean` and wired into `ArithmeticIncidencePositivity.lean`.
