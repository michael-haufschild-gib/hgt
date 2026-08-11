# Formation-scale receiver core — Lean formalization record

- **Source card:** `ULF-FSR-1`
- **Lean module:** `GaloisForLFunctions.HTGeometry.FormationScaleReceiver`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED CORE] [NO SORRY] [NO AXIOMS ADDED]`

## Certified declarations

1. `linear_mul_exp_neg_le`: one logarithmic derivative is absorbed by every positive analytic
   collar.
2. `formationWienerSummable_ghost`: logarithmic ghost formation transports a one-sided Wiener
   receiver from radius `ρ` to every strict smaller radius `ρ'`.
3. `formationWienerNorm_ghost_le`: exact collar estimate
   `‖G a‖_{ρ'} ≤ (ρ-ρ')⁻¹ ‖a‖_ρ`.
4. `no_bounded_derivation_of_generator`: no bounded derivation on one normed complex algebra can
   send a nonnilpotent formation generator to the unit.
5. `continuous_receiver_kills_formal_generator`: every continuous complex receiver kills a
   formal coordinate whose arbitrarily scalar-renormalized powers converge to zero.
6. `derivative_formationAdams`: exact polynomial fusion
   `D Ψ_q = q X^(q-1) Ψ_q D`.
7. `eval_formationAdams`: receiver transport `ev_z Ψ_q = ev_(z^q)`.
8. `eval_derivative_formationAdams`: pointwise fused ghost/Adams/receiver law.

These results certify the new field-level mechanism: generation cannot be represented by one
bounded carrier; its natural representation is operation-indexed and scale-valued.  Existing
`ClockAnalyticWienerScale` independently certifies the same collar mechanism for a two-sided
Fourier/Laplacian organ.

## Deliberately uncertified remainder

The full multiplicative one-sided Wiener algebra, its complete character-space classification,
and infinite exterior/formation inverse remain on the Stage-2 source card.  They are not claimed
Lean-proven by this record.
