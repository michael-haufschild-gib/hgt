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

## Full-surface closure (2026-08-12)

The card `ULF-FSR-1` is now certified in full, not only in its core.  Two further modules were
added, both wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`.

`GaloisForLFunctions.HTGeometry.WienerFormationScale` builds the Wiener receiver scale `W_R` in
coefficient coordinates on `C[[X]]`:

| Clause | Lean declaration |
|---|---|
| admission and norm `(FSR1.10)` | `WienerScaleAdmissible`, `wienerScaleNorm` |
| closure under `+`, `-`, scalars, Cauchy product | `WienerScaleAdmissible.add/.neg/.smul/.mul` |
| submultiplicativity `(FSR1.11)` | `wienerScaleNorm_mul_le` |
| radius monotonicity | `WienerScaleAdmissible.mono`, `wienerScaleNorm_mono` |
| receiver evaluation `(FSR1.12)` and its bound `(FSR1.13)` | `wienerScaleEval`, `norm_wienerScaleEval_le` |
| evaluation is a character | `wienerScaleEval_mul`, `wienerScaleEval_add`, `wienerScaleEvalHom` |
| collar loss `(FSR1.15)` with the sharp constant | `wienerScale_collar_bound`, `wienerScaleNorm_derivative_le` |
| Adams radius law and `(FSR1.19)` | `wienerScaleNorm_adams`, `wienerScaleNorm_adams_le` |
| ghost/Adams exchange `(FSR1.21)` and bound `(FSR1.22)` | `derivative_wienerScaleAdams`, `wienerScaleNorm_derivative_adams_le` |
| receiver covariance `(FSR1.23)` | `wienerScaleEval_adams` |
| Witt fusion `(FSR1.26)` and margin `(FSR1.27)` | `wienerScale_witt_fusion`, `wienerScaleNorm_geom` |
| the receiver algebra and its truncations | `wienerScaleAlgebra`, `wienerScaleTrunc`, `wienerScaleNorm_sub_trunc` |
| character classification, Theorem 4.1(3) | `exists_eval_of_bounded_character`, `wienerScaleEval_injective_point` |

`GaloisForLFunctions.HTGeometry.WienerFormationBanach` supplies Theorem 4.1(1) in full: for
`[Fact (0 < R)]` the type `WienerAlgebra R` carries `NormedCommRing`, `NormedAlgebra C` and
`CompleteSpace` instances, so it is a unital Banach algebra.  Completeness is proved by the weight
isometry `f -> (a_n R^n)` onto `l^1(N)` (`weightCoord`, `toLp`, `ofLp`, `isometryLp`).  The
continuous-character form of Theorem 4.1(3) is `exists_eval_of_continuous_character`, with the
contractive direction `norm_eval_le`; together these give the receiver spectrum `(FSR1.28)`.

`GaloisForLFunctions.HTGeometry.FormalAdicReceiverCollapse` supplies Theorem 3.1 for the literal
`T`-adic topology: `formalAdic_tendsto_smul_X_pow` is `(FSR1.6)`, `formalAdicCharacter_apply_X` is
`(FSR1.8)`, and `formalAdicCharacter_eq_constantCoeff` is `(FSR1.9)`; `formalAdicCharacter_unique`
records that only one receiver survives.

Verification: `lake env lean` on all three modules passes with no diagnostics; the foreground
umbrella build `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` completes 11,857 jobs.
Axiom prints across the whole certified surface report only `propext`, `Classical.choice` and
`Quot.sound`.  The open arithmetic scale/sheaf construction of the card's section 8 is deliberately
not formalized: it is the successor research problem, not a theorem of this card.
