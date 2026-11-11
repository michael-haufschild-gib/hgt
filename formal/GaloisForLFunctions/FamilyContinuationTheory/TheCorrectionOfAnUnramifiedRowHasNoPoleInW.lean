import GaloisForLFunctions.FamilyContinuationTheory.ThePrincipalRowIsAnEulerProduct

/-!
# The correction of an unramified row has no pole in `w`

At a good prime `π ∤ u` (`j = 0`) the local sum of the row `u` is
`P = (1 − V)⁻¹ + W (1 − W)⁻¹ + (1 − R)⁻¹ B`, with `W = ρY`, `D = η ρ̄ X` and
`B = R (1 − Q⁻¹)(1 − V)⁻¹ + W R − D − η (Q − 1) X Y V (1 − V)⁻¹` (the `j = 0` base sums of the
complete local identity). Removing the scalar Euler factors leaves the correction
`H = P (1 − V)(1 − W)/(1 − D)`, and with

`E = (1 − R)⁻¹ (R (1 − Q⁻¹)(1 − V)⁻¹ + W R − D R − η (Q − 1) X Y V (1 − V)⁻¹)`   (`rowE`)

one has the pole-free form

`H = 1 + (D (V + W − V W) − V W + (1 − V)(1 − W) E)/(1 − D)`   (`rowH`, `local_mul_eq_rowH`):

the factor `(1 − W)⁻¹` of the numerator `ζ`-function has cancelled. This is the expression that
continues `H` to `Re w ≤ 0`. Its distance from `1` is bounded by the sizes of the products
`DV, DW, VW, R` and `Q X Y V` (`norm_rowH_sub_one_le`).
-/

noncomputable section

open scoped BigOperators

namespace GaloisForLFunctions.FamilyContinuationTheory

/-- The excess `E = P* + D` of the ramified part over `−D`. -/
def rowE (Q ηp X Y V R W D : ℂ) : ℂ :=
  (1 - R)⁻¹ * (R * (1 - Q⁻¹) * (1 - V)⁻¹ + W * R - D * R -
    ηp * (Q - 1) * X * Y * V * (1 - V)⁻¹)

/-- The pole-free correction `1 + (D (V + W − VW) − VW + (1 − V)(1 − W) E)/(1 − D)`. -/
def rowH (Q ηp X Y V R W D : ℂ) : ℂ :=
  1 + (D * (V + W - V * W) - V * W + (1 - V) * (1 - W) * rowE Q ηp X Y V R W D) / (1 - D)

/-- **The cancellation.** The local sum times the scalar factors is the pole-free correction. -/
theorem local_mul_eq_rowH (Q ηp X Y V R W D : ℂ) (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hR : 1 - R ≠ 0) (hD : 1 - D ≠ 0) :
    ((1 - V)⁻¹ + W * (1 - W)⁻¹ + (1 - R)⁻¹ * (R * (1 - Q⁻¹) * (1 - V)⁻¹ + W * R - D -
      ηp * (Q - 1) * X * Y * V * (1 - V)⁻¹)) * (1 - V) * (1 - W) / (1 - D) =
      rowH Q ηp X Y V R W D := by
  unfold rowH rowE
  field_simp
  ring

/-- **The size of the correction.** For `‖V‖, ‖R‖, ‖D‖ < 1` and `‖1 − Q⁻¹‖ ≤ 1`,
`‖H − 1‖ ≤ (‖D‖‖V‖ + ‖D‖‖W‖ + ‖D‖‖V‖‖W‖ + ‖V‖‖W‖ + (1 + ‖V‖)(1 + ‖W‖) e)/(1 − ‖D‖)` with
`e = (1 − ‖R‖)⁻¹ (‖R‖ (1 − ‖V‖)⁻¹ + ‖W‖‖R‖ + ‖D‖‖R‖ + ‖η‖‖Q − 1‖‖X‖‖Y‖‖V‖ (1 − ‖V‖)⁻¹)`. -/
theorem norm_rowH_sub_one_le (Q ηp X Y V R W D : ℂ) (hV : ‖V‖ < 1) (hR : ‖R‖ < 1)
    (hD : ‖D‖ < 1) (hq : ‖1 - Q⁻¹‖ ≤ 1) :
    ‖rowH Q ηp X Y V R W D - 1‖ ≤
      (‖D‖ * ‖V‖ + ‖D‖ * ‖W‖ + ‖D‖ * ‖V‖ * ‖W‖ + ‖V‖ * ‖W‖ + (1 + ‖V‖) * (1 + ‖W‖) *
        ((1 - ‖R‖)⁻¹ * (‖R‖ * (1 - ‖V‖)⁻¹ + ‖W‖ * ‖R‖ + ‖D‖ * ‖R‖ +
          ‖ηp‖ * ‖Q - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ * (1 - ‖V‖)⁻¹))) / (1 - ‖D‖) := by
  have hV0 : 0 < 1 - ‖V‖ := by linarith
  have hR0 : 0 < 1 - ‖R‖ := by linarith
  have hD0 : 0 < 1 - ‖D‖ := by linarith
  -- lower bounds of the denominators
  have dV : 1 - ‖V‖ ≤ ‖1 - V‖ := by
    have := norm_sub_norm_le (1 : ℂ) V
    rw [norm_one] at this
    linarith
  have dR : 1 - ‖R‖ ≤ ‖1 - R‖ := by
    have := norm_sub_norm_le (1 : ℂ) R
    rw [norm_one] at this
    linarith
  have dD : 1 - ‖D‖ ≤ ‖1 - D‖ := by
    have := norm_sub_norm_le (1 : ℂ) D
    rw [norm_one] at this
    linarith
  have iV : ‖(1 - V)⁻¹‖ ≤ (1 - ‖V‖)⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hV0 dV
  have iR : ‖(1 - R)⁻¹‖ ≤ (1 - ‖R‖)⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hR0 dR
  have iD : ‖(1 - D)⁻¹‖ ≤ (1 - ‖D‖)⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hD0 dD
  -- the excess
  have hE : ‖rowE Q ηp X Y V R W D‖ ≤ (1 - ‖R‖)⁻¹ * (‖R‖ * (1 - ‖V‖)⁻¹ + ‖W‖ * ‖R‖ +
      ‖D‖ * ‖R‖ + ‖ηp‖ * ‖Q - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ * (1 - ‖V‖)⁻¹) := by
    unfold rowE
    rw [norm_mul]
    refine mul_le_mul iR ?_ (norm_nonneg _) (inv_nonneg.mpr hR0.le)
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
    · rw [norm_mul, norm_mul]
      calc ‖R‖ * ‖1 - Q⁻¹‖ * ‖(1 - V)⁻¹‖ ≤ ‖R‖ * 1 * (1 - ‖V‖)⁻¹ := by gcongr
        _ = ‖R‖ * (1 - ‖V‖)⁻¹ := by ring
    · rw [norm_mul]
    · rw [norm_mul]
    · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
      gcongr
  -- the numerator
  have hnum : ‖D * (V + W - V * W) - V * W + (1 - V) * (1 - W) * rowE Q ηp X Y V R W D‖ ≤
      ‖D‖ * ‖V‖ + ‖D‖ * ‖W‖ + ‖D‖ * ‖V‖ * ‖W‖ + ‖V‖ * ‖W‖ + (1 + ‖V‖) * (1 + ‖W‖) *
        ((1 - ‖R‖)⁻¹ * (‖R‖ * (1 - ‖V‖)⁻¹ + ‖W‖ * ‖R‖ + ‖D‖ * ‖R‖ +
          ‖ηp‖ * ‖Q - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ * (1 - ‖V‖)⁻¹)) := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_mul]
      calc ‖D‖ * ‖V + W - V * W‖ ≤ ‖D‖ * (‖V‖ + ‖W‖ + ‖V‖ * ‖W‖) := by
            gcongr
            refine (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
            rw [norm_mul]
        _ = ‖D‖ * ‖V‖ + ‖D‖ * ‖W‖ + ‖D‖ * ‖V‖ * ‖W‖ := by ring
    · rw [norm_mul]
    · rw [norm_mul, norm_mul]
      refine mul_le_mul (mul_le_mul ((norm_sub_le _ _).trans (by rw [norm_one]))
        ((norm_sub_le _ _).trans (by rw [norm_one])) (norm_nonneg _) (by positivity)) hE
        (norm_nonneg _) (by positivity)
  unfold rowH
  rw [add_sub_cancel_left, norm_div]
  calc _ ≤ _ / ‖1 - D‖ := by gcongr
    _ ≤ _ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact inv_anti₀ hD0 dD

end GaloisForLFunctions.FamilyContinuationTheory
