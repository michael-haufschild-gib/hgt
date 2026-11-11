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
`DV, DW, VW, R` and `Q X Y V` (`norm_rowH_sub_one_le`): `‖H − 1‖ ≤ 80 Q^{−363/200}` near the
principal residue point (`norm_rowH_sub_one_le_D2`) and `‖H − 1‖ ≤ 80 Q^{−1−ε₀}` on the region of
the contour moves `Re x ≥ 51/100`, `Re w ≥ −1/100`, `Re(x + w) ≥ 1 + ε₀`, `Re z ≥ 17/50`
(`norm_rowH_sub_one_le_D1`).
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
  refine (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans ?_
  exact div_le_div_of_nonneg_left (by positivity) hD0 dD

/-- `Q^a Q^b ≤ Q^c` for `Q ≥ 1` and `a + b ≤ c`. -/
theorem rpow_mul_rpow_le_of_add_le {Q a b c : ℝ} (hQ : 1 ≤ Q) (h : a + b ≤ c) :
    Q ^ a * Q ^ b ≤ Q ^ c := by
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hQ h

/-- **The correction near the principal residue point.** At a good prime of norm `Q ≥ 7`, on
`Re x ≥ 7/8`, `Re w ≥ 19/20`, `Re z ≥ 33/200` (`‖X‖ ≤ Q^{−7/8}`, `‖Y‖, ‖W‖ ≤ Q^{−19/20}`,
`‖V‖ ≤ Q^{−99/100}`): `‖H − 1‖ ≤ 80 Q^{−363/200}`; the binding term is `Q X Y V`. -/
theorem norm_rowH_sub_one_le_D2 {Q : ℝ} (hQ : 7 ≤ Q) {ηp X Y V R W D : ℂ}
    (hX : ‖X‖ ≤ Q ^ (-(7 / 8 : ℝ))) (hY : ‖Y‖ ≤ Q ^ (-(19 / 20 : ℝ)))
    (hW : ‖W‖ ≤ Q ^ (-(19 / 20 : ℝ))) (hV : ‖V‖ ≤ Q ^ (-(99 / 100 : ℝ))) (hD : ‖D‖ ≤ ‖X‖)
    (hR : ‖R‖ ≤ Q ^ 4 * ‖X‖ ^ 6 * ‖V‖) (hη : ‖ηp‖ ≤ 1) :
    ‖rowH (Q : ℂ) ηp X Y V R W D - 1‖ ≤ 80 * Q ^ (-(363 / 200 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  set T := Q ^ (-(363 / 200 : ℝ))
  have hT0 : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  -- the individual sizes are at most `1/2`
  have hx2 : ‖X‖ ≤ 1 / 2 := hX.trans (rpow_le_half_of_four_le hQ4 (by norm_num))
  have hy2 : ‖Y‖ ≤ 1 / 2 := hY.trans (rpow_le_half_of_four_le hQ4 (by norm_num))
  have hw2 : ‖W‖ ≤ 1 / 2 := hW.trans (rpow_le_half_of_four_le hQ4 (by norm_num))
  have hv2 : ‖V‖ ≤ 1 / 2 := hV.trans (rpow_le_half_of_four_le hQ4 (by norm_num))
  have hd2 : ‖D‖ ≤ 1 / 2 := hD.trans hx2
  -- `R`
  have hRT : ‖R‖ ≤ T := by
    refine hR.trans ?_
    calc Q ^ 4 * ‖X‖ ^ 6 * ‖V‖ ≤ Q ^ 4 * (Q ^ (-(7 / 8 : ℝ))) ^ 6 * Q ^ (-(99 / 100 : ℝ)) := by
          gcongr
      _ = Q ^ ((4 : ℝ) + (-(7 / 8 : ℝ)) * 6 + (-(99 / 100 : ℝ))) := by
          rw [Real.rpow_add hQ0, Real.rpow_add hQ0, Real.rpow_mul hQ0.le]
          norm_cast
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have hr2 : ‖R‖ ≤ 1 / 2 := hRT.trans ((Real.rpow_le_rpow_of_exponent_le hQ1
    (by norm_num : -(363 / 200 : ℝ) ≤ -(1 / 2))).trans (rpow_le_half_of_four_le hQ4 le_rfl))
  -- the products
  have hdv : ‖D‖ * ‖V‖ ≤ T := (mul_le_mul (hD.trans hX) hV (norm_nonneg _)
    (Real.rpow_nonneg hQ0.le _)).trans (rpow_mul_rpow_le_of_add_le hQ1 (by norm_num))
  have hdw : ‖D‖ * ‖W‖ ≤ T := (mul_le_mul (hD.trans hX) hW (norm_nonneg _)
    (Real.rpow_nonneg hQ0.le _)).trans (rpow_mul_rpow_le_of_add_le hQ1 (by norm_num))
  have hvw : ‖V‖ * ‖W‖ ≤ T := (mul_le_mul hV hW (norm_nonneg _)
    (Real.rpow_nonneg hQ0.le _)).trans (rpow_mul_rpow_le_of_add_le hQ1 (by norm_num))
  have hdvw : ‖D‖ * ‖V‖ * ‖W‖ ≤ T :=
    (mul_le_of_le_one_right (by positivity) (by linarith)).trans hdv
  have hQm1 : ‖(Q : ℂ) - 1‖ ≤ Q := by
    rw [show (Q : ℂ) - 1 = ((Q - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hP : ‖ηp‖ * ‖(Q : ℂ) - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ ≤ T := by
    calc ‖ηp‖ * ‖(Q : ℂ) - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ ≤
        1 * Q * Q ^ (-(7 / 8 : ℝ)) * Q ^ (-(19 / 20 : ℝ)) * Q ^ (-(99 / 100 : ℝ)) := by
          gcongr
      _ = Q ^ ((1 : ℝ) + (-(7 / 8 : ℝ)) + (-(19 / 20 : ℝ)) + (-(99 / 100 : ℝ))) := by
          rw [Real.rpow_add hQ0, Real.rpow_add hQ0, Real.rpow_add hQ0, Real.rpow_one, one_mul]
      _ = T := by norm_num; rfl
  have hq : ‖1 - ((Q : ℂ))⁻¹‖ ≤ 1 := by
    rw [show (1 : ℂ) - (Q : ℂ)⁻¹ = ((1 - Q⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    have : 0 < Q⁻¹ := inv_pos.mpr hQ0
    have : Q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ1
    constructor <;> linarith
  refine (norm_rowH_sub_one_le (Q : ℂ) ηp X Y V R W D (by linarith) (by linarith) (by linarith)
    hq).trans ?_
  -- the denominators are at most `2`
  have iv : (1 - ‖V‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have ir : (1 - ‖R‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have iv0 : 0 ≤ (1 - ‖V‖)⁻¹ := inv_nonneg.mpr (by linarith)
  have ir0 : 0 ≤ (1 - ‖R‖)⁻¹ := inv_nonneg.mpr (by linarith)
  have he : (1 - ‖R‖)⁻¹ * (‖R‖ * (1 - ‖V‖)⁻¹ + ‖W‖ * ‖R‖ + ‖D‖ * ‖R‖ +
      ‖ηp‖ * ‖(Q : ℂ) - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ * (1 - ‖V‖)⁻¹) ≤ 2 * (6 * T) := by
    refine mul_le_mul ir ?_ (by positivity) (by norm_num)
    have t1 : ‖R‖ * (1 - ‖V‖)⁻¹ ≤ T * 2 := mul_le_mul hRT iv iv0 hT0
    have t2 : ‖W‖ * ‖R‖ ≤ T := (mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans hRT
    have t3 : ‖D‖ * ‖R‖ ≤ T := (mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans hRT
    have t4 : ‖ηp‖ * ‖(Q : ℂ) - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ * (1 - ‖V‖)⁻¹ ≤ T * 2 :=
      mul_le_mul hP iv iv0 hT0
    linarith
  have hvw' : (1 + ‖V‖) * (1 + ‖W‖) ≤ 9 / 4 := by
    nlinarith [norm_nonneg V, norm_nonneg W]
  have hnum : ‖D‖ * ‖V‖ + ‖D‖ * ‖W‖ + ‖D‖ * ‖V‖ * ‖W‖ + ‖V‖ * ‖W‖ + (1 + ‖V‖) * (1 + ‖W‖) *
      ((1 - ‖R‖)⁻¹ * (‖R‖ * (1 - ‖V‖)⁻¹ + ‖W‖ * ‖R‖ + ‖D‖ * ‖R‖ +
        ‖ηp‖ * ‖(Q : ℂ) - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ * (1 - ‖V‖)⁻¹)) ≤ 31 * T := by
    have := mul_le_mul hvw' he (by positivity) (by norm_num)
    linarith
  have id : (1 - ‖D‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  rw [div_eq_mul_inv]
  calc _ ≤ 31 * T * 2 := mul_le_mul hnum id (inv_nonneg.mpr (by linarith)) (by positivity)
    _ ≤ 80 * T := by linarith

/-- **The correction on the region of the contour moves.** At a good prime of norm `Q ≥ 7`, on
`Re x ≥ 51/100`, `Re w ≥ −1/100`, `Re(x + w) ≥ 1 + ε₀`, `Re z ≥ 17/50` (`‖X‖ ≤ Q^{−x_r}`,
`‖Y‖, ‖W‖ ≤ Q^{−w_r}`, `‖V‖ ≤ Q^{−51/25}`), with `0 < ε₀ ≤ 2/25`:
`‖H − 1‖ ≤ 80 Q^{−1−ε₀}`. The binding terms are `DW` and `(1 − W) R`; no factor `(1 − W)⁻¹`
occurs, so `|W| > 1` is allowed. -/
theorem norm_rowH_sub_one_le_D1 {Q ε₀ xr wr : ℝ} (hQ : 7 ≤ Q) (hε : 0 < ε₀)
    (hε' : ε₀ ≤ 2 / 25) (hxr : 51 / 100 ≤ xr) (hwr : -(1 / 100) ≤ wr) (hxw : 1 + ε₀ ≤ xr + wr)
    {ηp X Y V R W D : ℂ} (hX : ‖X‖ ≤ Q ^ (-xr)) (hY : ‖Y‖ ≤ Q ^ (-wr)) (hW : ‖W‖ ≤ Q ^ (-wr))
    (hV : ‖V‖ ≤ Q ^ (-(51 / 25 : ℝ))) (hD : ‖D‖ ≤ ‖X‖) (hR : ‖R‖ ≤ Q ^ 4 * ‖X‖ ^ 6 * ‖V‖)
    (hη : ‖ηp‖ ≤ 1) :
    ‖rowH (Q : ℂ) ηp X Y V R W D - 1‖ ≤ 80 * Q ^ (-(1 + ε₀)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  set T := Q ^ (-(1 + ε₀))
  have hT0 : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hpow : ∀ a : ℝ, a ≤ -(1 + ε₀) → Q ^ a ≤ T := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hQ1 ha
  -- sizes
  have hx2 : ‖X‖ ≤ 1 / 2 := hX.trans ((Real.rpow_le_rpow_of_exponent_le hQ1
    (by linarith : -xr ≤ -(1 / 2))).trans (rpow_le_half_of_four_le hQ4 le_rfl))
  have hv2 : ‖V‖ ≤ 1 / 2 := hV.trans (rpow_le_half_of_four_le hQ4 (by norm_num))
  have hd2 : ‖D‖ ≤ 1 / 2 := hD.trans hx2
  have hw1 : ‖W‖ ≤ Q ^ (1 / 100 : ℝ) :=
    hW.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hV1 : ‖V‖ ≤ 1 := by linarith
  -- `R ≤ Q^{−11/10}`
  have hRb : ‖R‖ ≤ Q ^ (-(11 / 10 : ℝ)) := by
    refine hR.trans ?_
    calc Q ^ 4 * ‖X‖ ^ 6 * ‖V‖ ≤ Q ^ 4 * (Q ^ (-xr)) ^ 6 * Q ^ (-(51 / 25 : ℝ)) := by gcongr
      _ = Q ^ ((4 : ℝ) + (-xr) * 6 + (-(51 / 25 : ℝ))) := by
          rw [Real.rpow_add hQ0, Real.rpow_add hQ0, Real.rpow_mul hQ0.le]
          norm_cast
      _ ≤ Q ^ (-(11 / 10 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hr2 : ‖R‖ ≤ 1 / 2 := hRb.trans (rpow_le_half_of_four_le hQ4 (by norm_num))
  have hrT : ‖R‖ ≤ T := hRb.trans (hpow _ (by linarith))
  have hwr : ‖W‖ * ‖R‖ ≤ T := (mul_le_mul hw1 hRb (norm_nonneg _) (by positivity)).trans
    ((rpow_mul_rpow_le_of_add_le hQ1 le_rfl).trans (hpow _ (by linarith)))
  have hwwr : ‖W‖ * (‖W‖ * ‖R‖) ≤ T := by
    calc ‖W‖ * (‖W‖ * ‖R‖) ≤ Q ^ (1 / 100 : ℝ) * (Q ^ (1 / 100 : ℝ) * Q ^ (-(11 / 10 : ℝ))) := by
          gcongr
      _ = Q ^ ((1 / 100 : ℝ) + ((1 / 100 : ℝ) + (-(11 / 10 : ℝ)))) := by
          rw [Real.rpow_add hQ0, Real.rpow_add hQ0]
      _ ≤ T := hpow _ (by linarith)
  -- the products
  have hdv : ‖D‖ * ‖V‖ ≤ T := (mul_le_mul (hD.trans hX) hV (norm_nonneg _)
    (Real.rpow_nonneg hQ0.le _)).trans
      ((rpow_mul_rpow_le_of_add_le hQ1 le_rfl).trans (hpow _ (by linarith)))
  have hdw : ‖D‖ * ‖W‖ ≤ T := (mul_le_mul (hD.trans hX) hW (norm_nonneg _)
    (Real.rpow_nonneg hQ0.le _)).trans
      ((rpow_mul_rpow_le_of_add_le hQ1 le_rfl).trans (hpow _ (by linarith)))
  have hvw : ‖V‖ * ‖W‖ ≤ T := (mul_le_mul hV hW (norm_nonneg _)
    (Real.rpow_nonneg hQ0.le _)).trans
      ((rpow_mul_rpow_le_of_add_le hQ1 le_rfl).trans (hpow _ (by linarith)))
  have hdvw : ‖D‖ * ‖V‖ * ‖W‖ ≤ T := by
    calc ‖D‖ * ‖V‖ * ‖W‖ = ‖D‖ * ‖W‖ * ‖V‖ := by ring
      _ ≤ T * 1 := mul_le_mul hdw hV1 (norm_nonneg _) hT0
      _ = T := mul_one T
  have hQm1 : ‖(Q : ℂ) - 1‖ ≤ Q := by
    rw [show (Q : ℂ) - 1 = ((Q - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hPb : ‖ηp‖ * ‖(Q : ℂ) - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ ≤ Q ^ (-(51 / 25 : ℝ) - ε₀) := by
    calc ‖ηp‖ * ‖(Q : ℂ) - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ ≤
        1 * Q * Q ^ (-xr) * Q ^ (-wr) * Q ^ (-(51 / 25 : ℝ)) := by gcongr
      _ = Q ^ ((1 : ℝ) + -xr + -wr + (-(51 / 25 : ℝ))) := by
          rw [Real.rpow_add hQ0, Real.rpow_add hQ0, Real.rpow_add hQ0, Real.rpow_one, one_mul]
      _ ≤ Q ^ (-(51 / 25 : ℝ) - ε₀) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hP : ‖ηp‖ * ‖(Q : ℂ) - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ ≤ T := hPb.trans (hpow _ (by linarith))
  have hwP : ‖W‖ * (‖ηp‖ * ‖(Q : ℂ) - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖) ≤ T :=
    (mul_le_mul hw1 hPb (by positivity) (by positivity)).trans
      ((rpow_mul_rpow_le_of_add_le hQ1 le_rfl).trans (hpow _ (by linarith)))
  have hq : ‖1 - ((Q : ℂ))⁻¹‖ ≤ 1 := by
    rw [show (1 : ℂ) - (Q : ℂ)⁻¹ = ((1 - Q⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    have : 0 < Q⁻¹ := inv_pos.mpr hQ0
    have : Q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ1
    constructor <;> linarith
  refine (norm_rowH_sub_one_le (Q : ℂ) ηp X Y V R W D (by linarith) (by linarith) (by linarith)
    hq).trans ?_
  have iv : (1 - ‖V‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have ir : (1 - ‖R‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have id : (1 - ‖D‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have iv0 : 0 ≤ (1 - ‖V‖)⁻¹ := inv_nonneg.mpr (by linarith)
  have ir0 : 0 ≤ (1 - ‖R‖)⁻¹ := inv_nonneg.mpr (by linarith)
  set P := ‖ηp‖ * ‖(Q : ℂ) - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖
  set e := (1 - ‖R‖)⁻¹ * (‖R‖ * (1 - ‖V‖)⁻¹ + ‖W‖ * ‖R‖ + ‖D‖ * ‖R‖ + P * (1 - ‖V‖)⁻¹)
  have hP' : ‖ηp‖ * ‖(Q : ℂ) - 1‖ * ‖X‖ * ‖Y‖ * ‖V‖ * (1 - ‖V‖)⁻¹ = P * (1 - ‖V‖)⁻¹ := rfl
  -- `(1 + ‖W‖) e ≤ 24 T`
  have hdr : ‖D‖ * ‖R‖ ≤ ‖R‖ := mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have hinner : ‖R‖ * (1 - ‖V‖)⁻¹ + ‖W‖ * ‖R‖ + ‖D‖ * ‖R‖ + P * (1 - ‖V‖)⁻¹ ≤
      3 * ‖R‖ + ‖W‖ * ‖R‖ + 2 * P := by
    have := mul_le_mul_of_nonneg_left iv (norm_nonneg R)
    have := mul_le_mul_of_nonneg_left iv (show 0 ≤ P by positivity)
    linarith
  have he : e ≤ 2 * (3 * ‖R‖ + ‖W‖ * ‖R‖ + 2 * P) :=
    mul_le_mul ir hinner (by positivity) (by norm_num)
  have hwe : (1 + ‖W‖) * e ≤ 2 * (3 * T + T + 2 * T) + 2 * (3 * T + T + 2 * T) := by
    have h1 : (1 + ‖W‖) * e ≤ (1 + ‖W‖) * (2 * (3 * ‖R‖ + ‖W‖ * ‖R‖ + 2 * P)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    have h2 : (1 + ‖W‖) * (2 * (3 * ‖R‖ + ‖W‖ * ‖R‖ + 2 * P)) =
        2 * (3 * ‖R‖ + ‖W‖ * ‖R‖ + 2 * P) +
          2 * (3 * (‖W‖ * ‖R‖) + ‖W‖ * (‖W‖ * ‖R‖) + 2 * (‖W‖ * P)) := by ring
    linarith
  have hnum : ‖D‖ * ‖V‖ + ‖D‖ * ‖W‖ + ‖D‖ * ‖V‖ * ‖W‖ + ‖V‖ * ‖W‖ + (1 + ‖V‖) * (1 + ‖W‖) * e ≤
      40 * T := by
    have h3 : (1 + ‖V‖) * (1 + ‖W‖) * e ≤ 3 / 2 * (24 * T) := by
      rw [mul_assoc]
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    linarith
  rw [div_eq_mul_inv]
  calc _ ≤ 40 * T * 2 := mul_le_mul hnum id (inv_nonneg.mpr (by linarith)) (by positivity)
    _ ≤ 80 * T := by linarith

end GaloisForLFunctions.FamilyContinuationTheory
