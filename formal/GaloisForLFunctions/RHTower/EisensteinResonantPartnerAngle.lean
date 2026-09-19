import GaloisForLFunctions.RHTower.EisensteinResonantStateNorm

/-!
# The partner angle law of resonant states

For a zero `ρ` of `Λ` in the strip (`Im ρ > 0`) the reflected point `ρ' = 1 − conj ρ` is again a
zero, and its resonant state `E*(·, ρ'/2)` is the complex conjugate of the functional-equation
partner `E*(·, (1+ρ)/2) = E*(·, (1−ρ)/2)` of `E*(·, ρ/2)`.  On the critical line `ρ' = ρ` and the
two states coincide; off the line they are distinct eigenfunctions of the Laplacian.

The Maass–Selberg relation gives the exact Hermitian pairing of the two truncated states,
`⟨Λ^Y E*(·,ρ/2), Λ^Y E*(·,ρ'/2)⟩ = 2 Λ(ρ−1) Λ(1+ρ) √Y`, and the exact norms
`‖Λ(ρ−1)‖² Y^{1−Re ρ}/(1−Re ρ)` and `‖Λ(1+ρ)‖² Y^{Re ρ}/Re ρ`.  Hence the squared cosine of the
angle between the two truncated states is `4 Re ρ (1 − Re ρ) = 1 − (2 Re ρ − 1)²`, independent of
the height `Y` and of the values of `Λ`: the sine of the partner angle is the functional-equation
tilt `|2 Re ρ − 1|`, and the Cauchy–Schwarz inequality is saturated exactly at zeros on the line.
-/

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The Hermitian pairing `∫_𝒟 Λ^Y E_u · conj (Λ^Y E_v) dμ` of two truncated line models. -/
def hermitianPairing (Y : ℝ) (u v : ℂ) : ℂ :=
  ∫ z in fd, truncatedLineModel u Y z * (starRingEnd ℂ) (truncatedLineModel v Y z)

/-- The reflected zero `1 − conj ρ` is a zero of `Λ`. -/
theorem reflectedCompletedLambda_one_sub_conj_eq_zero {ρ : ℂ} (hρ : reflectedCompletedLambda ρ = 0)
    (him : ρ.im ≠ 0) : reflectedCompletedLambda (1 - (starRingEnd ℂ) ρ) = 0 := by
  rw [reflectedCompletedLambda_one_sub_of_im (by simp [him]), reflectedCompletedLambda_conj, hρ,
    map_zero]

/-- The parameter of the reflected zero's state is `−conj(ρ/2)`. -/
theorem conj_resonantParameter_one_sub_conj (ρ : ℂ) :
    (starRingEnd ℂ) (resonantParameter (1 - (starRingEnd ℂ) ρ)) = -(ρ / 2) := by
  unfold resonantParameter
  simp only [map_sub, map_div₀, map_one, map_ofNat, Complex.conj_conj]
  ring

/-- **The Hermitian pairing with the reflected zero's state is the bilinear pairing with the
functional-equation partner `E*(·, (1+ρ)/2)`.** -/
theorem hermitianPairing_reflected_eq {ρ : ℂ} (him : ρ.im ≠ 0) (Y : ℝ) :
    hermitianPairing Y (resonantParameter ρ) (resonantParameter (1 - (starRingEnd ℂ) ρ)) =
      truncatedPairing Y (resonantParameter ρ) (ρ / 2) := by
  unfold hermitianPairing truncatedPairing
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  have h2 : (ρ / 2).im ≠ 0 := by simp [him]
  rw [truncatedLineModel_conj, conj_resonantParameter_one_sub_conj, truncatedLineModel_neg h2]

/-- **The Maass–Selberg value of the partner pairing.** -/
theorem truncatedPairing_partner {ρ : ℂ} (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re)
    (him : 0 < ρ.im) {Y : ℝ} (hY : 1 ≤ Y) :
    truncatedPairing Y (resonantParameter ρ) (ρ / 2) =
      2 * reflectedCompletedLambda (ρ - 1) * reflectedCompletedLambda (1 + ρ) *
        (Y : ℂ) ^ ((1 : ℂ) / 2) := by
  have hu : resonantParameter ρ ∈ eisensteinLineDomain := resonantParameter_mem h0 him
  have hv : ρ / 2 ∈ eisensteinLineDomain := ⟨by simp; linarith, by simp; linarith⟩
  have h := maassSelberg_lineModel hu hv hY
  have hAu : msA (resonantParameter ρ) = 0 := by rw [msA_resonantParameter]; exact hρ
  have hBv : msB (ρ / 2) = 0 := by
    unfold msB; rw [show (2 : ℂ) * (ρ / 2) = ρ by ring]; exact hρ
  have hAv : msA (ρ / 2) = reflectedCompletedLambda (1 + ρ) := by
    unfold msA; congr 1; ring
  have hBu := msB_resonantParameter ρ
  have hsub : resonantParameter ρ - ρ / 2 = -(1 / 2 : ℂ) := by unfold resonantParameter; ring
  have hadd : resonantParameter ρ + ρ / 2 = ρ - 1 / 2 := by unfold resonantParameter; ring
  have hsub' : ρ / 2 - resonantParameter ρ = (1 : ℂ) / 2 := by unfold resonantParameter; ring
  unfold msRight at h
  rw [hAu, hBv, hAv, hBu, hsub, hadd, hsub'] at h
  have hne : ρ - 1 / 2 ≠ 0 := by
    intro h'
    have := congrArg Complex.im h'
    simp at this
    linarith
  have key : (ρ - 1 / 2) * (-(1 / 2 : ℂ) * truncatedPairing Y (resonantParameter ρ) (ρ / 2) +
      reflectedCompletedLambda (ρ - 1) * reflectedCompletedLambda (1 + ρ) *
        (Y : ℂ) ^ ((1 : ℂ) / 2)) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp key with h' | h'
  · exact absurd h' hne
  · linear_combination -2 * h'

/-- **The truncated norm of the reflected zero's state.** -/
theorem integral_norm_sq_reflectedState {ρ : ℂ} (hρ : reflectedCompletedLambda ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : 0 < ρ.im) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in fd, ‖truncatedLineModel (resonantParameter (1 - (starRingEnd ℂ) ρ)) Y z‖ ^ 2 =
      ‖reflectedCompletedLambda (1 + ρ)‖ ^ 2 * Y ^ ρ.re / ρ.re := by
  have hρ' := reflectedCompletedLambda_one_sub_conj_eq_zero hρ him.ne'
  have h := integral_norm_sq_resonantState hρ' (by simp; linarith) (by simp; linarith)
    (by simp; linarith) hY
  rw [h]
  have e1 : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by simp
  have e2 : reflectedCompletedLambda (1 - (starRingEnd ℂ) ρ - 1) =
      (starRingEnd ℂ) (reflectedCompletedLambda (1 + ρ)) := by
    rw [← reflectedCompletedLambda_conj, map_add, map_one]
    have := reflectedCompletedLambda_one_sub_of_im (s := 1 + (starRingEnd ℂ) ρ) (by simp [him.ne'])
    rw [← this]; congr 1; ring
  rw [e1, e2, Complex.norm_conj]
  congr 2 <;> ring_nf

/-- **The partner angle law.** For every zero `ρ` of `Λ` in the strip with `Im ρ > 0` and every
`Y ≥ 1`, the squared Hermitian pairing of the truncated resonant states of `ρ` and of the
reflected zero `1 − conj ρ` equals `4 Re ρ (1 − Re ρ)` times the product of their squared norms.
The ratio is independent of `Y` and of the values of `Λ`. -/
theorem partner_angle_law {ρ : ℂ} (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (him : 0 < ρ.im) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖hermitianPairing Y (resonantParameter ρ) (resonantParameter (1 - (starRingEnd ℂ) ρ))‖ ^ 2 =
      4 * ρ.re * (1 - ρ.re) *
        ((∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2) *
          ∫ z in fd, ‖truncatedLineModel (resonantParameter (1 - (starRingEnd ℂ) ρ)) Y z‖ ^ 2) := by
  have hYpos : 0 < Y := by linarith
  rw [hermitianPairing_reflected_eq him.ne', truncatedPairing_partner hρ h0 him hY,
    integral_norm_sq_resonantState hρ h0 h1 him hY, integral_norm_sq_reflectedState hρ h0 h1 him hY]
  have hpow : ‖(Y : ℂ) ^ ((1 : ℂ) / 2)‖ ^ 2 = Y := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    have : ((1 : ℂ) / 2).re = (1 : ℝ) / 2 := by simp
    rw [this, ← Real.rpow_natCast, ← Real.rpow_mul hYpos.le]
    norm_num
  have hYY : Y ^ (1 - ρ.re) * Y ^ ρ.re = Y := by
    rw [← Real.rpow_add hYpos]; simp
  rw [norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow, hpow]
  have hre : ρ.re ≠ 0 := h0.ne'
  have hre' : 1 - ρ.re ≠ 0 := by linarith
  have hY2 : Y ^ ρ.re = Y / Y ^ (1 - ρ.re) := by
    rw [eq_div_iff (Real.rpow_pos_of_pos hYpos _).ne', mul_comm]; exact hYY
  rw [hY2, show ‖(2 : ℂ)‖ = 2 by simp]
  field_simp
  ring

/-- The partner angle law in tilt form: `cos² = 1 − (2 Re ρ − 1)²`. -/
theorem partner_angle_tilt {ρ : ℂ} (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (him : 0 < ρ.im) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖hermitianPairing Y (resonantParameter ρ) (resonantParameter (1 - (starRingEnd ℂ) ρ))‖ ^ 2 =
      (1 - (2 * ρ.re - 1) ^ 2) *
        ((∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2) *
          ∫ z in fd, ‖truncatedLineModel (resonantParameter (1 - (starRingEnd ℂ) ρ)) Y z‖ ^ 2) := by
  rw [partner_angle_law hρ h0 h1 him hY]; ring

/-- The product of the two truncated norms is positive. -/
theorem partner_norms_pos {ρ : ℂ} (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (him : 0 < ρ.im) {Y : ℝ} (hY : 1 ≤ Y) :
    0 < (∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2) *
          ∫ z in fd, ‖truncatedLineModel (resonantParameter (1 - (starRingEnd ℂ) ρ)) Y z‖ ^ 2 := by
  have hYpos : 0 < Y := by linarith
  rw [integral_norm_sq_resonantState hρ h0 h1 him hY, integral_norm_sq_reflectedState hρ h0 h1 him hY]
  have hn1 := reflectedCompletedLambda_sub_one_ne_zero h1 him.ne'
  have hn2 : reflectedCompletedLambda (1 + ρ) ≠ 0 := by
    unfold reflectedCompletedLambda
    apply mul_ne_zero
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    · exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hp1 : 0 < ‖reflectedCompletedLambda (ρ - 1)‖ := norm_pos_iff.mpr hn1
  have hp2 : 0 < ‖reflectedCompletedLambda (1 + ρ)‖ := norm_pos_iff.mpr hn2
  have hr1 : 0 < 1 - ρ.re := by linarith
  have hY1 : 0 < Y ^ (1 - ρ.re) := Real.rpow_pos_of_pos hYpos _
  have hY2 : 0 < Y ^ ρ.re := Real.rpow_pos_of_pos hYpos _
  positivity

/-- **Cauchy–Schwarz is saturated exactly on the critical line:** the truncated resonant states of
`ρ` and of `1 − conj ρ` are parallel if and only if `Re ρ = 1/2`. -/
theorem partner_saturation_iff {ρ : ℂ} (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (him : 0 < ρ.im) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖hermitianPairing Y (resonantParameter ρ) (resonantParameter (1 - (starRingEnd ℂ) ρ))‖ ^ 2 =
      (∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2) *
          (∫ z in fd, ‖truncatedLineModel (resonantParameter (1 - (starRingEnd ℂ) ρ)) Y z‖ ^ 2) ↔
      ρ.re = 1 / 2 := by
  rw [partner_angle_tilt hρ h0 h1 him hY]
  have hpos := partner_norms_pos hρ h0 h1 him hY
  constructor
  · intro h
    have h' : (2 * ρ.re - 1) ^ 2 * ((∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2) *
        ∫ z in fd, ‖truncatedLineModel (resonantParameter (1 - (starRingEnd ℂ) ρ)) Y z‖ ^ 2) = 0 := by
      linear_combination -h
    rcases mul_eq_zero.mp h' with h'' | h''
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h''
      linarith
    · exact absurd h'' hpos.ne'
  · intro h
    rw [h]; ring

end

end RHTower
