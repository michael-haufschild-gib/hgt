import GaloisForLFunctions.RHTower.XiHorizontalLogDerivativeModel
import GaloisForLFunctions.HTGeometry.LogLinearGronwallModel

/-!
# The archimedean factor of `ξ` along vertical lines

`G(w) = w(w−1)/2 · π^{−w/2} Γ(w/2)` is the archimedean factor of `ξ = G ζ` (`xi_eq_archG_mul_zeta`).
On `1 ≤ Re w ≤ 3`, Stirling's formula for the digamma function gives, with
`L_T = ½ log(T/2π) + iπ/4` (`horizontalSlope T`),

`‖G'/G(σ + iX) − L_T‖ ≤ (12 + |X − T|)/T`   for `|X − T| ≤ T/2`, `T ≥ 48`

(`norm_logDeriv_archG_sub_slope_le`), hence the vertical log-linear model

`‖G(w₁ + iu) − G(w₁) e^{iuL_T}‖ ≤ ‖G(w₁)‖ e^{−πu/4} (e^{η|u|} − 1)`,   `η = (12 + |Im w₁ − T| + V)/T`

for `|u| ≤ V` (`norm_archG_vertical_sub_model_le`), and the lower bound
`‖G(σ + iT)‖ ≥ m e^{−(T−24)(log T + 2)}` on `3/2 ≤ σ ≤ 5/2` (`exists_norm_archG_lower`).
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The archimedean factor `G(w) = w(w−1)/2 · π^{−w/2} Γ(w/2)`. -/
def archG (w : ℂ) : ℂ := w * (w - 1) / 2 * ((Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2))

theorem xi_eq_archG_mul_zeta {w : ℂ} (hw : 1 < w.re) : xi w = archG w * riemannZeta w := by
  rw [xi_eq_four_factors hw, archG]; ring

theorem half_ne_neg_natCast {w : ℂ} (hw : 0 < w.re) : ∀ m : ℕ, w / 2 ≠ -m := by
  intro m h
  have hre : (w / 2).re = -(m : ℝ) := by rw [h]; simp
  have : (w / 2).re = w.re / 2 := by simp
  rw [this] at hre
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

private theorem ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : w ≠ 0 := by
  rintro rfl; simp at hw

theorem archG_ne_zero {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) : archG w ≠ 0 := by
  have hπne : ((Real.pi : ℂ) ^ (-w / 2)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (by simp [Real.pi_ne_zero])
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (ne_zero_of_re_pos hw) (sub_ne_zero.mpr hw1))
    two_ne_zero) (mul_ne_zero hπne (Complex.Gamma_ne_zero (half_ne_neg_natCast hw)))

theorem differentiableAt_archG {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ archG w := by
  have hdπ : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) w :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by simp [Real.pi_ne_zero]))
  have hdΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) w :=
    (Complex.differentiableAt_Gamma (w / 2) (half_ne_neg_natCast hw)).comp w (by fun_prop)
  unfold archG
  exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) / 2) w).mul (hdπ.mul hdΓ)

/-- `G'/G(w) = 1/w + 1/(w−1) − ½ log π + ½ ψ(w/2)` on `Re w > 0`, `w ≠ 1`. -/
theorem logDeriv_archG {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    logDeriv archG w = 1 / w + 1 / (w - 1) - (Real.log Real.pi : ℂ) / 2 +
      Complex.digamma (w / 2) / 2 := by
  have hw0 := ne_zero_of_re_pos hw
  have hhalf := half_ne_neg_natCast hw
  have hπne : ((Real.pi : ℂ) ^ (-w / 2)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (by simp [Real.pi_ne_zero])
  have hΓne : Complex.Gamma (w / 2) ≠ 0 := Complex.Gamma_ne_zero hhalf
  have hqne : w * (w - 1) / 2 ≠ 0 := div_ne_zero (mul_ne_zero hw0 (sub_ne_zero.mpr hw1)) two_ne_zero
  have hdq : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) / 2) w := by fun_prop
  have hdπ : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) w :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by simp [Real.pi_ne_zero]))
  have hdΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) w :=
    (Complex.differentiableAt_Gamma (w / 2) hhalf).comp w (by fun_prop)
  unfold archG
  rw [logDeriv_mul (f := fun z : ℂ => z * (z - 1) / 2)
      (g := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2))
      w hqne (mul_ne_zero hπne hΓne) hdq (hdπ.mul hdΓ),
    logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      (g := fun z : ℂ => Complex.Gamma (z / 2)) w hπne hΓne hdπ hdΓ,
    logDeriv_quadratic hw0 hw1, logDeriv_piPow w, logDeriv_gammaHalf hhalf]
  ring

/-- The slope decomposition of `G'/G` at `σ + iX`. -/
theorem logDeriv_archG_sub_horizontalSlope_eq {σ X : ℝ} (hσ : 0 < σ) (hX : 0 < X) :
    logDeriv archG ((σ : ℂ) + X * I) - horizontalSlope X =
      Complex.log (1 - I * (σ / X : ℝ)) / 2 +
        (1 / ((σ : ℂ) + X * I) + 1 / ((σ : ℂ) + X * I - 1) - 1 / (2 * ((σ : ℂ) + X * I)) +
          GaloisForLFunctions.HTGeometry.digammaStirlingDefect (((σ : ℂ) + X * I) / 2) / 2) := by
  set s : ℂ := (σ : ℂ) + X * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = X := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  rw [logDeriv_archG (by rw [hsre]; exact hσ) hs1]
  have hdig : Complex.digamma (s / 2) =
      GaloisForLFunctions.HTGeometry.digammaStirlingDefect (s / 2) + Complex.log (s / 2) -
        1 / (2 * (s / 2)) := by
    rw [GaloisForLFunctions.HTGeometry.digammaStirlingDefect]
    ring
  rw [hdig, hs, log_horizontalPoint_half_eq hX, horizontalSlope,
    Real.log_div (by positivity) (by positivity), Real.log_div hX.ne' (by norm_num),
    Real.log_mul (by norm_num) Real.pi_pos.ne']
  rw [← hs]
  have h2 : (2 : ℂ) * (s / 2) = s := by ring
  rw [h2]
  push_cast
  ring_nf

theorem norm_log_one_add_le_two_mul {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 + z)‖ ≤ 2 * ‖z‖ := by
  have h := Complex.norm_log_one_add_sub_self_le (z := z) (by linarith)
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h2 : ‖Complex.log (1 + z)‖ ≤ ‖z‖ + ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
    have := norm_add_le (Complex.log (1 + z) - z) z
    rw [sub_add_cancel] at this
    linarith
  have h3 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ := by
    have : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ ≤ ‖z‖ ^ 2 * 2 := by gcongr
    nlinarith [norm_nonneg z]
  linarith

/-- `‖G'/G(σ + iX) − L_X‖ ≤ 6/X` on `1 ≤ σ ≤ 3`, `X ≥ 24`. -/
theorem norm_logDeriv_archG_sub_horizontalSlope_le {σ X : ℝ} (hσ1 : 1 ≤ σ) (hσ3 : σ ≤ 3)
    (hX : 24 ≤ X) : ‖logDeriv archG ((σ : ℂ) + X * I) - horizontalSlope X‖ ≤ 6 / X := by
  have hX0 : 0 < X := by linarith
  rw [logDeriv_archG_sub_horizontalSlope_eq (by linarith) hX0]
  set s : ℂ := (σ : ℂ) + X * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = X := by simp [hs]
  have hsX : X ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s
    rwa [hsim, abs_of_pos hX0] at this
  have hs1X : X ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    rwa [Complex.sub_im, hsim, Complex.one_im, sub_zero, abs_of_pos hX0] at this
  have hs2 : X / 2 ≤ ‖s / 2‖ := by
    rw [norm_div, Complex.norm_ofNat]; linarith
  have h1 : ‖1 / s‖ ≤ 1 / X := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le hX0 hsX
  have h2 : ‖1 / (s - 1)‖ ≤ 1 / X := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le hX0 hs1X
  have h3 : ‖1 / (2 * s)‖ ≤ 1 / (2 * X) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hD := GaloisForLFunctions.HTGeometry.norm_digammaStirlingDefect_le
    (z := s / 2) (by simp [hsre]; linarith) (by linarith)
  have h4 : ‖GaloisForLFunctions.HTGeometry.digammaStirlingDefect (s / 2) / 2‖ ≤ 12 / X ^ 2 := by
    rw [norm_div, Complex.norm_ofNat]
    have hsq : (X / 2) ^ 2 ≤ ‖s / 2‖ ^ 2 := by gcongr
    have : 6 / ‖s / 2‖ ^ (2 : ℕ) ≤ 6 / (X / 2) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    calc ‖GaloisForLFunctions.HTGeometry.digammaStirlingDefect (s / 2)‖ / 2
        ≤ 6 / (X / 2) ^ 2 / 2 := by gcongr; exact hD.trans this
      _ = 12 / X ^ 2 := by field_simp; ring
  have h5 : ‖Complex.log (1 - I * (σ / X : ℝ)) / 2‖ ≤ 3 / X := by
    have hz : ‖-(I * (σ / X : ℝ))‖ = σ / X := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    have hsm : σ / X ≤ 1 / 2 := by rw [div_le_iff₀ hX0]; linarith
    have hl := norm_log_one_add_le_two_mul (z := -(I * (σ / X : ℝ))) (by rw [hz]; exact hsm)
    rw [← sub_eq_add_neg, hz] at hl
    rw [norm_div, Complex.norm_ofNat]
    have : σ / X ≤ 3 / X := by gcongr
    linarith
  have hsmall : 1 / X + 1 / X + 1 / (2 * X) + 12 / X ^ 2 ≤ 3 / X := by
    have e : 1 / X + 1 / X + 1 / (2 * X) + 12 / X ^ 2 = (5 * X + 24) / (2 * X ^ 2) := by
      field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) hX0]
    nlinarith
  calc ‖Complex.log (1 - I * (σ / X : ℝ)) / 2 + (1 / s + 1 / (s - 1) - 1 / (2 * s) +
        GaloisForLFunctions.HTGeometry.digammaStirlingDefect (s / 2) / 2)‖
      ≤ ‖Complex.log (1 - I * (σ / X : ℝ)) / 2‖ + (‖1 / s‖ + ‖1 / (s - 1)‖ + ‖1 / (2 * s)‖ +
          ‖GaloisForLFunctions.HTGeometry.digammaStirlingDefect (s / 2) / 2‖) := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 3 / X + (1 / X + 1 / X + 1 / (2 * X) + 12 / X ^ 2) := by gcongr
    _ ≤ 3 / X + 3 / X := by gcongr
    _ = 6 / X := by ring

theorem abs_log_div_le {X T : ℝ} (hT : 0 < T) (h : |X - T| ≤ T / 2) :
    |Real.log (X / T)| ≤ 2 * |X - T| / T := by
  have hX : T / 2 ≤ X := by have := (abs_le.mp h).1; linarith
  have hX0 : X ≠ 0 := by intro h0; rw [h0] at hX; linarith
  have hXpos : 0 < X / T := by apply div_pos <;> linarith
  rw [abs_le]
  constructor
  · have h1 := Real.one_sub_inv_le_log_of_pos hXpos
    have e : 1 - (X / T)⁻¹ = (X - T) / X := by field_simp
    have h2 : -(2 * |X - T| / T) ≤ (X - T) / X := by
      rw [neg_le, ← neg_div, div_le_div_iff₀ (by linarith) hT]
      have := neg_abs_le (X - T)
      nlinarith [abs_nonneg (X - T)]
    linarith
  · have h1 := Real.log_le_sub_one_of_pos hXpos
    have e : X / T - 1 = (X - T) / T := by field_simp
    have h2 : (X - T) / T ≤ 2 * |X - T| / T := by
      gcongr; linarith [le_abs_self (X - T), abs_nonneg (X - T)]
    linarith

/-- **The slope at the reference height.** -/
theorem norm_logDeriv_archG_sub_slope_le {σ X T : ℝ} (hσ1 : 1 ≤ σ) (hσ3 : σ ≤ 3)
    (hT : 48 ≤ T) (hXT : |X - T| ≤ T / 2) :
    ‖logDeriv archG ((σ : ℂ) + X * I) - horizontalSlope T‖ ≤ (12 + |X - T|) / T := by
  have hT0 : 0 < T := by linarith
  have hX : T / 2 ≤ X := by have := (abs_le.mp hXT).1; linarith
  have hX24 : 24 ≤ X := by linarith
  have h1 := norm_logDeriv_archG_sub_horizontalSlope_le hσ1 hσ3 hX24
  have h6 : 6 / X ≤ 12 / T := by
    rw [div_le_div_iff₀ (by linarith) hT0]; linarith
  have hslope : horizontalSlope X - horizontalSlope T = ((Real.log (X / T) / 2 : ℝ) : ℂ) := by
    simp only [horizontalSlope]
    rw [Real.log_div (by linarith) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_div (by linarith) hT0.ne']
    push_cast; ring
  have h2 : ‖horizontalSlope X - horizontalSlope T‖ ≤ |X - T| / T := by
    rw [hslope, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    have := abs_log_div_le hT0 hXT
    rw [div_le_div_iff₀ two_pos hT0]
    rw [le_div_iff₀ hT0] at this
    linarith
  calc ‖logDeriv archG ((σ : ℂ) + X * I) - horizontalSlope T‖
      ≤ ‖logDeriv archG ((σ : ℂ) + X * I) - horizontalSlope X‖ +
          ‖horizontalSlope X - horizontalSlope T‖ := by
        rw [← sub_add_sub_cancel _ (horizontalSlope X)]; exact norm_add_le _ _
    _ ≤ 12 / T + |X - T| / T := by linarith
    _ = (12 + |X - T|) / T := by ring

theorem norm_horizontalSlope_le {X : ℝ} (hX : 24 ≤ X) : ‖horizontalSlope X‖ ≤ Real.log X / 2 + 1 := by
  simp only [horizontalSlope]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
    norm_div, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have h1 : 0 ≤ Real.log (X / (2 * Real.pi)) := Real.log_nonneg (by
    rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_d2])
  have h2 : Real.log (X / (2 * Real.pi)) ≤ Real.log X :=
    Real.log_le_log (by positivity) (div_le_self (by linarith) (by nlinarith [Real.pi_gt_three]))
  rw [abs_of_nonneg (by positivity)]
  have := Real.pi_lt_d2
  linarith

/-- `‖G'/G(σ + iX)‖ ≤ log X + 2` on `1 ≤ σ ≤ 3`, `X ≥ 24`. -/
theorem norm_logDeriv_archG_le {σ X : ℝ} (hσ1 : 1 ≤ σ) (hσ3 : σ ≤ 3) (hX : 24 ≤ X) :
    ‖logDeriv archG ((σ : ℂ) + X * I)‖ ≤ Real.log X + 2 := by
  have h1 := norm_logDeriv_archG_sub_horizontalSlope_le hσ1 hσ3 hX
  have h2 := norm_horizontalSlope_le hX
  have h3 : 6 / X ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h4 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  calc ‖logDeriv archG ((σ : ℂ) + X * I)‖
      ≤ ‖logDeriv archG ((σ : ℂ) + X * I) - horizontalSlope X‖ + ‖horizontalSlope X‖ := by
        have := norm_sub_norm_le (logDeriv archG ((σ : ℂ) + X * I)) (horizontalSlope X)
        linarith
    _ ≤ Real.log X + 2 := by linarith

/-! ## Vertical models -/

theorem hasDerivAt_archG_vertical {σ X₁ : ℝ} (hσ : 0 < σ) (v : ℝ) :
    HasDerivAt (fun u : ℝ => archG ((σ : ℂ) + X₁ * I + u * I))
      (deriv archG ((σ : ℂ) + X₁ * I + v * I) * I) v := by
  have hre : 0 < ((σ : ℂ) + X₁ * I + v * I).re := by simp [hσ]
  have h1 : HasDerivAt (fun w : ℂ => archG ((σ : ℂ) + X₁ * I + w * I))
      (deriv archG ((σ : ℂ) + X₁ * I + v * I) * I) (v : ℂ) := by
    have hinner : HasDerivAt (fun w : ℂ => (σ : ℂ) + X₁ * I + w * I) I (v : ℂ) := by
      simpa using ((hasDerivAt_id (v : ℂ)).mul_const I).const_add ((σ : ℂ) + X₁ * I)
    exact (differentiableAt_archG hre).hasDerivAt.comp (v : ℂ) hinner
  exact h1.comp_ofReal

theorem vertical_point_eq (σ X₁ u : ℝ) :
    (σ : ℂ) + X₁ * I + u * I = (σ : ℂ) + ((X₁ + u : ℝ) : ℂ) * I := by push_cast; ring

/-- **The vertical log-linear model.** For `1 ≤ σ ≤ 3`, `T ≥ 48`, `|X₁ − T| + V ≤ T/2` and
`|u| ≤ V`: `‖G(w₁ + iu) − G(w₁) e^{iuL_T}‖ ≤ ‖G(w₁)‖ e^{−πu/4}(e^{η|u|} − 1)`,
`w₁ = σ + iX₁`, `η = (12 + |X₁ − T| + V)/T`. -/
theorem norm_archG_vertical_sub_model_le {σ X₁ T V u : ℝ} (hσ1 : 1 ≤ σ) (hσ3 : σ ≤ 3)
    (hT : 48 ≤ T) (hV : |X₁ - T| + V ≤ T / 2) (hu : |u| ≤ V) :
    ‖archG ((σ : ℂ) + X₁ * I + u * I) -
        archG ((σ : ℂ) + X₁ * I) * Complex.exp (u * I * horizontalSlope T)‖ ≤
      ‖archG ((σ : ℂ) + X₁ * I)‖ * Real.exp (-(u * (Real.pi / 4))) *
        (Real.exp ((12 + |X₁ - T| + V) / T * |u|) - 1) := by
  set F : ℝ → ℂ := fun v => archG ((σ : ℂ) + X₁ * I + v * I) with hF
  set η := (12 + |X₁ - T| + V) / T
  have hT0 : 0 < T := by linarith
  have hV0 : 0 ≤ V := (abs_nonneg u).trans hu
  have hη : 0 < η := by positivity
  have hmem : ∀ x ∈ uIcc 0 u, |x| ≤ V := by
    intro x hx
    rcases le_total 0 u with h | h
    · rw [uIcc_of_le h] at hx; rw [abs_of_nonneg hx.1]; exact hx.2.trans (le_abs_self u |>.trans hu)
    · rw [uIcc_of_ge h] at hx
      rw [abs_of_nonpos hx.2]; have := neg_abs_le u; linarith [hx.1]
  have hderiv : ∀ x ∈ uIcc 0 u, HasDerivAt F (deriv archG ((σ : ℂ) + X₁ * I + x * I) * I) x :=
    fun x _ => hasDerivAt_archG_vertical (by linarith) x
  have hbound : ∀ x ∈ uIcc 0 u, ‖deriv archG ((σ : ℂ) + X₁ * I + x * I) * I -
      (I * horizontalSlope T) * F x‖ ≤ η * ‖F x‖ := by
    intro x hx
    have hxV := hmem x hx
    set w := (σ : ℂ) + X₁ * I + x * I
    have hwre : 0 < w.re := by simp [w]; linarith
    have hXT : |(X₁ + x) - T| ≤ T / 2 := by
      have := abs_add_le (X₁ - T) x
      rw [show X₁ - T + x = X₁ + x - T by ring] at this
      linarith
    have hw1 : w ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp [w] at this
      have := (abs_le.mp hXT).1
      linarith
    have hFne : archG w ≠ 0 := archG_ne_zero hwre hw1
    have hld : deriv archG w = logDeriv archG w * archG w := by
      rw [logDeriv_apply]; field_simp
    have hslope := norm_logDeriv_archG_sub_slope_le hσ1 hσ3 hT hXT
    rw [← vertical_point_eq] at hslope
    have hle : (12 + |X₁ + x - T|) / T ≤ η := by
      apply div_le_div_of_nonneg_right _ hT0.le
      have := abs_add_le (X₁ - T) x
      rw [show X₁ - T + x = X₁ + x - T by ring] at this
      linarith
    change ‖deriv archG w * I - I * horizontalSlope T * archG w‖ ≤ η * ‖archG w‖
    rw [hld, show logDeriv archG w * archG w * I - I * horizontalSlope T * archG w =
      I * archG w * (logDeriv archG w - horizontalSlope T) by ring, norm_mul, norm_mul,
      Complex.norm_I, one_mul, mul_comm η]
    gcongr
    exact hslope.trans hle
  have h := GaloisForLFunctions.HTGeometry.norm_sub_mul_exp_le (a := I * horizontalSlope T) hη
    hderiv hbound
  simp only [sub_zero, hF] at h
  have hre : (I * horizontalSlope T).re = -(Real.pi / 4) := by
    simp [horizontalSlope, Complex.mul_re]
  rw [hre] at h
  have e1 : archG ((σ : ℂ) + X₁ * I + (0 : ℝ) * I) = archG ((σ : ℂ) + X₁ * I) := by simp
  have e2 : ((u : ℂ)) * (I * horizontalSlope T) = u * I * horizontalSlope T := by ring
  rw [e1, e2] at h
  refine h.trans (le_of_eq ?_)
  ring_nf

/-- **Lower bound.** On `3/2 ≤ σ ≤ 5/2` and heights `T ≥ 24`,
`‖G(σ + iT)‖ ≥ m e^{−(T−24)(log T + 2)}` with `m > 0`. -/
theorem exists_norm_archG_lower :
    ∃ m > 0, ∀ σ ∈ Icc (3 / 2 : ℝ) (5 / 2), ∀ T : ℝ, 24 ≤ T →
      m * Real.exp (-((T - 24) * (Real.log T + 2))) ≤ ‖archG ((σ : ℂ) + T * I)‖ := by
  have hK : IsCompact ((fun σ : ℝ => (σ : ℂ) + (24 : ℝ) * I) '' Icc (3 / 2 : ℝ) (5 / 2)) :=
    isCompact_Icc.image (by fun_prop)
  have hne : ((fun σ : ℝ => (σ : ℂ) + (24 : ℝ) * I) '' Icc (3 / 2 : ℝ) (5 / 2)).Nonempty :=
    (nonempty_Icc.mpr (by norm_num)).image _
  have hcont : ContinuousOn (fun w => ‖archG w‖)
      ((fun σ : ℝ => (σ : ℂ) + (24 : ℝ) * I) '' Icc (3 / 2 : ℝ) (5 / 2)) := by
    intro w hw
    obtain ⟨σ, hσ, rfl⟩ := hw
    exact (differentiableAt_archG (by simp; linarith [hσ.1])).continuousAt.norm.continuousWithinAt
  obtain ⟨w₀, ⟨σ₀, hσ₀, rfl⟩, hmin⟩ := hK.exists_isMinOn hne hcont
  refine ⟨‖archG ((σ₀ : ℂ) + (24 : ℝ) * I)‖, norm_pos_iff.mpr (archG_ne_zero (by simp; linarith
    [hσ₀.1]) (by intro h; have := congrArg Complex.im h; simp at this)), fun σ hσ T hT => ?_⟩
  have hm : ‖archG ((σ₀ : ℂ) + (24 : ℝ) * I)‖ ≤ ‖archG ((σ : ℂ) + (24 : ℝ) * I)‖ :=
    hmin ⟨σ, hσ, rfl⟩
  -- backward Grönwall from height `T` down to `24`
  set F : ℝ → ℂ := fun x => archG ((σ : ℂ) + (T + 24 - x : ℝ) * I) with hF
  have hderiv : ∀ x ∈ Icc (24 : ℝ) T, HasDerivAt F
      (-(deriv archG ((σ : ℂ) + (T + 24 - x : ℝ) * I) * I)) x := by
    intro x _
    have h := hasDerivAt_archG_vertical (σ := σ) (X₁ := T + 24) (by linarith [hσ.1]) (-x)
    have hc := h.scomp x (hasDerivAt_neg x)
    refine (hc.congr_deriv (by
      simp only [neg_smul, one_smul, neg_inj]
      congr 2; push_cast; ring)).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp only [hF, Function.comp]
    congr 1; push_cast; ring
  have hbd : ∀ x ∈ Icc (24 : ℝ) T,
      ‖-(deriv archG ((σ : ℂ) + (T + 24 - x : ℝ) * I) * I)‖ ≤ (Real.log T + 2) * ‖F x‖ := by
    intro x hx
    set w := (σ : ℂ) + (T + 24 - x : ℝ) * I
    have hwre : 0 < w.re := by simp [w]; linarith [hσ.1]
    have hw1 : w ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp [w] at this; linarith [hx.2]
    have hld : deriv archG w = logDeriv archG w * archG w := by
      rw [logDeriv_apply]; field_simp [archG_ne_zero hwre hw1]
    have hX : 24 ≤ T + 24 - x := by linarith [hx.2]
    have hlog := norm_logDeriv_archG_le (σ := σ) (by linarith [hσ.1]) (by linarith [hσ.2]) hX
    have hlogT : Real.log (T + 24 - x) ≤ Real.log T :=
      Real.log_le_log (by linarith) (by linarith [hx.1])
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one, hld, norm_mul]
    change ‖logDeriv archG w‖ * ‖archG w‖ ≤ (Real.log T + 2) * ‖archG w‖
    gcongr
    linarith
  have hg := GaloisForLFunctions.HTGeometry.norm_le_mul_exp_of_norm_deriv_le_Icc hT hderiv hbd
  simp only [hF] at hg
  have e1 : ((σ : ℂ) + ((T + 24 - T : ℝ) : ℂ) * I) = (σ : ℂ) + (24 : ℝ) * I := by
    congr 2; push_cast; ring
  have e2 : ((σ : ℂ) + ((T + 24 - 24 : ℝ) : ℂ) * I) = (σ : ℂ) + T * I := by
    congr 2; push_cast; ring
  rw [e1, e2] at hg
  have hpos := Real.exp_pos ((Real.log T + 2) * (T - 24))
  calc ‖archG ((σ₀ : ℂ) + (24 : ℝ) * I)‖ * Real.exp (-((T - 24) * (Real.log T + 2)))
      ≤ ‖archG ((σ : ℂ) + T * I)‖ * Real.exp ((Real.log T + 2) * (T - 24)) *
          Real.exp (-((T - 24) * (Real.log T + 2))) := by gcongr; exact hm.trans hg
    _ = ‖archG ((σ : ℂ) + T * I)‖ := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf; simp

end

end RHTower
