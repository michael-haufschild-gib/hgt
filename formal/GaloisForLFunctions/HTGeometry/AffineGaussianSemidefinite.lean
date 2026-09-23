import GaloisForLFunctions.HTGeometry.PeriodicBoundedThetaNorm

/-!
# Semi-definiteness in every direction

The vanishing argument along a line through the origin only constrains directions on which the
theta function is not identically zero.  Running it along an **affine** line removes that
restriction: on `z0 + C v` the Hermitian exponent is

`Re H (z0, z0) + 2 Re H (z0, t v) + |t|^(2 : ℕ) Re H (v,v)`,

whose cross term is linear in `|t|` and is absorbed into the Gaussian by completing the square.  A
theta function that is nonzero at a single point therefore forces `Re H (v,v) >= 0` for **every**
direction `v`, which is the semi-definiteness the generalized Riemann relations need.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Gaussian decay along an affine complex line kills the function on that line.** -/
theorem eq_zero_of_gaussian_decay_along_affine_line {f : W → ℂ} (hf : Differentiable ℂ f)
    (z₀ v : W) {C a : ℝ} (ha : 0 < a)
    (hbound : ∀ t : ℂ, ‖f (z₀ + t • v)‖ ≤ C * Real.exp (-a * ‖t‖ ^ (2 : ℕ))) (t : ℂ) :
    f (z₀ + t • v) = 0 := by
  have hg : Differentiable ℂ fun t : ℂ => f (z₀ + t • v) :=
    hf.comp ((differentiable_id.smul_const v).const_add z₀)
  exact eq_zero_of_gaussian_decay hg ha hbound t

/-- The Hermitian exponent along an affine line. -/
theorem hermitianForm_affine_re {H : W → W → ℂ} (hH : IsHermitianForm H) (z₀ v : W) (s : ℂ) :
    (H (z₀ + s • v) (z₀ + s • v)).re
      = (H z₀ z₀).re + 2 * (H z₀ (s • v)).re + ‖s‖ ^ (2 : ℕ) * (H v v).re := by
  rw [hH.add_left, hH.add_right, hH.add_right, Complex.add_re, Complex.add_re, Complex.add_re,
    hermitianForm_smul_self hH, hH.re_symm (s • v) z₀]
  ring

/-- The cross term is linear in the parameter. -/
theorem abs_hermitianForm_cross_le {H : W → W → ℂ} (hH : IsHermitianForm H) (z₀ v : W) (s : ℂ) :
    |(H z₀ (s • v)).re| ≤ ‖s‖ * ‖H v z₀‖ := by
  have hsw : H z₀ (s • v) = star (s * H v z₀) := by
    rw [hH.symm (s • v) z₀, hH.smul_left]
  calc |(H z₀ (s • v)).re| ≤ ‖H z₀ (s • v)‖ := Complex.abs_re_le_norm _
    _ = ‖s‖ * ‖H v z₀‖ := by rw [hsw, norm_star, norm_mul]

/-- **A negative direction kills a bounded theta function on every affine line in that
direction.** -/
theorem eq_zero_along_affine_line_of_neg {H : W → W → ℂ} (hH : IsHermitianForm H)
    {θ : W → ℂ} (hdiff : Differentiable ℂ θ) {M : ℝ} (hbdd : ∀ z, thetaNorm H θ z ≤ M)
    {v : W} (hv : (H v v).re < 0) (z₀ : W) (t : ℂ) :
    θ (z₀ + t • v) = 0 := by
  have hMnn : 0 ≤ M := by
    have h := hbdd z₀
    rw [thetaNorm] at h
    have := Real.exp_pos (-(Real.pi / 2) * (H z₀ z₀).re)
    nlinarith [norm_nonneg (θ z₀)]
  set c : ℝ := (H v v).re with hc
  set B : ℝ := ‖H v z₀‖ with hB
  have hBnn : 0 ≤ B := norm_nonneg _
  have hcneg : 0 < -c := by rw [hc]; linarith
  have ha : 0 < -(Real.pi / 4) * c := by
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  refine eq_zero_of_gaussian_decay_along_affine_line hdiff z₀ v ha
    (C := M * Real.exp (Real.pi / 2 * ((H z₀ z₀).re + 2 * B ^ (2 : ℕ) / (-c)))) (fun s => ?_) t
  have hb := hbdd (z₀ + s • v)
  rw [thetaNorm, hermitianForm_affine_re hH] at hb
  have hexp : (0 : ℝ) < Real.exp (-(Real.pi / 2)
      * ((H z₀ z₀).re + 2 * (H z₀ (s • v)).re + ‖s‖ ^ (2 : ℕ) * c)) := Real.exp_pos _
  rw [← le_div_iff₀ hexp, div_eq_mul_inv, ← Real.exp_neg] at hb
  refine hb.trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left ?_ hMnn
  rw [Real.exp_le_exp]
  have hcross : (H z₀ (s • v)).re ≤ ‖s‖ * B :=
    le_trans (le_abs_self _) (abs_hermitianForm_cross_le hH z₀ v s)
  have hamgm : 2 * (‖s‖ * B) ≤ (-c / 2) * ‖s‖ ^ (2 : ℕ) + 2 * B ^ (2 : ℕ) / (-c) := by
    have hcne : c ≠ 0 := ne_of_lt hv
    have hD : (2 * B ^ (2 : ℕ) / (-c)) * (-c) = 2 * B ^ (2 : ℕ) := by field_simp
    nlinarith [sq_nonneg ((-c) * ‖s‖ - 2 * B), hcneg, norm_nonneg s, hBnn, hD]
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith [hcross, hamgm, sq_nonneg ‖s‖, hpi]

/-- **Semi-definiteness in every direction.**  A theta function nonzero at a single point forces
the Hermitian form to be non-negative in every direction. -/
theorem nonneg_re_of_thetaNorm_bounded_of_exists_ne_zero {H : W → W → ℂ} (hH : IsHermitianForm H)
    {θ : W → ℂ} (hdiff : Differentiable ℂ θ) {M : ℝ} (hbdd : ∀ z, thetaNorm H θ z ≤ M)
    {z₀ : W} (hne : θ z₀ ≠ 0) (v : W) :
    0 ≤ (H v v).re := by
  by_contra hlt
  push Not at hlt
  have h := eq_zero_along_affine_line_of_neg hH hdiff hbdd hlt z₀ 0
  rw [zero_smul, add_zero] at h
  exact hne h

end GaloisForLFunctions.HTGeometry
