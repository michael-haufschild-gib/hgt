import GaloisForLFunctions.RHTower.MobiusCausalBoundaryEnergy
import GaloisForLFunctions.RHTower.MobiusCausalMultiplierBounds

/-!
# The centered signed-Schur boundary quotient and its critical Hardy limit

Formalizes the analytic core of
`mobius-schur-centered-boundary-limit-law.md` (equations `(3)`, `(4)`, `(5)`) and of
`mobius-schur-causal-critical-graph-limit-law.md` (equations `(2)`--`(7)`, `(13)`, `(14)`).

With `c_ω = 1/(1+ω)`,

```text
G_ω(z) = c_ω (1/ζ(1+2ω+z) - 1/ζ(1+2ω)) / z ,
G_0(z) = 1/(z ζ(1+z)) ,
H_ω(z) = [ζ(1+z)/(1+ω+z) - c_ω/z] / ζ(1+2ω+z) ,
H_0(z) = 1/(1+z) - G_0(z) .
```

The exact splitting `M_ω = H_ω + G_ω` of the coupled causal multiplier is algebraic.  On the
boundary line the centered quotient has a majorant uniform in the parameter: near the origin it is a
difference quotient of the entire pole unit `Z(s) = (s-1)ζ(s)`, and far out the uniform reciprocal
bound on the shifted line applies.  Dominated convergence then gives the strong Hardy limits

```text
∫ ‖G_ω(iτ) - G_0(iτ)‖² dτ → 0 ,      ∫ ‖H_ω(iτ) - H_0(iτ)‖² dτ → 0 .
```
-/

open Complex MeasureTheory Filter Topology Set Metric

noncomputable section
namespace RHTower

/-! ### The two components -/

/-- Card `(3)`: the centered signed-Schur difference quotient. -/
def centeredSchurQuotient (ω : ℝ) (z : ℂ) : ℂ :=
  (1 / ((1 : ℂ) + (ω : ℂ))) *
    (((riemannZeta (1 + 2 * (ω : ℂ) + z))⁻¹ - (riemannZeta (1 + 2 * (ω : ℂ)))⁻¹) / z)

/-- Card `(4)`: the critical limit of the centered quotient. -/
def centeredSchurLimit (z : ℂ) : ℂ := 1 / (z * riemannZeta (1 + z))

/-- Card `(3)` of the causal-graph law: the renormalized floor-remainder transform. -/
def floorRemainderTransfer (ω : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (1 + z) / (1 + (ω : ℂ) + z) - (1 / ((1 : ℂ) + (ω : ℂ))) / z) /
    riemannZeta (1 + 2 * (ω : ℂ) + z)

/-- Card `(6)` of the causal-graph law: the critical floor-remainder limit. -/
def floorRemainderLimit (z : ℂ) : ℂ := 1 / (1 + z) - centeredSchurLimit z

/-- **Card `(14)` of the causal-graph law.**  The exact critical cancellation. -/
theorem floorRemainderLimit_add_centeredSchurLimit (z : ℂ) :
    floorRemainderLimit z + centeredSchurLimit z = 1 / (1 + z) := by
  rw [floorRemainderLimit]
  ring

/-- **Card `(5)` of the causal-graph law.**  The coupled causal multiplier splits exactly. -/
theorem mobiusCausalMultiplier_eq_add {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    mobiusCausalMultiplier ω z = floorRemainderTransfer ω z + centeredSchurQuotient ω z := by
  have hζ := riemannZeta_one_add_two_mul_add_ne_zero hω hz
  have hζ0 := riemannZeta_one_add_two_mul_ne_zero hω
  have hlin := one_add_ofReal_add_ne_zero hω hz
  have hω0 := one_add_ofReal_ne_zero hω
  rw [mobiusCausalMultiplier, floorRemainderTransfer, centeredSchurQuotient]
  field_simp
  ring

/-! ### The pole-unit form of the centered quotient -/

/-- The reciprocal zeta value in pole-unit coordinates. -/
theorem inv_riemannZeta_eq_poleUnit {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    (riemannZeta s)⁻¹ = (s - 1) / zetaPoleUnit s := by
  rw [zetaPoleUnit_of_ne hs]
  have h1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  field_simp

theorem centeredSchurQuotient_eq_poleUnit {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) :
    centeredSchurQuotient ω z =
      (1 / ((1 : ℂ) + (ω : ℂ))) *
        (((2 * (ω : ℂ) + z) / zetaPoleUnit (1 + 2 * (ω : ℂ) + z) -
          2 * (ω : ℂ) / zetaPoleUnit (1 + 2 * (ω : ℂ))) / z) := by
  have h1 := inv_riemannZeta_eq_poleUnit (one_add_two_mul_add_ne_one hω hz)
    (riemannZeta_one_add_two_mul_add_ne_zero hω hz)
  have hne0 : (1 : ℂ) + 2 * (ω : ℂ) ≠ 1 := by
    have h := one_add_two_mul_add_ne_one hω (z := 0) (by simp)
    simpa using h
  have h2 := inv_riemannZeta_eq_poleUnit hne0 (riemannZeta_one_add_two_mul_ne_zero hω)
  have e1 : (1 : ℂ) + 2 * (ω : ℂ) + z - 1 = 2 * (ω : ℂ) + z := by ring
  have e2 : (1 : ℂ) + 2 * (ω : ℂ) - 1 = 2 * (ω : ℂ) := by ring
  rw [centeredSchurQuotient, h1, h2, e1, e2]

/-! ### The uniform near-origin bound -/

theorem exists_near_origin_centered_bound :
    ∃ δ ω₀ C : ℝ, 0 < δ ∧ 0 < ω₀ ∧ 0 ≤ C ∧
      ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ → ∀ z : ℂ, 0 ≤ z.re → z ≠ 0 → ‖z‖ ≤ δ →
        ‖centeredSchurQuotient ω z‖ ≤ C := by
  obtain ⟨ρ, Cb, hρpos, hρ8, hCb1, hbd⟩ := exists_poleUnit_ball_bounds
  have hCb0 : (0 : ℝ) < Cb := by linarith
  refine ⟨ρ / 4, ρ / 8, 2 * Cb * (Cb * 1) / (1 / 2 : ℝ) ^ (2 : ℕ), by linarith, by linarith,
    by positivity, ?_⟩
  intro ω hω hωle z hzre hz0 hzδ
  have hzn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hmemZ : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → (1 : ℂ) + 2 * (ω : ℂ) + w ∈ closedBall (1 : ℂ) ρ := by
    intro w hw
    have h1 : dist ((1 : ℂ) + 2 * (ω : ℂ) + w) 1 = ‖2 * (ω : ℂ) + w‖ := by
      rw [dist_eq_norm]; ring_nf
    rw [Metric.mem_closedBall, h1]
    have h2 : ‖2 * (ω : ℂ) + w‖ ≤ 2 * ω + ‖w‖ := by
      refine le_trans (norm_add_le _ _) ?_
      have : ‖2 * ((ω : ℝ) : ℂ)‖ = 2 * ω := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]; norm_num
      rw [this]
    linarith
  have hmem0 : (1 : ℂ) + 2 * (ω : ℂ) ∈ closedBall (1 : ℂ) ρ := by
    have h := hmemZ 0 (by simpa using le_of_lt (by linarith : (0:ℝ) < ρ / 4))
    simpa using h
  have hmemz := hmemZ z hzδ
  obtain ⟨hZlow, hZup, hZ'up, -⟩ := hbd _ hmemz
  obtain ⟨hZlow0, hZup0, -, -⟩ := hbd _ hmem0
  -- the numerators
  have hA0 : ‖2 * ((ω : ℝ) : ℂ)‖ ≤ Cb := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
    have : ω ≤ ρ / 8 := hωle
    have : (2 : ℝ) * ω ≤ 1 := by linarith
    simpa using by linarith
  have hAdiff : ‖(2 * (ω : ℂ) + z) - 2 * (ω : ℂ)‖ ≤ Cb * ‖z‖ := by
    have hz' : ‖(2 * (ω : ℂ) + z) - 2 * (ω : ℂ)‖ = ‖z‖ := by
      congr 1; ring
    rw [hz']
    nlinarith [hzn.le]
  have hBdiff : ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + z) - zetaPoleUnit (1 + 2 * (ω : ℂ))‖
      ≤ Cb * ‖z‖ := by
    have hmv := HTGeometry.norm_sub_le_of_hasDerivAt_ball
      (f := zetaPoleUnit) (f' := deriv zetaPoleUnit) (c := (1 : ℂ)) (r := ρ) (C := Cb)
      (fun w => (differentiable_zetaPoleUnit w).hasDerivAt)
      (fun w hw => (hbd w hw).2.2.1)
      (x := (1 : ℂ) + 2 * (ω : ℂ)) (y := (1 : ℂ) + 2 * (ω : ℂ) + z)
      hmem0 hmemz
    have hdiff : ((1 : ℂ) + 2 * (ω : ℂ) + z) - ((1 : ℂ) + 2 * (ω : ℂ)) = z := by ring
    rw [hdiff] at hmv
    exact hmv
  have hquot := HTGeometry.norm_div_sub_div_le (m := (1 / 2 : ℝ)) (K := Cb * ‖z‖) (L := Cb)
    (by norm_num) hZlow hZlow0 hA0 hZup0 hAdiff hBdiff (by positivity)
  have hωnorm : ‖(1 : ℂ) / ((1 : ℂ) + (ω : ℂ))‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have hre : ((1 : ℂ) + (ω : ℂ)).re = 1 + ω := by simp
    have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) + (ω : ℂ)‖ := by
      have := Complex.re_le_norm ((1 : ℂ) + (ω : ℂ))
      rw [hre] at this
      linarith
    rw [div_le_one (by linarith)]
    linarith
  have hstep : ‖((2 * (ω : ℂ) + z) / zetaPoleUnit (1 + 2 * (ω : ℂ) + z) -
      2 * (ω : ℂ) / zetaPoleUnit (1 + 2 * (ω : ℂ))) / z‖
      ≤ 2 * Cb * (Cb * 1) / (1 / 2 : ℝ) ^ (2 : ℕ) := by
    rw [norm_div, div_le_iff₀ hzn]
    have hgoal : 2 * Cb * (Cb * ‖z‖) / (1 / 2 : ℝ) ^ (2 : ℕ)
        = 2 * Cb * (Cb * 1) / (1 / 2 : ℝ) ^ (2 : ℕ) * ‖z‖ := by ring
    calc ‖(2 * (ω : ℂ) + z) / zetaPoleUnit (1 + 2 * (ω : ℂ) + z) -
          2 * (ω : ℂ) / zetaPoleUnit (1 + 2 * (ω : ℂ))‖
        ≤ 2 * Cb * (Cb * ‖z‖) / (1 / 2 : ℝ) ^ (2 : ℕ) := hquot
      _ = 2 * Cb * (Cb * 1) / (1 / 2 : ℝ) ^ (2 : ℕ) * ‖z‖ := hgoal
  rw [centeredSchurQuotient_eq_poleUnit hω hzre, norm_mul]
  calc ‖(1 : ℂ) / ((1 : ℂ) + (ω : ℂ))‖ *
        ‖((2 * (ω : ℂ) + z) / zetaPoleUnit (1 + 2 * (ω : ℂ) + z) -
          2 * (ω : ℂ) / zetaPoleUnit (1 + 2 * (ω : ℂ))) / z‖
      ≤ 1 * (2 * Cb * (Cb * 1) / (1 / 2 : ℝ) ^ (2 : ℕ)) :=
        mul_le_mul hωnorm hstep (norm_nonneg _) (by norm_num)
    _ = 2 * Cb * (Cb * 1) / (1 / 2 : ℝ) ^ (2 : ℕ) := one_mul _


/-! ### The mid-range and far-field bounds -/

theorem norm_inv_one_add_ofReal_le {ω : ℝ} (hω : 0 < ω) :
    ‖(1 : ℂ) / ((1 : ℂ) + (ω : ℂ))‖ ≤ 1 := by
  rw [norm_div, norm_one]
  have hre : ((1 : ℂ) + (ω : ℂ)).re = 1 + ω := by simp
  have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) + (ω : ℂ)‖ := by
    have := Complex.re_le_norm ((1 : ℂ) + (ω : ℂ))
    rw [hre] at this
    linarith
  rw [div_le_one (by linarith)]
  linarith

theorem norm_centeredSchurQuotient_line_le {ω : ℝ} (hω : 0 < ω) {τ : ℝ} (hτ : τ ≠ 0) :
    ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I)‖
      ≤ (‖(riemannZeta (1 + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ +
          ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖) / |τ| := by
  have hznorm : ‖(τ : ℂ) * Complex.I‖ = |τ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hτpos : 0 < |τ| := abs_pos.mpr hτ
  have hstep : ‖((riemannZeta (1 + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I))⁻¹ -
      (riemannZeta (1 + 2 * (ω : ℂ)))⁻¹) / ((τ : ℂ) * Complex.I)‖
      ≤ (‖(riemannZeta (1 + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ +
          ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖) / |τ| := by
    rw [norm_div, hznorm]
    gcongr
    exact norm_sub_le _ _
  rw [centeredSchurQuotient, norm_mul]
  calc ‖(1 : ℂ) / ((1 : ℂ) + (ω : ℂ))‖ *
        ‖((riemannZeta (1 + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I))⁻¹ -
          (riemannZeta (1 + 2 * (ω : ℂ)))⁻¹) / ((τ : ℂ) * Complex.I)‖
      ≤ 1 * ((‖(riemannZeta (1 + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ +
          ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖) / |τ|) :=
        mul_le_mul (norm_inv_one_add_ofReal_le hω) hstep (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem norm_centeredSchurQuotient_far_le {ω : ℝ} (hω : 0 < ω) (hω1 : 2 * ω ≤ 1)
    (hζinv : ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖ ≤ 1) {τ : ℝ} (hτ : 9 < |τ|) :
    ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I)‖
      ≤ (26 / zetaLowerA + 1) * Real.log |τ| ^ (26 : ℕ) / |τ| := by
  have hτ9 : (9 : ℝ) ≤ |τ| := le_of_lt hτ
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hτ
    linarith
  have hτpos : 0 < |τ| := abs_pos.mpr hτ0
  have hL2 : 2 < Real.log |τ| := two_lt_log_abs hτ9
  have hL1 : (1 : ℝ) ≤ Real.log |τ| := by linarith
  have hshift := norm_inv_riemannZeta_shift_le hω hω1 hτ9
  have hpow : Real.log |τ| ^ (7 : ℕ) ≤ Real.log |τ| ^ (26 : ℕ) :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have hApos : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hbase := norm_centeredSchurQuotient_line_le hω hτ0
  have hnum : ‖(riemannZeta (1 + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ +
      ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖
      ≤ (26 / zetaLowerA + 1) * Real.log |τ| ^ (26 : ℕ) := by
    have h1 : ‖(riemannZeta (1 + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖
        ≤ 26 / zetaLowerA * Real.log |τ| ^ (26 : ℕ) := by
      refine le_trans hshift ?_
      have h26 : (0 : ℝ) < 26 / zetaLowerA := by positivity
      nlinarith [hpow]
    have h2 : ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖ ≤ 1 * Real.log |τ| ^ (26 : ℕ) := by
      have hge : (1 : ℝ) ≤ Real.log |τ| ^ (26 : ℕ) := one_le_pow₀ hL1
      linarith
    linarith
  calc ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I)‖
      ≤ (‖(riemannZeta (1 + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ +
          ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖) / |τ| := hbase
    _ ≤ (26 / zetaLowerA + 1) * Real.log |τ| ^ (26 : ℕ) / |τ| := by gcongr

theorem exists_mid_range_centered_bound {ω₀ δ : ℝ} (_hω₀ : 0 < ω₀) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ →
      ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖ ≤ 1 →
      ∀ τ : ℝ, δ ≤ |τ| → |τ| ≤ 9 →
        ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_midRange_zeta_bounds ω₀ δ hδ
  refine ⟨(C + 1) / δ, by positivity, fun ω hω hωle hζinv τ hτδ hτ9 => ?_⟩
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hτδ
    linarith
  have hτpos : 0 < |τ| := abs_pos.mpr hτ0
  have hmem : (1 : ℂ) + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I ∈ midRangeSet ω₀ δ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, mul_one]
      linarith
    · simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, mul_one]
      linarith
    · simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im,
        mul_zero, zero_add, mul_one, add_zero, zero_mul]
      exact hτδ
    · simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im,
        mul_zero, zero_add, mul_one, add_zero, zero_mul]
      exact hτ9
  have hbase := norm_centeredSchurQuotient_line_le hω hτ0
  have hnum : ‖(riemannZeta (1 + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I))⁻¹‖ +
      ‖(riemannZeta (1 + 2 * (ω : ℂ)))⁻¹‖ ≤ C + 1 := by
    have h1 := (hC _ hmem).2
    linarith
  refine le_trans hbase ?_
  rw [div_le_div_iff₀ hτpos hδ]
  nlinarith [hτδ, hC0, hτpos]


/-! ### The uniform boundary majorant -/

theorem farFieldConstant_pos : 0 < farFieldConstant := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  rw [farFieldConstant]
  positivity

/-- **The uniform boundary bound for the centered Schur quotient.** -/
theorem exists_uniform_centered_bound :
    ∃ ω₀ K lam : ℝ, 0 < ω₀ ∧ 0 ≤ K ∧ 0 < lam ∧
      ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ → ∀ τ : ℝ, τ ≠ 0 →
        ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I)‖ ≤ lam * boundaryMajorant K τ := by
  obtain ⟨δ, ω₀n, Cn, hδ, hω₀n, hCn, hnear⟩ := exists_near_origin_centered_bound
  obtain ⟨ω₂, hω₂, hinvζ⟩ := exists_inv_zeta_real_bound
  have hδ' : 0 < min δ 9 := lt_min hδ (by norm_num)
  have hω₀ : 0 < min (min ω₀n ω₂) (1 / 2 : ℝ) := lt_min (lt_min hω₀n hω₂) (by norm_num)
  obtain ⟨Cm, hCm, hmid⟩ :=
    exists_mid_range_centered_bound (ω₀ := min (min ω₀n ω₂) (1 / 2 : ℝ)) (δ := min δ 9) hω₀ hδ'
  have hApos : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  set Cfar : ℝ := 26 / zetaLowerA + 1 with hCfar
  have hCfarpos : 0 < Cfar := by rw [hCfar]; positivity
  set lam : ℝ := Cfar / farFieldConstant with hlam
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos hCfarpos farFieldConstant_pos
  set K : ℝ := max Cn Cm / lam with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have : 0 ≤ max Cn Cm := le_trans hCn (le_max_left _ _)
    positivity
  refine ⟨min (min ω₀n ω₂) (1 / 2 : ℝ), K, lam, hω₀, hK0, hlampos, ?_⟩
  intro ω hω hωle τ hτ
  have hωn : ω ≤ ω₀n := le_trans hωle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hω2 : ω ≤ ω₂ := le_trans hωle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hωhalf : 2 * ω ≤ 1 := by
    have : ω ≤ 1 / 2 := le_trans hωle (min_le_right _ _)
    linarith
  have hζinv := hinvζ ω hω hω2
  have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hτ
  have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
  have hznorm : ‖(τ : ℂ) * Complex.I‖ = |τ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hlamK : lam * K = max Cn Cm := by
    rw [hK]
    field_simp
  by_cases hcase1 : |τ| ≤ min δ 9
  · have hle : ‖(τ : ℂ) * Complex.I‖ ≤ δ := by
      rw [hznorm]
      exact le_trans hcase1 (min_le_left _ _)
    have h := hnear ω hω hωn ((τ : ℂ) * Complex.I) hzre hz0 hle
    have h9 : |τ| ≤ 9 := le_trans hcase1 (min_le_right _ _)
    rw [boundaryMajorant_near h9, hlamK]
    exact le_trans h (le_max_left _ _)
  · rw [not_le] at hcase1
    by_cases hcase2 : |τ| ≤ 9
    · have h := hmid ω hω hωle hζinv τ (le_of_lt hcase1) hcase2
      rw [boundaryMajorant_near hcase2, hlamK]
      exact le_trans h (le_max_right _ _)
    · rw [not_le] at hcase2
      have h := norm_centeredSchurQuotient_far_le hω hωhalf hζinv hcase2
      rw [boundaryMajorant_far hcase2]
      have hfFC : farFieldConstant ≠ 0 := ne_of_gt farFieldConstant_pos
      have hval : lam * (farFieldConstant * Real.log |τ| ^ (26 : ℕ) / |τ|)
          = Cfar * Real.log |τ| ^ (26 : ℕ) / |τ| := by
        rw [hlam]
        field_simp
      rw [hval]
      exact h

/-! ### The pointwise critical limit -/

theorem tendsto_centeredSchurQuotient {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    Tendsto (fun ω : ℝ => centeredSchurQuotient ω z) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (centeredSchurLimit z)) := by
  have h1z : (1 : ℂ) + z ≠ 1 := one_add_ne_one hz0
  have hζ0 : riemannZeta (1 + z) ≠ 0 := riemannZeta_one_add_ne_zero hz
  have hζcont : ContinuousAt riemannZeta (1 + z) :=
    (differentiableAt_riemannZeta h1z).continuousAt
  have hshift : Tendsto (fun ω : ℝ => (1 : ℂ) + 2 * (ω : ℂ) + z)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 + z)) := by
    have hc : Continuous fun ω : ℝ => (1 : ℂ) + 2 * (ω : ℂ) + z := by fun_prop
    have h0 : (1 : ℂ) + 2 * ((0 : ℝ) : ℂ) + z = 1 + z := by push_cast; ring
    have h := hc.tendsto (0 : ℝ)
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun ω : ℝ => (riemannZeta (1 + 2 * (ω : ℂ) + z))⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((riemannZeta (1 + z))⁻¹)) :=
    ((hζcont.tendsto.comp hshift).inv₀ hζ0)
  have hB : Tendsto (fun ω : ℝ => (riemannZeta (1 + 2 * (ω : ℂ)))⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := tendsto_inv_riemannZeta_one_add_two_mul
  have hc : Tendsto (fun ω : ℝ => (1 : ℂ) / ((1 : ℂ) + (ω : ℂ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    have hcont : Continuous fun ω : ℝ => (1 : ℂ) + (ω : ℂ) := by fun_prop
    have h0 : (1 : ℂ) + ((0 : ℝ) : ℂ) = 1 := by push_cast; ring
    have h := hcont.tendsto (0 : ℝ)
    rw [h0] at h
    have hmono : Tendsto (fun ω : ℝ => (1 : ℂ) + (ω : ℂ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := h.mono_left nhdsWithin_le_nhds
    have hinv : Tendsto (fun ω : ℝ => ((1 : ℂ) + (ω : ℂ))⁻¹)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((1 : ℂ))⁻¹) := hmono.inv₀ one_ne_zero
    simpa [one_div] using hinv
  have hmain := hc.mul (((hA.sub hB)).div_const z)
  have hval : (1 : ℂ) * (((riemannZeta (1 + z))⁻¹ - 0) / z) = centeredSchurLimit z := by
    rw [centeredSchurLimit, sub_zero, one_mul]
    field_simp
  rw [hval] at hmain
  exact hmain

theorem continuousOn_centeredSchurQuotient_line {ω : ℝ} (hω : 0 < ω) :
    ContinuousOn (fun τ : ℝ => centeredSchurQuotient ω ((τ : ℂ) * Complex.I))
      {t : ℝ | t ≠ 0} := by
  intro τ hτ0
  have hτ : τ ≠ 0 := hτ0
  have hne2 : (1 : ℂ) + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := by
    have h := line_ne_one (c := (1 : ℂ) + 2 * (ω : ℂ)) (by simp) hτ
    simpa [add_assoc] using h
  have hz : ContinuousAt (fun t : ℝ => ((t : ℂ) * Complex.I)) τ := by
    have : Continuous (fun t : ℝ => ((t : ℂ) * Complex.I)) := by continuity
    exact this.continuousAt
  have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hτ
  have hC : ContinuousAt (fun t : ℝ => riemannZeta (1 + 2 * (ω : ℂ) + (t : ℂ) * Complex.I)) τ := by
    have := continuousAt_zeta_line (c := (1 : ℂ) + 2 * (ω : ℂ)) (τ := τ) (by
      simpa [add_assoc] using hne2)
    simpa [add_assoc] using this
  have hζ0 : riemannZeta ((1 : ℂ) + 2 * (ω : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, Complex.I_re,
      Complex.I_im, mul_one]
    linarith
  have hcont : ContinuousAt
      (fun t : ℝ => centeredSchurQuotient ω ((t : ℂ) * Complex.I)) τ := by
    refine ContinuousAt.mul continuousAt_const ?_
    exact ((hC.inv₀ hζ0).sub continuousAt_const).div hz hz0
  exact hcont.continuousWithinAt


/-! ### The strong Hardy limits -/

/-- **Card `(5)` of the centered-boundary law.**  The centered Schur quotient converges to
`G_0(z) = 1/(z ζ(1+z))` in the boundary `L²` (Hardy) norm. -/
theorem tendsto_boundary_centeredSchur_energy :
    Tendsto (fun ω : ℝ => ∫ τ : ℝ, ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I) -
        centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨ω₀, K, lam, hω₀, hK, hlam, hbound⟩ := exists_uniform_centered_bound
  have hev : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ω ∧ ω ≤ ω₀ := by
    filter_upwards [Ioc_mem_nhdsGT hω₀] with ω hω
    exact ⟨hω.1, hω.2⟩
  have hlimfun : ∀ τ : ℝ, τ ≠ 0 →
      ‖centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ≤ lam * boundaryMajorant K τ := by
    intro τ hτ
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
    have hlim := (tendsto_centeredSchurQuotient hzre hz0).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [hev] with ω hω
    exact hbound ω hω.1 hω.2 τ hτ
  have hcontlim : ContinuousOn (fun τ : ℝ => centeredSchurLimit ((τ : ℂ) * Complex.I))
      {t : ℝ | t ≠ 0} := by
    intro τ hτ0
    have hτ : τ ≠ 0 := hτ0
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hne1 : (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := line_ne_one (by simp) hτ
    have hζ0 : riemannZeta ((1 : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
      refine riemannZeta_ne_zero_of_one_le_re ?_
      simp
    have hz : ContinuousAt (fun t : ℝ => ((t : ℂ) * Complex.I)) τ := by
      have : Continuous (fun t : ℝ => ((t : ℂ) * Complex.I)) := by continuity
      exact this.continuousAt
    have hA : ContinuousAt (fun t : ℝ => riemannZeta (1 + (t : ℂ) * Complex.I)) τ :=
      continuousAt_zeta_line hne1
    have hcont : ContinuousAt
        (fun t : ℝ => centeredSchurLimit ((t : ℂ) * Complex.I)) τ := by
      refine continuousAt_const.div (hz.mul hA) ?_
      exact mul_ne_zero hz0 hζ0
    exact hcont.continuousWithinAt
  have hmeas : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable (fun τ : ℝ =>
        ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I) -
          centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ)) volume := by
    filter_upwards [hev] with ω hω
    have h1 := aestronglyMeasurable_of_continuousOn_ne_zero
      (continuousOn_centeredSchurQuotient_line hω.1)
    have h2 := aestronglyMeasurable_of_continuousOn_ne_zero hcontlim
    exact ((h1.sub h2).norm.pow 2)
  have hdom : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ᵐ τ : ℝ,
      ‖‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I) -
        centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ)‖ ≤ lam ^ (2 : ℕ) * boundaryBound K τ := by
    filter_upwards [hev] with ω hω
    filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
    have hτ : τ ≠ 0 := hτmem
    have h1 := hbound ω hω.1 hω.2 τ hτ
    have h2 := hlimfun τ hτ
    have h3 : ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I) -
        centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ≤ 2 * (lam * boundaryMajorant K τ) := by
      refine le_trans (norm_sub_le _ _) ?_
      linarith
    have h4 : (0 : ℝ) ≤ ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I) -
        centeredSchurLimit ((τ : ℂ) * Complex.I)‖ := norm_nonneg _
    have hmaj : (0 : ℝ) ≤ boundaryMajorant K τ := boundaryMajorant_nonneg hK τ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), boundaryBound_eq K τ]
    calc ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I) -
          centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ)
        ≤ (2 * (lam * boundaryMajorant K τ)) ^ (2 : ℕ) := pow_le_pow_left₀ h4 h3 2
      _ = lam ^ (2 : ℕ) * (4 * boundaryMajorant K τ ^ (2 : ℕ)) := by ring
  have hlim : ∀ᵐ τ : ℝ, Tendsto (fun ω : ℝ =>
      ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I) -
        centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
    have hτ : τ ≠ 0 := hτmem
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
    have hpt := tendsto_centeredSchurQuotient hzre hz0
    have h := ((hpt.sub (tendsto_const_nhds
      (x := centeredSchurLimit ((τ : ℂ) * Complex.I)))).norm.pow 2)
    simpa using h
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (fun τ : ℝ => lam ^ (2 : ℕ) * boundaryBound K τ) hmeas hdom
    ((integrable_boundaryBound K).const_mul (lam ^ (2 : ℕ))) hlim
  simpa using hDCT

theorem boundaryMajorant_smul_add {c1 c2 K1 K2 : ℝ} (h1 : 0 < c1) (h2 : 0 < c2) (τ : ℝ) :
    c1 * boundaryMajorant K1 τ + c2 * boundaryMajorant K2 τ
      = (c1 + c2) * boundaryMajorant ((c1 * K1 + c2 * K2) / (c1 + c2)) τ := by
  have hsum : 0 < c1 + c2 := by linarith
  by_cases hτ : |τ| ≤ 9
  · rw [boundaryMajorant_near hτ, boundaryMajorant_near hτ, boundaryMajorant_near hτ]
    field_simp
  · rw [not_le] at hτ
    rw [boundaryMajorant_far hτ, boundaryMajorant_far hτ, boundaryMajorant_far hτ]
    ring

theorem floorRemainderTransfer_eq_sub {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    floorRemainderTransfer ω z = mobiusCausalMultiplier ω z - centeredSchurQuotient ω z := by
  rw [mobiusCausalMultiplier_eq_add hω hz hz0]
  ring

theorem tendsto_floorRemainderTransfer {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    Tendsto (fun ω : ℝ => floorRemainderTransfer ω z) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (floorRemainderLimit z)) := by
  have hM := tendsto_mobiusCausalMultiplier hz hz0
  have hG := tendsto_centeredSchurQuotient hz hz0
  have hsub := hM.sub hG
  rw [show (1 : ℂ) / (1 + z) - centeredSchurLimit z = floorRemainderLimit z from rfl] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  exact (floorRemainderTransfer_eq_sub hω hz hz0).symm

theorem continuousOn_floorRemainderTransfer_line {ω : ℝ} (hω : 0 < ω) :
    ContinuousOn (fun τ : ℝ => floorRemainderTransfer ω ((τ : ℂ) * Complex.I))
      {t : ℝ | t ≠ 0} := by
  have hM := continuousOn_mobiusCausalMultiplier_line hω
  have hG := continuousOn_centeredSchurQuotient_line hω
  refine (hM.sub hG).congr ?_
  intro τ hτ0
  have hτ : τ ≠ 0 := hτ0
  have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hτ
  have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
  exact floorRemainderTransfer_eq_sub hω hzre hz0

theorem exists_uniform_floorRemainder_bound :
    ∃ ω₀ K lam : ℝ, 0 < ω₀ ∧ 0 ≤ K ∧ 0 < lam ∧
      ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ → ∀ τ : ℝ, τ ≠ 0 →
        ‖floorRemainderTransfer ω ((τ : ℂ) * Complex.I)‖ ≤ lam * boundaryMajorant K τ := by
  obtain ⟨ω₁, K₁, hω₁, hK₁, hM⟩ := exists_uniform_multiplier_bound
  obtain ⟨ω₂, K₂, lam₂, hω₂, hK₂, hlam₂, hG⟩ := exists_uniform_centered_bound
  refine ⟨min ω₁ ω₂, (1 * K₁ + lam₂ * K₂) / (1 + lam₂), 1 + lam₂, lt_min hω₁ hω₂, ?_,
    by linarith, ?_⟩
  · have : 0 ≤ 1 * K₁ + lam₂ * K₂ := by positivity
    positivity
  · intro ω hω hωle τ hτ
    have hω1 : ω ≤ ω₁ := le_trans hωle (min_le_left _ _)
    have hω2 : ω ≤ ω₂ := le_trans hωle (min_le_right _ _)
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
    rw [floorRemainderTransfer_eq_sub hω hzre hz0]
    refine le_trans (norm_sub_le _ _) ?_
    rw [← boundaryMajorant_smul_add (c1 := (1:ℝ)) (c2 := lam₂) one_pos hlam₂ τ, one_mul]
    exact add_le_add (hM ω hω hω1 τ hτ) (hG ω hω hω2 τ hτ)

/-- **Card `(7)` of the causal-graph law.**  The renormalized floor-remainder transform converges
to `H_0` in the boundary `L²` norm. -/
theorem tendsto_boundary_floorRemainder_energy :
    Tendsto (fun ω : ℝ => ∫ τ : ℝ, ‖floorRemainderTransfer ω ((τ : ℂ) * Complex.I) -
        floorRemainderLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨ω₀, K, lam, hω₀, hK, hlam, hbound⟩ := exists_uniform_floorRemainder_bound
  have hev : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ω ∧ ω ≤ ω₀ := by
    filter_upwards [Ioc_mem_nhdsGT hω₀] with ω hω
    exact ⟨hω.1, hω.2⟩
  have hlimfun : ∀ τ : ℝ, τ ≠ 0 →
      ‖floorRemainderLimit ((τ : ℂ) * Complex.I)‖ ≤ lam * boundaryMajorant K τ := by
    intro τ hτ
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
    have hlim := (tendsto_floorRemainderTransfer hzre hz0).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [hev] with ω hω
    exact hbound ω hω.1 hω.2 τ hτ
  have hcontlim : ContinuousOn (fun τ : ℝ => floorRemainderLimit ((τ : ℂ) * Complex.I))
      {t : ℝ | t ≠ 0} := by
    intro τ hτ0
    have hτ : τ ≠ 0 := hτ0
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hne1 : (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := line_ne_one (by simp) hτ
    have hζ0 : riemannZeta ((1 : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
      refine riemannZeta_ne_zero_of_one_le_re ?_
      simp
    have hz : ContinuousAt (fun t : ℝ => ((t : ℂ) * Complex.I)) τ := by
      have : Continuous (fun t : ℝ => ((t : ℂ) * Complex.I)) := by continuity
      exact this.continuousAt
    have hA : ContinuousAt (fun t : ℝ => riemannZeta (1 + (t : ℂ) * Complex.I)) τ :=
      continuousAt_zeta_line hne1
    have hlin0 : (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 0 := by
      intro h
      have hre : ((1 : ℂ) + (τ : ℂ) * Complex.I).re = 0 := by rw [h]; simp
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero] at hre
      linarith
    have hcont : ContinuousAt
        (fun t : ℝ => floorRemainderLimit ((t : ℂ) * Complex.I)) τ := by
      refine ContinuousAt.sub ?_ ?_
      · exact continuousAt_const.div (continuousAt_const.add hz) hlin0
      · exact continuousAt_const.div (hz.mul hA) (mul_ne_zero hz0 hζ0)
    exact hcont.continuousWithinAt
  have hmeas : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable (fun τ : ℝ =>
        ‖floorRemainderTransfer ω ((τ : ℂ) * Complex.I) -
          floorRemainderLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ)) volume := by
    filter_upwards [hev] with ω hω
    have h1 := aestronglyMeasurable_of_continuousOn_ne_zero
      (continuousOn_floorRemainderTransfer_line hω.1)
    have h2 := aestronglyMeasurable_of_continuousOn_ne_zero hcontlim
    exact ((h1.sub h2).norm.pow 2)
  have hdom : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ᵐ τ : ℝ,
      ‖‖floorRemainderTransfer ω ((τ : ℂ) * Complex.I) -
        floorRemainderLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ)‖ ≤ lam ^ (2 : ℕ) * boundaryBound K τ := by
    filter_upwards [hev] with ω hω
    filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
    have hτ : τ ≠ 0 := hτmem
    have h1 := hbound ω hω.1 hω.2 τ hτ
    have h2 := hlimfun τ hτ
    have h3 : ‖floorRemainderTransfer ω ((τ : ℂ) * Complex.I) -
        floorRemainderLimit ((τ : ℂ) * Complex.I)‖ ≤ 2 * (lam * boundaryMajorant K τ) := by
      refine le_trans (norm_sub_le _ _) ?_
      linarith
    have h4 : (0 : ℝ) ≤ ‖floorRemainderTransfer ω ((τ : ℂ) * Complex.I) -
        floorRemainderLimit ((τ : ℂ) * Complex.I)‖ := norm_nonneg _
    have hmaj : (0 : ℝ) ≤ boundaryMajorant K τ := boundaryMajorant_nonneg hK τ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), boundaryBound_eq K τ]
    calc ‖floorRemainderTransfer ω ((τ : ℂ) * Complex.I) -
          floorRemainderLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ)
        ≤ (2 * (lam * boundaryMajorant K τ)) ^ (2 : ℕ) := pow_le_pow_left₀ h4 h3 2
      _ = lam ^ (2 : ℕ) * (4 * boundaryMajorant K τ ^ (2 : ℕ)) := by ring
  have hlim : ∀ᵐ τ : ℝ, Tendsto (fun ω : ℝ =>
      ‖floorRemainderTransfer ω ((τ : ℂ) * Complex.I) -
        floorRemainderLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
    have hτ : τ ≠ 0 := hτmem
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
    have hpt := tendsto_floorRemainderTransfer hzre hz0
    have h := ((hpt.sub (tendsto_const_nhds
      (x := floorRemainderLimit ((τ : ℂ) * Complex.I)))).norm.pow 2)
    simpa using h
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (fun τ : ℝ => lam ^ (2 : ℕ) * boundaryBound K τ) hmeas hdom
    ((integrable_boundaryBound K).const_mul (lam ^ (2 : ℕ))) hlim
  simpa using hDCT


/-- The critical limit obeys the same uniform boundary majorant. -/
theorem exists_uniform_centeredSchurLimit_bound :
    ∃ K lam : ℝ, 0 ≤ K ∧ 0 < lam ∧ ∀ τ : ℝ, τ ≠ 0 →
      ‖centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ≤ lam * boundaryMajorant K τ := by
  obtain ⟨ω₀, K, lam, hω₀, hK, hlam, hbound⟩ := exists_uniform_centered_bound
  refine ⟨K, lam, hK, hlam, fun τ hτ => ?_⟩
  have hev : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ω ∧ ω ≤ ω₀ := by
    filter_upwards [Ioc_mem_nhdsGT hω₀] with ω hω
    exact ⟨hω.1, hω.2⟩
  have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hτ
  have hzre : (0 : ℝ) ≤ ((τ : ℂ) * Complex.I).re := by simp
  have hlim := (tendsto_centeredSchurQuotient hzre hz0).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [hev] with ω hω
  exact hbound ω hω.1 hω.2 τ hτ

/-- The critical limit has finite boundary energy. -/
theorem integrable_norm_sq_centeredSchurLimit :
    Integrable (fun τ : ℝ => ‖centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ)) := by
  obtain ⟨K, lam, hK, hlam, hbound⟩ := exists_uniform_centeredSchurLimit_bound
  have hcontlim : ContinuousOn (fun τ : ℝ => centeredSchurLimit ((τ : ℂ) * Complex.I))
      {t : ℝ | t ≠ 0} := by
    intro τ hτ0
    have hτ : τ ≠ 0 := hτ0
    have hz0 : ((τ : ℂ) * Complex.I) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
      exact hτ
    have hne1 : (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := line_ne_one (by simp) hτ
    have hζ0 : riemannZeta ((1 : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
      refine riemannZeta_ne_zero_of_one_le_re ?_
      simp
    have hz : ContinuousAt (fun t : ℝ => ((t : ℂ) * Complex.I)) τ := by
      have : Continuous (fun t : ℝ => ((t : ℂ) * Complex.I)) := by continuity
      exact this.continuousAt
    have hA : ContinuousAt (fun t : ℝ => riemannZeta (1 + (t : ℂ) * Complex.I)) τ :=
      continuousAt_zeta_line hne1
    exact (continuousAt_const.div (hz.mul hA) (mul_ne_zero hz0 hζ0)).continuousWithinAt
  refine Integrable.mono ((integrable_boundaryBound K).const_mul (lam ^ (2 : ℕ)))
    ((aestronglyMeasurable_of_continuousOn_ne_zero hcontlim).norm.pow 2) ?_
  filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
  have hτ : τ ≠ 0 := hτmem
  have h2 := hbound τ hτ
  have h4 : (0 : ℝ) ≤ ‖centeredSchurLimit ((τ : ℂ) * Complex.I)‖ := norm_nonneg _
  have hmaj : (0 : ℝ) ≤ boundaryMajorant K τ := boundaryMajorant_nonneg hK τ
  have hbb : (0 : ℝ) ≤ lam ^ (2 : ℕ) * boundaryBound K τ := by
    have := boundaryBound_nonneg K τ
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
    abs_of_nonneg hbb, boundaryBound_eq K τ]
  calc ‖centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ (2 : ℕ)
      ≤ (lam * boundaryMajorant K τ) ^ (2 : ℕ) := pow_le_pow_left₀ h4 h2 2
    _ ≤ lam ^ (2 : ℕ) * (4 * boundaryMajorant K τ ^ (2 : ℕ)) := by nlinarith [sq_nonneg (boundaryMajorant K τ)]

end RHTower
