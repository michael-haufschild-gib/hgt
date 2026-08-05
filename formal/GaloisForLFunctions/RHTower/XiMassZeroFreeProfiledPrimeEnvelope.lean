import GaloisForLFunctions.RHTower.XiMassPrimeGradedOpenCore
import GaloisForLFunctions.RHTower.XiWardZeroFreeMarginPrimeLogSampling

/-!
# Zero-free profiled growth of the mass--Xi prime source

The zero-free margin contains more information than the unconditional constant exponential type
`1/2`.  Functional-equation reflection transports the strict-right margin to every Xi divisor
copy.  Mass shifting contracts transverse displacement.  Splitting each trace term at Poisson
height

`|u| / log (|u| + 9)^9`

then balances two mechanisms: low points spend the zero-free margin, while high points spend half
of the real-time Laplace decay.  The resulting trace and literal von-Mangoldt source have the
unconditional envelope

`exp (|u|/2 - min(C, sigma/2) |u| / log(|u|+9)^9)`.

This is strictly smaller than every fixed constant times `exp (|u|/2)` at large height.  It does
not assert boundedness and uses no RH hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The zero-free margin on every multiplicity copy -/

/-- **The strict-right zero-free margin folded onto the full Xi divisor.**  Every multiplicity copy
has transverse displacement at most `1/2` minus the explicit margin evaluated at its Poisson
height. -/
theorem abs_xiSpectralPoint_im_le_half_sub_zeroFreeMargin (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| ≤
      1 / 2 - xiWardZeroFreeMargin (xiPoissonPoint q).re := by
  have hrightCase : ∀ r : XiZeroCopy,
      0 < (I * xiSpectralPoint r).re →
        |(xiSpectralPoint r).im| ≤
          1 / 2 - xiWardZeroFreeMargin (xiPoissonPoint r).re := by
    intro r hr
    let qr : XiRightZeroCopy := ⟨r, hr⟩
    have hmargin :
        xiWardZeroFreeMargin (xiRightCenteredZero qr).im =
          xiWardZeroFreeMargin (xiPoissonPoint r).re := by
      unfold xiWardZeroFreeMargin
      rw [abs_of_nonneg (xiPoissonPoint_re_nonneg r), xiPoissonPoint_re_eq_abs]
      congr 3
      simp [qr, xiRightCenteredZero, Complex.mul_im]
    have hzim : (xiSpectralPoint r).im < 0 := by
      simpa [Complex.mul_re] using hr
    have hbound := xiRightCenteredZero_re_le_half_sub_margin qr
    rw [hmargin] at hbound
    rw [abs_of_neg hzim]
    simpa [qr, xiRightCenteredZero, Complex.mul_re] using hbound
  rcases lt_trichotomy (I * xiSpectralPoint q).re 0 with hleft | hline | hright
  · let r := xiZeroCopyReflectEquiv q
    have hrpos : 0 < (I * xiSpectralPoint r).re := by
      dsimp only [r]
      rw [xiSpectralPoint_reflect]
      simp only [mul_neg, Complex.neg_re]
      linarith
    have hr := hrightCase r hrpos
    dsimp only [r] at hr
    rw [xiSpectralPoint_reflect, xiPoissonPoint_reflect] at hr
    simpa only [Complex.neg_im, abs_neg] using hr
  · have hzim : (xiSpectralPoint q).im = 0 := by
      simpa [Complex.mul_re] using hline
    rw [hzim, abs_zero]
    linarith [xiWardZeroFreeMargin_le_half (xiPoissonPoint q).re]
  · exact hrightCase q hright

/-! ## The profile envelope and termwise split -/

/-- The subcritical zero-free profile on a fixed positive line. -/
def xiMassZeroFreeProfileEnvelope (σ u : ℝ) : ℝ :=
  Real.exp
    (|u| / 2 - min xiWardZeroFreeMarginC (σ / 2) * |u| /
      Real.log (|u| + 9) ^ (9 : ℕ))

/-- The profile is at least one, so a uniformly bounded auxiliary channel can be absorbed into it. -/
theorem one_le_xiMassZeroFreeProfileEnvelope {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    1 ≤ xiMassZeroFreeProfileEnvelope σ u := by
  have hL : 1 ≤ Real.log (|u| + 9) :=
    le_of_lt (one_lt_log_abs_add_nine u)
  have hL9 : 1 ≤ Real.log (|u| + 9) ^ (9 : ℕ) := by
    calc
      (1 : ℝ) = 1 ^ (9 : ℕ) := by norm_num
      _ ≤ Real.log (|u| + 9) ^ (9 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hL 9
  have hD0 : 0 ≤ min xiWardZeroFreeMarginC (σ / 2) := by
    exact (lt_min xiWardZeroFreeMarginC_pos (by linarith)).le
  have hDhalf : min xiWardZeroFreeMarginC (σ / 2) ≤ 1 / 2 :=
    le_trans (min_le_left _ _) xiWardZeroFreeMarginC_le_half
  have hdiv :
      min xiWardZeroFreeMarginC (σ / 2) /
          Real.log (|u| + 9) ^ (9 : ℕ) ≤ 1 / 2 := by
    exact (div_le_self hD0 hL9).trans hDhalf
  unfold xiMassZeroFreeProfileEnvelope
  apply Real.one_le_exp
  have hmul := mul_le_mul_of_nonneg_left hdiv (abs_nonneg u)
  rw [show min xiWardZeroFreeMarginC (σ / 2) * |u| /
      Real.log (|u| + 9) ^ (9 : ℕ) =
      |u| * (min xiWardZeroFreeMarginC (σ / 2) /
        Real.log (|u| + 9) ^ (9 : ℕ)) by ring]
  linarith

/-- Mass shifting preserves the full height-dependent zero-free margin. -/
theorem abs_im_xiMassFamily_le_half_sub_zeroFreeMargin
    {a : ℝ} (ha : 1 / 2 ≤ a) (q : XiZeroCopy) :
    |((xiMassFamily ha).pt q).im| ≤
      1 / 2 - xiWardZeroFreeMargin (xiPoissonPoint q).re :=
  (abs_im_xiMassFamily_le_abs_im_xiSpectralPoint ha q).trans
    (abs_xiSpectralPoint_im_le_half_sub_zeroFreeMargin q)

/-- **Low/high profile split for one mass trace term.**  A low Poisson height spends the zero-free
margin; a high height spends half the Laplace weight. -/
theorem norm_xiMassFamily_term_le_zeroFreeProfile
    {a σ u : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ) (q : XiZeroCopy) :
    ‖(xiMassFamily ha).term ((σ : ℂ) + u * I) q‖ ≤
      xiMassZeroFreeProfileEnvelope σ u *
        ((xiMassFamily ha).weight σ q + (xiMassFamily ha).weight (σ / 2) q) := by
  let U : ℝ := |u|
  let L9 : ℝ := Real.log (|u| + 9) ^ (9 : ℕ)
  let D : ℝ := min xiWardZeroFreeMarginC (σ / 2)
  have hU : 0 ≤ U := abs_nonneg u
  have hL : 1 ≤ Real.log (|u| + 9) :=
    le_of_lt (one_lt_log_abs_add_nine u)
  have hL9 : 1 ≤ L9 := by
    dsimp only [L9]
    calc
      (1 : ℝ) = 1 ^ (9 : ℕ) := by norm_num
      _ ≤ Real.log (|u| + 9) ^ (9 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hL 9
  have hL9pos : 0 < L9 := lt_of_lt_of_le zero_lt_one hL9
  have hDleC : D ≤ xiWardZeroFreeMarginC := min_le_left _ _
  have hDleSigma : D ≤ σ / 2 := min_le_right _ _
  have hτre : (((σ : ℂ) + u * I)).re = σ := by
    norm_num [Complex.mul_re]
  have hτim : (((σ : ℂ) + u * I)).im = u := by
    norm_num [Complex.mul_im]
  have hmassMargin := abs_im_xiMassFamily_le_half_sub_zeroFreeMargin ha q
  by_cases hlow : (xiPoissonPoint q).re ≤ U / L9
  · have hGleU : U / L9 ≤ U := div_le_self hU hL9
    have hRU : (xiPoissonPoint q).re ≤ U := hlow.trans hGleU
    have hmanti :
        xiWardZeroFreeMargin U ≤ xiWardZeroFreeMargin (xiPoissonPoint q).re := by
      apply xiWardZeroFreeMargin_anti
      rw [abs_of_nonneg (xiPoissonPoint_re_nonneg q), abs_of_nonneg hU]
      exact hRU
    have hmU : xiWardZeroFreeMargin U = xiWardZeroFreeMarginC / L9 := by
      unfold xiWardZeroFreeMargin
      rw [abs_of_nonneg hU]
    have hJ : |((xiMassFamily ha).pt q).im| ≤
        1 / 2 - xiWardZeroFreeMarginC / L9 := by
      rw [hmU] at hmanti
      linarith
    have huJ : u * ((xiMassFamily ha).pt q).im ≤
        U * (1 / 2 - xiWardZeroFreeMarginC / L9) := by
      calc
        u * ((xiMassFamily ha).pt q).im ≤
            |u * ((xiMassFamily ha).pt q).im| := le_abs_self _
        _ = U * |((xiMassFamily ha).pt q).im| := by
          rw [abs_mul]
        _ ≤ U * (1 / 2 - xiWardZeroFreeMarginC / L9) :=
          mul_le_mul_of_nonneg_left hJ hU
    have hcorr : D * U / L9 ≤ xiWardZeroFreeMarginC * U / L9 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDleC hU) hL9pos.le
    have huJ' : u * ((xiMassFamily ha).pt q).im ≤
        U / 2 - xiWardZeroFreeMarginC * U / L9 := by
      calc
        u * ((xiMassFamily ha).pt q).im ≤
            U * (1 / 2 - xiWardZeroFreeMarginC / L9) := huJ
        _ = U / 2 - xiWardZeroFreeMarginC * U / L9 := by ring
    have hexp :
        -(σ * ((xiMassFamily ha).pt q).re -
            u * ((xiMassFamily ha).pt q).im) ≤
          (U / 2 - D * U / L9) +
            -(σ * ((xiMassFamily ha).pt q).re) := by
      calc
        -(σ * ((xiMassFamily ha).pt q).re -
            u * ((xiMassFamily ha).pt q).im) =
            -(σ * ((xiMassFamily ha).pt q).re) +
              u * ((xiMassFamily ha).pt q).im := by ring
        _ ≤ -(σ * ((xiMassFamily ha).pt q).re) +
            (U / 2 - xiWardZeroFreeMarginC * U / L9) := by linarith
        _ ≤ -(σ * ((xiMassFamily ha).pt q).re) +
            (U / 2 - D * U / L9) :=
          by linarith [sub_le_sub_left hcorr (U / 2)]
        _ = (U / 2 - D * U / L9) +
            -(σ * ((xiMassFamily ha).pt q).re) := by ring
    have hprimary :
        ‖(xiMassFamily ha).term ((σ : ℂ) + u * I) q‖ ≤
          xiMassZeroFreeProfileEnvelope σ u *
            (xiMassFamily ha).weight σ q := by
      rw [HTGeometry.AbstractSpectralFamily.norm_term,
        xiMassZeroFreeProfileEnvelope,
        HTGeometry.AbstractSpectralFamily.weight, ← Real.exp_add, hτre, hτim]
      dsimp only [U, L9, D] at hexp ⊢
      exact Real.exp_le_exp.mpr hexp
    calc
      ‖(xiMassFamily ha).term ((σ : ℂ) + u * I) q‖ ≤
          xiMassZeroFreeProfileEnvelope σ u *
            (xiMassFamily ha).weight σ q := hprimary
      _ ≤ xiMassZeroFreeProfileEnvelope σ u *
          ((xiMassFamily ha).weight σ q +
            (xiMassFamily ha).weight (σ / 2) q) := by
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_right (Real.exp_pos _).le
        · exact (Real.exp_pos _).le
  · have hRG : U / L9 < (xiPoissonPoint q).re := lt_of_not_ge hlow
    have hRM : (xiPoissonPoint q).re < ((xiMassFamily ha).pt q).re := by
      change (xiPoissonPoint q).re <
        (HTGeometry.csqrt (xiMassArg a q)).re
      rw [HTGeometry.csqrt_re]
      exact xiPoissonPoint_re_lt_csqrtRe ha q
    have hJhalf : |((xiMassFamily ha).pt q).im| ≤ 1 / 2 :=
      ((xiMassFamily ha).abs_im_lt q).le
    have huJ : u * ((xiMassFamily ha).pt q).im ≤ U / 2 := by
      calc
        u * ((xiMassFamily ha).pt q).im ≤
            |u * ((xiMassFamily ha).pt q).im| := le_abs_self _
        _ = U * |((xiMassFamily ha).pt q).im| := by
          rw [abs_mul]
        _ ≤ U * (1 / 2) := mul_le_mul_of_nonneg_left hJhalf hU
        _ = U / 2 := by ring
    have hG0 : 0 ≤ U / L9 := div_nonneg hU hL9pos.le
    have hcorr1 : D * (U / L9) ≤ (σ / 2) * (U / L9) :=
      mul_le_mul_of_nonneg_right hDleSigma hG0
    have hcorr2 : (σ / 2) * (U / L9) ≤
        (σ / 2) * ((xiMassFamily ha).pt q).re := by
      exact mul_le_mul_of_nonneg_left (hRG.trans hRM).le (by linarith)
    have hcorr : D * U / L9 ≤
        (σ / 2) * ((xiMassFamily ha).pt q).re := by
      rw [show D * U / L9 = D * (U / L9) by ring]
      exact hcorr1.trans hcorr2
    have hexp :
        -(σ * ((xiMassFamily ha).pt q).re -
            u * ((xiMassFamily ha).pt q).im) ≤
          (U / 2 - D * U / L9) +
            -((σ / 2) * ((xiMassFamily ha).pt q).re) := by
      calc
        -(σ * ((xiMassFamily ha).pt q).re -
            u * ((xiMassFamily ha).pt q).im) =
            -(σ * ((xiMassFamily ha).pt q).re) +
              u * ((xiMassFamily ha).pt q).im := by ring
        _ ≤ -(σ * ((xiMassFamily ha).pt q).re) + U / 2 := by linarith
        _ = -((σ / 2) * ((xiMassFamily ha).pt q).re) +
            (U / 2 - (σ / 2) * ((xiMassFamily ha).pt q).re) := by ring
        _ ≤ -((σ / 2) * ((xiMassFamily ha).pt q).re) +
            (U / 2 - D * U / L9) :=
          by linarith [sub_le_sub_left hcorr (U / 2)]
        _ = (U / 2 - D * U / L9) +
            -((σ / 2) * ((xiMassFamily ha).pt q).re) := by ring
    have hprimary :
        ‖(xiMassFamily ha).term ((σ : ℂ) + u * I) q‖ ≤
          xiMassZeroFreeProfileEnvelope σ u *
            (xiMassFamily ha).weight (σ / 2) q := by
      rw [HTGeometry.AbstractSpectralFamily.norm_term,
        xiMassZeroFreeProfileEnvelope,
        HTGeometry.AbstractSpectralFamily.weight, ← Real.exp_add, hτre, hτim]
      dsimp only [U, L9, D] at hexp ⊢
      exact Real.exp_le_exp.mpr hexp
    calc
      ‖(xiMassFamily ha).term ((σ : ℂ) + u * I) q‖ ≤
          xiMassZeroFreeProfileEnvelope σ u *
            (xiMassFamily ha).weight (σ / 2) q := hprimary
      _ ≤ xiMassZeroFreeProfileEnvelope σ u *
          ((xiMassFamily ha).weight σ q +
            (xiMassFamily ha).weight (σ / 2) q) := by
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_left (Real.exp_pos _).le
        · exact (Real.exp_pos _).le

/-! ## Summed trace and prime-source envelopes -/

/-- **Unconditional profiled mass-trace bound.** -/
theorem norm_xiMassFamily_traceC_le_zeroFreeProfile
    {a σ : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ) (u : ℝ) :
    ‖(xiMassFamily ha).traceC ((σ : ℂ) + u * I)‖ ≤
      ((xiMassFamily ha).traceReal σ +
        (xiMassFamily ha).traceReal (σ / 2)) *
          xiMassZeroFreeProfileEnvelope σ u := by
  have hτ : 0 < (((σ : ℂ) + u * I)).re := by
    simpa [Complex.mul_re] using hσ
  have hσ2 : 0 < σ / 2 := by linarith
  have hnorm := (xiMassFamily ha).summable_norm_term hτ
  have hwσ := (xiMassFamily ha).summable_weight hσ
  have hwσ2 := (xiMassFamily ha).summable_weight hσ2
  have hmajor : Summable (fun q : XiZeroCopy =>
      xiMassZeroFreeProfileEnvelope σ u *
        ((xiMassFamily ha).weight σ q +
          (xiMassFamily ha).weight (σ / 2) q)) :=
    (hwσ.add hwσ2).mul_left _
  calc
    ‖(xiMassFamily ha).traceC ((σ : ℂ) + u * I)‖ ≤
        ∑' q : XiZeroCopy,
          ‖(xiMassFamily ha).term ((σ : ℂ) + u * I) q‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : XiZeroCopy,
        xiMassZeroFreeProfileEnvelope σ u *
          ((xiMassFamily ha).weight σ q +
            (xiMassFamily ha).weight (σ / 2) q) :=
      Summable.tsum_le_tsum
        (fun q => norm_xiMassFamily_term_le_zeroFreeProfile ha hσ q)
        hnorm hmajor
    _ = xiMassZeroFreeProfileEnvelope σ u *
        ((xiMassFamily ha).traceReal σ +
          (xiMassFamily ha).traceReal (σ / 2)) := by
      rw [tsum_mul_left]
      unfold HTGeometry.AbstractSpectralFamily.traceReal
      congr 1
      exact hwσ.tsum_add hwσ2
    _ = ((xiMassFamily ha).traceReal σ +
          (xiMassFamily ha).traceReal (σ / 2)) *
        xiMassZeroFreeProfileEnvelope σ u := by ring

/-- **Unconditional profiled bound for the literal von-Mangoldt bottom integral.**  The Gamma
channel is uniformly bounded and is absorbed because the profile is at least one. -/
theorem norm_xiMassBottomPrimeIntegral_le_zeroFreeProfile
    {a c σ : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hσ : 0 < σ) (u : ℝ) :
    ‖xiMassBottomPrimeIntegral a c ((σ : ℂ) + u * I)‖ ≤
      (‖(Real.pi : ℂ) * I‖ *
          ((xiMassFamily (show 1 / 2 ≤ a by linarith)).traceReal σ +
            (xiMassFamily (show 1 / 2 ≤ a by linarith)).traceReal (σ / 2)) +
        xiMassBottomArchUniformBound a σ) *
          xiMassZeroFreeProfileEnvelope σ u := by
  have ha : 1 / 2 ≤ a := by linarith
  have hτ : 0 < (((σ : ℂ) + u * I)).re := by
    simpa [Complex.mul_re] using hσ
  let B : ℝ := xiMassBottomArchUniformBound a σ
  have hB : 0 ≤ B := xiMassBottomArchUniformBound_nonneg
    (show 0 < a by linarith) hσ
  have hE : 1 ≤ xiMassZeroFreeProfileEnvelope σ u :=
    one_le_xiMassZeroFreeProfileEnvelope hσ u
  have hBE : B ≤ B * xiMassZeroFreeProfileEnvelope σ u :=
    le_mul_of_one_le_right hB hE
  have htrace := norm_xiMassFamily_traceC_le_zeroFreeProfile ha hσ u
  rw [xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch hhalf hca hτ]
  calc
    ‖I * (∫ x : ℝ,
          xiMassBottomSourceIntegrand a c ((σ : ℂ) + u * I) x) +
        xiMassBottomArchIntegral a c ((σ : ℂ) + u * I)‖ ≤
      ‖I * (∫ x : ℝ,
          xiMassBottomSourceIntegrand a c ((σ : ℂ) + u * I) x)‖ +
        ‖xiMassBottomArchIntegral a c ((σ : ℂ) + u * I)‖ :=
      norm_add_le _ _
    _ = ‖∫ x : ℝ,
          xiMassBottomSourceIntegrand a c ((σ : ℂ) + u * I) x‖ +
        ‖xiMassBottomArchIntegral a c ((σ : ℂ) + u * I)‖ := by simp
    _ ≤ ‖(Real.pi : ℂ) * I‖ *
          ‖(xiMassFamily ha).traceC ((σ : ℂ) + u * I)‖ + B := by
      apply add_le_add
      · rw [integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace
          hhalf hca hτ, norm_mul]
      · exact norm_integral_xiMassBottomArchIntegrand_le_uniform
          hhalf hca hσ
    _ ≤ ‖(Real.pi : ℂ) * I‖ *
          (((xiMassFamily ha).traceReal σ +
              (xiMassFamily ha).traceReal (σ / 2)) *
            xiMassZeroFreeProfileEnvelope σ u) + B := by
      have hmul := mul_le_mul_of_nonneg_left htrace
        (norm_nonneg ((Real.pi : ℂ) * I))
      linarith
    _ ≤ ‖(Real.pi : ℂ) * I‖ *
          (((xiMassFamily ha).traceReal σ +
              (xiMassFamily ha).traceReal (σ / 2)) *
            xiMassZeroFreeProfileEnvelope σ u) +
          B * xiMassZeroFreeProfileEnvelope σ u := by linarith
    _ = (‖(Real.pi : ℂ) * I‖ *
          ((xiMassFamily ha).traceReal σ +
            (xiMassFamily ha).traceReal (σ / 2)) + B) *
          xiMassZeroFreeProfileEnvelope σ u := by ring

end

end RHTower
