import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62MellinKernel

/-!
# Chen--Gupta--Li Lemma 6.2: initial Mellin representation

This module proves the pre-contour part of CGL equation (6.3).  It turns the
compact physical character sum from equation (6.1) into the line-`Re(s)=2`
Mellin integral of `H(s) N^s L(s-it, χ)`.  The Fubini step is proved using a
closed `n⁻²` majorant; neither it nor the exported identity accepts an analytic
convergence premise.
-/

open Complex MeasureTheory
open scoped LSeries.notation

noncomputable section

namespace RHTower

private theorem cglInitialMellin_phase_power_normalization
    (N : CGLPositiveLength) {n : ℕ} (hn : 0 < n) (t : ℝ) (s : ℂ) :
    cglMellinPhase t N.value * cglMellinPhase t ((n : ℝ) / N.value) *
        (((n : ℝ) / N.value : ℝ) : ℂ) ^ (-s) =
      (N.value : ℂ) ^ s * (n : ℂ) ^ (-(s - (t : ℂ) * I)) := by
  have hN : (N.value : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt N.positive
  have hnreal : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hratio : ((n : ℝ) / N.value) ≠ 0 := div_ne_zero hnreal hN
  have hlog : Real.log (n : ℝ) =
      Real.log N.value + Real.log ((n : ℝ) / N.value) := by
    rw [← Real.log_mul hN hratio]
    congr 1
    field_simp
  have hNcast : (N.value : ℂ) = ((N.value : ℝ) : ℂ) := by norm_cast
  have hncast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
  have hNnonneg : (0 : ℝ) ≤ N.value := by positivity
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hrationonneg : (0 : ℝ) ≤ (n : ℝ) / N.value := by positivity
  rw [hNcast, hncast]
  unfold cglMellinPhase
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hratio),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by
      exact_mod_cast Nat.ne_of_gt N.positive)),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by
      exact_mod_cast Nat.ne_of_gt hn))]
  rw [← Complex.ofReal_log hNnonneg,
    ← Complex.ofReal_log hnnonneg,
    ← Complex.ofReal_log hrationonneg]
  rw [hlog]
  conv_lhs => rw [← Complex.exp_add, ← Complex.exp_add]
  conv_rhs => rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- The `Re(s)=2` point at height `u` in CGL's initial Mellin integral. -/
def cglInitialMellinLinePoint (u : ℝ) : ℂ :=
  (2 : ℂ) + (u : ℂ) * I

private def cglInitialMellinTerm
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  if n = 0 then 0 else
    cglMellinPhase t N.value * χ n * cglMellinPhase t ((n : ℝ) / N.value) *
      (((n : ℝ) / N.value : ℝ) : ℂ) ^ (-cglInitialMellinLinePoint u) *
        cglLemma62MellinTransform w (cglInitialMellinLinePoint u)

/-- The exact line-`Re(s)=2` integrand in CGL equation (6.3), before the
imprimitive Euler-factor replacement and contour shift. -/
def cglInitialMellinIntegrand
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t u : ℝ) : ℂ :=
  cglLemma62MellinTransform w (cglInitialMellinLinePoint u) *
    (N.value : ℂ) ^ (cglInitialMellinLinePoint u) *
      LSeries (fun n : ℕ => χ n)
        (cglInitialMellinLinePoint u - (t : ℂ) * I)

/-- The same initial-line integrand in its meromorphically continuable
`LFunction` form. -/
def cglInitialLFunctionIntegrand
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t u : ℝ) : ℂ :=
  cglLemma62MellinTransform w (cglInitialMellinLinePoint u) *
    (N.value : ℂ) ^ (cglInitialMellinLinePoint u) *
      DirichletCharacter.LFunction χ
        (cglInitialMellinLinePoint u - (t : ℂ) * I)

private theorem cglInitialMellinTerm_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) (n : ℕ) :
    Integrable (cglInitialMellinTerm w N Q χ t n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · change Integrable (fun _ : ℝ => (0 : ℂ))
    simp
  let Hline : ℝ → ℂ := fun u =>
    cglLemma62MellinTransform w (cglInitialMellinLinePoint u)
  have hH : Integrable Hline := by
    change Integrable (fun u : ℝ =>
      cglLemma62MellinTransform w ((2 : ℂ) + (u : ℂ) * I))
    exact cglLemma62_mellinTransform_verticalIntegrable w 2
  have hN : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : 0 < (n : ℝ) / N.value := div_pos hnR hN
  unfold cglInitialMellinTerm
  simp only [if_neg hn.ne']
  have hline : Continuous (fun u : ℝ => -cglInitialMellinLinePoint u) := by
    unfold cglInitialMellinLinePoint
    fun_prop
  have hpow : Continuous (fun u : ℝ =>
      (((n : ℝ) / N.value : ℝ) : ℂ) ^ (-cglInitialMellinLinePoint u)) := by
    exact Continuous.const_cpow hline
      (Or.inl (Complex.ofReal_ne_zero.mpr hratio.ne'))
  refine Integrable.mono' (hH.norm.const_mul (((n : ℝ) / N.value) ^ (-2 : ℝ))) ?_ ?_
  · have hmeas : AEStronglyMeasurable (fun u : ℝ =>
        cglMellinPhase t N.value * χ n * cglMellinPhase t ((n : ℝ) / N.value) *
          (((n : ℝ) / N.value : ℝ) : ℂ) ^ (-cglInitialMellinLinePoint u)) :=
      (((continuous_const.mul continuous_const).mul continuous_const).mul hpow).aestronglyMeasurable
    exact hmeas.mul hH.aestronglyMeasurable
  filter_upwards with u
  change ‖cglMellinPhase t N.value * χ n * cglMellinPhase t ((n : ℝ) / N.value) *
      (((n : ℝ) / N.value : ℝ) : ℂ) ^ (-cglInitialMellinLinePoint u) * Hline u‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_cglMellinPhase,
    norm_cglMellinPhase,
    Complex.norm_cpow_eq_rpow_re_of_pos hratio]
  have hre : (-cglInitialMellinLinePoint u).re = (-2 : ℝ) := by
    simp [cglInitialMellinLinePoint]
  rw [hre]
  have hcoeff := χ.norm_le_one (n : ZMod Q.value)
  calc
    1 * ‖χ (n : ZMod Q.value)‖ * 1 *
        ((n : ℝ) / N.value) ^ (-2 : ℝ) * ‖Hline u‖ =
      ‖χ (n : ZMod Q.value)‖ *
        (((n : ℝ) / N.value) ^ (-2 : ℝ) * ‖Hline u‖) := by ring
    _ ≤ 1 * (((n : ℝ) / N.value) ^ (-2 : ℝ) * ‖Hline u‖) :=
      mul_le_mul_of_nonneg_right hcoeff
        (mul_nonneg (Real.rpow_nonneg hratio.le _) (norm_nonneg _))
    _ = _ := by ring

private theorem cglInitialMellin_ratio_neg_two
    (N : CGLPositiveLength) {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) / N.value) ^ (-2 : ℝ) =
      (N.value : ℝ) ^ 2 * (n : ℝ) ^ (-2 : ℝ) := by
  have hN : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.div_rpow hnR.le hN.le, Real.rpow_neg hnR.le,
    Real.rpow_neg hN.le]
  field_simp [hN.ne']
  norm_num

private theorem cglInitialMellinTerm_integral_norm_le
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) (n : ℕ) :
    (∫ u : ℝ, ‖cglInitialMellinTerm w N Q χ t n u‖) ≤
      (N.value : ℝ) ^ 2 * (n : ℝ) ^ (-2 : ℝ) *
        ∫ u : ℝ, ‖cglLemma62MellinTransform w (cglInitialMellinLinePoint u)‖ := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [cglInitialMellinTerm, Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0)]
  let Hline : ℝ → ℂ := fun u =>
    cglLemma62MellinTransform w (cglInitialMellinLinePoint u)
  have hH : Integrable Hline := by
    change Integrable (fun u : ℝ =>
      cglLemma62MellinTransform w ((2 : ℂ) + (u : ℂ) * I))
    exact cglLemma62_mellinTransform_verticalIntegrable w 2
  have hN : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : 0 < (n : ℝ) / N.value := div_pos hnR hN
  have hpoint : ∀ u : ℝ,
      ‖cglInitialMellinTerm w N Q χ t n u‖ ≤
        ((n : ℝ) / N.value) ^ (-2 : ℝ) * ‖Hline u‖ := by
    intro u
    unfold cglInitialMellinTerm
    simp only [if_neg hn.ne']
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_cglMellinPhase,
      norm_cglMellinPhase,
      Complex.norm_cpow_eq_rpow_re_of_pos hratio]
    have hre : (-cglInitialMellinLinePoint u).re = (-2 : ℝ) := by
      simp [cglInitialMellinLinePoint]
    rw [hre]
    have hcoeff := χ.norm_le_one (n : ZMod Q.value)
    calc
      1 * ‖χ (n : ZMod Q.value)‖ * 1 *
          ((n : ℝ) / N.value) ^ (-2 : ℝ) * ‖Hline u‖ =
        ‖χ (n : ZMod Q.value)‖ *
          (((n : ℝ) / N.value) ^ (-2 : ℝ) * ‖Hline u‖) := by ring
      _ ≤ 1 * (((n : ℝ) / N.value) ^ (-2 : ℝ) * ‖Hline u‖) :=
        mul_le_mul_of_nonneg_right hcoeff
          (mul_nonneg (Real.rpow_nonneg hratio.le _) (norm_nonneg _))
      _ = _ := by ring
  calc
    (∫ u : ℝ, ‖cglInitialMellinTerm w N Q χ t n u‖) ≤
        ∫ u : ℝ, ((n : ℝ) / N.value) ^ (-2 : ℝ) * ‖Hline u‖ :=
      integral_mono (cglInitialMellinTerm_integrable w N Q χ t n).norm
        (hH.norm.const_mul _) hpoint
    _ = ((n : ℝ) / N.value) ^ (-2 : ℝ) * ∫ u : ℝ, ‖Hline u‖ :=
      integral_const_mul _ _
    _ = _ := by
      rw [cglInitialMellin_ratio_neg_two N hn]

private theorem cglInitialMellinTerm_integral_norm_summable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖cglInitialMellinTerm w N Q χ t n u‖) := by
  let V : ℝ := ∫ u : ℝ,
    ‖cglLemma62MellinTransform w (cglInitialMellinLinePoint u)‖
  have hrpow : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
    refine (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).congr fun n => ?_
    rw [← Real.rpow_neg (Nat.cast_nonneg n)]
  have hbound : ∀ n : ℕ,
      (∫ u : ℝ, ‖cglInitialMellinTerm w N Q χ t n u‖) ≤
        (N.value : ℝ) ^ 2 * (n : ℝ) ^ (-2 : ℝ) * V := by
    intro n
    simpa only [V] using cglInitialMellinTerm_integral_norm_le w N Q χ t n
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _) hbound ?_
  refine (hrpow.mul_left ((N.value : ℝ) ^ 2 * V)).congr ?_
  intro n
  ring

private theorem cglInitialMellinTerm_integral_eq
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) (n : ℕ) :
    (∫ u : ℝ, cglInitialMellinTerm w N Q χ t n u) =
      (2 * Real.pi : ℝ) •
        (cglMellinPhase t N.value *
          (χ n * cglSmoothBumpHt w.toCGLSmoothBump t ((n : ℝ) / N.value))) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have hwzero : w.toCGLSmoothBump.value (0 : ℝ) = 0 :=
      w.toCGLSmoothBump.outside_support 0 (by norm_num)
    simp [cglInitialMellinTerm, cglSmoothBumpHt_apply,
      cglSmoothBumpHtValue, hwzero]
  have hN : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : 0 < (n : ℝ) / N.value := div_pos hnR hN
  have hinv := cglLemma62_mellinInv_two_eq_squaredCutoff w hratio
  rw [mellinInv] at hinv
  have hJ :
      (∫ u : ℝ,
        (((n : ℝ) / N.value : ℝ) : ℂ) ^ (-cglInitialMellinLinePoint u) *
          cglLemma62MellinTransform w (cglInitialMellinLinePoint u)) =
        (2 * Real.pi : ℝ) •
          (w.toCGLSmoothBump.value ((n : ℝ) / N.value) *
            w.toCGLSmoothBump.value ((n : ℝ) / N.value)) := by
    rw [← hinv, smul_smul]
    have hpi : (2 * Real.pi : ℝ) * (1 / (2 * Real.pi)) = 1 := by
      field_simp
    rw [hpi, one_smul]
    rfl
  unfold cglInitialMellinTerm
  simp only [if_neg hn.ne']
  rw [show (fun u : ℝ =>
      cglMellinPhase t N.value * χ n * cglMellinPhase t ((n : ℝ) / N.value) *
        (((n : ℝ) / N.value : ℝ) : ℂ) ^ (-cglInitialMellinLinePoint u) *
          cglLemma62MellinTransform w (cglInitialMellinLinePoint u)) =
        fun u : ℝ =>
          (cglMellinPhase t N.value * χ n *
            cglMellinPhase t ((n : ℝ) / N.value)) *
              ((((n : ℝ) / N.value : ℝ) : ℂ) ^ (-cglInitialMellinLinePoint u) *
                cglLemma62MellinTransform w (cglInitialMellinLinePoint u)) by
      funext u
      ring]
  rw [integral_const_mul, hJ, cglSmoothBumpHt_apply, cglSmoothBumpHtValue]
  rw [Complex.real_smul, Complex.real_smul]
  ring

private theorem cglInitialMellinTerm_tsum_eq_integrand
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t u : ℝ) :
    (∑' n : ℕ, cglInitialMellinTerm w N Q χ t n u) =
      cglInitialMellinIntegrand w N Q χ t u := by
  unfold cglInitialMellinIntegrand LSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [cglInitialMellinTerm, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne']
    unfold cglInitialMellinTerm
    simp only [if_neg hn.ne']
    calc
      cglMellinPhase t N.value * χ n * cglMellinPhase t ((n : ℝ) / N.value) *
          (((n : ℝ) / N.value : ℝ) : ℂ) ^ (-cglInitialMellinLinePoint u) *
            cglLemma62MellinTransform w (cglInitialMellinLinePoint u) =
        χ n * (cglMellinPhase t N.value *
          cglMellinPhase t ((n : ℝ) / N.value) *
            (((n : ℝ) / N.value : ℝ) : ℂ) ^ (-cglInitialMellinLinePoint u)) *
              cglLemma62MellinTransform w (cglInitialMellinLinePoint u) := by ring
      _ = χ n * ((N.value : ℂ) ^ cglInitialMellinLinePoint u *
          (n : ℂ) ^ (-(cglInitialMellinLinePoint u - (t : ℂ) * I))) *
            cglLemma62MellinTransform w (cglInitialMellinLinePoint u) := by
        rw [cglInitialMellin_phase_power_normalization N hn t]
      _ = cglLemma62MellinTransform w (cglInitialMellinLinePoint u) *
          (N.value : ℂ) ^ cglInitialMellinLinePoint u *
            (χ n / (n : ℂ) ^ (cglInitialMellinLinePoint u - (t : ℂ) * I)) := by
        rw [Complex.cpow_neg]
        ring

/-- **CGL equation (6.3), initial line.**  The normalized physical
character sum equals the line-`Re(s)=2` Mellin integral before its Euler-factor
rewrite and contour shift.  All convergence and interchange obligations are
closed internally. -/
theorem cglLemma62_smoothedCharacterSum_initialMellin
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) :
    (2 * Real.pi : ℝ) •
      (cglMellinPhase t N.value * cglLemma62SmoothedCharacterSum w N Q χ t) =
      ∫ u : ℝ, cglInitialMellinIntegrand w N Q χ t u := by
  have hFint : ∀ n : ℕ, Integrable (cglInitialMellinTerm w N Q χ t n) :=
    fun n => cglInitialMellinTerm_integrable w N Q χ t n
  have hFsum := cglInitialMellinTerm_integral_norm_summable w N Q χ t
  have hswap := hasSum_integral_of_summable_integral_norm hFint hFsum
  calc
    (2 * Real.pi : ℝ) •
        (cglMellinPhase t N.value * cglLemma62SmoothedCharacterSum w N Q χ t) =
      ∑' n : ℕ, (2 * Real.pi : ℝ) •
        (cglMellinPhase t N.value *
          (χ n * cglSmoothBumpHt w.toCGLSmoothBump t ((n : ℝ) / N.value))) := by
        unfold cglLemma62SmoothedCharacterSum
        rw [Complex.real_smul, ← tsum_mul_left, ← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [Complex.real_smul]
    _ = ∑' n : ℕ, ∫ u : ℝ, cglInitialMellinTerm w N Q χ t n u := by
      apply tsum_congr
      intro n
      exact (cglInitialMellinTerm_integral_eq w N Q χ t n).symm
    _ = ∫ u : ℝ, ∑' n : ℕ, cglInitialMellinTerm w N Q χ t n u := hswap.tsum_eq
    _ = ∫ u : ℝ, cglInitialMellinIntegrand w N Q χ t u := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u =>
        cglInitialMellinTerm_tsum_eq_integrand w N Q χ t u

/-- **CGL equation (6.3), initial line in `LFunction` form.**  This closed
identity is the exact starting point for the induced-character rewrite and
the subsequent contour shift. -/
theorem cglLemma62_smoothedCharacterSum_initialMellin_lfunction
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) :
    (2 * Real.pi : ℝ) •
      (cglMellinPhase t N.value * cglLemma62SmoothedCharacterSum w N Q χ t) =
      ∫ u : ℝ, cglInitialLFunctionIntegrand w N Q χ t u := by
  rw [cglLemma62_smoothedCharacterSum_initialMellin]
  apply integral_congr_ae
  filter_upwards with u
  unfold cglInitialMellinIntegrand cglInitialLFunctionIntegrand
  congr 2
  rw [← DirichletCharacter.LFunction_eq_LSeries]
  simp [cglInitialMellinLinePoint]

end RHTower
