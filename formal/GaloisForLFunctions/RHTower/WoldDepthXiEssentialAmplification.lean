import GaloisForLFunctions.RHTower.CCMFirstClockWoldXiDepthCapacityNoGo
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Wold-depth--Xi essential amplification

The literal Wold maximum-shell mass and the literal completed-Xi depth successor determine an
exact minimal operator amplification.  Its exponent-normal logarithmic action is
`Real.log 2 / 2`.  Every continuous linear operator family realizing those source/reporter
pairs eventually dominates every smaller exponential rate.
-/

open Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

/-- Shell-coordinate Hilbert carrier for Wold maximum-depth increments. -/
abbrev WoldDepthShellHilbert := lp (fun _ : ℕ => ℂ) 2

/-- Canonical coordinate vector carrying the literal Wold shell mass at depth `M + 1`. -/
def woldDepthShellVector (M : ℕ) : WoldDepthShellHilbert :=
  (Real.sqrt (shellSourceMass (M + 1)) : ℂ) •
    (lp.single 2 M (1 : ℂ) : WoldDepthShellHilbert)

/-- Norm of the canonical Wold shell vector. -/
theorem norm_woldDepthShellVector (M : ℕ) :
    ‖woldDepthShellVector M‖ = Real.sqrt (shellSourceMass (M + 1)) := by
  rw [woldDepthShellVector, norm_smul,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Squared shell-vector norm is exactly the Wold maximum-shell probability. -/
theorem norm_sq_woldDepthShellVector {M : ℕ} (hM : 1 ≤ M) :
    ‖woldDepthShellVector M‖ ^ 2 = shellSourceMass (M + 1) := by
  rw [norm_woldDepthShellVector]
  exact Real.sq_sqrt (shellSourceMass_pos (by omega)).le

/-- Exact source-linked lower bound for an operator realizing the actual Xi depth successor. -/
theorem norm_ge_xiDepthSuccessorDefect_div_woldShell
    {u : ℂ} {M : ℕ} (hM : 1 ≤ M)
    (T : WoldDepthShellHilbert →L[ℂ] ℂ)
    (hT : T (woldDepthShellVector M) = xiDepthSuccessorDefect u M) :
    ‖xiDepthSuccessorDefect u M‖ /
        Real.sqrt (shellSourceMass (M + 1)) ≤ ‖T‖ := by
  have hmass : 0 < shellSourceMass (M + 1) :=
    shellSourceMass_pos (by omega)
  have hsqrt : 0 < Real.sqrt (shellSourceMass (M + 1)) :=
    Real.sqrt_pos.2 hmass
  apply (div_le_iff₀ hsqrt).2
  have hop := T.le_opNorm (woldDepthShellVector M)
  rw [hT, norm_woldDepthShellVector] at hop
  simpa [mul_comm] using hop

/-- Exact least norm forced by one actual Wold-shell/Xi-successor pair. -/
def woldXiDepthMinimalAmplification (u : ℂ) (M : ℕ) : ℝ :=
  ‖xiDepthSuccessorDefect u M‖ /
    Real.sqrt (shellSourceMass (M + 1))

/-- Prime-two rescaling of squared canonical shell norms converges to `1/2`. -/
theorem tendsto_two_pow_mul_norm_sq_woldDepthShellVector :
    Tendsto
      (fun M : ℕ =>
        (2 : ℝ) ^ (M + 1) * ‖woldDepthShellVector M‖ ^ 2)
      atTop (𝓝 (1 / 2)) := by
  refine (tendsto_scaledShellSourceMass.comp
    (tendsto_add_atTop_nat 1)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  simp only [Function.comp_apply]
  rw [norm_sq_woldDepthShellVector hM,
    ← scaledShellSourceMass_eq]

/-- Literal Wold shell mass has exponential logarithmic rate `-log 2`. -/
theorem tendsto_log_shellSourceMass_div_depth :
    Tendsto
      (fun M : ℕ =>
        Real.log (shellSourceMass (M + 1)) / ((M + 1 : ℕ) : ℝ))
      atTop (𝓝 (-Real.log 2)) := by
  have hscaled :
      Tendsto (fun M : ℕ => scaledShellSourceMass (M + 1))
        atTop (𝓝 (1 / 2)) :=
    tendsto_scaledShellSourceMass.comp (tendsto_add_atTop_nat 1)
  have hlogscaled :
      Tendsto (fun M : ℕ => Real.log (scaledShellSourceMass (M + 1)))
        atTop (𝓝 (Real.log (1 / 2))) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp hscaled
  have hdepth :
      Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinv :
      Tendsto (fun M : ℕ => (((M + 1 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hdepth
  have hzero :
      Tendsto
        (fun M : ℕ =>
          Real.log (scaledShellSourceMass (M + 1)) *
            (((M + 1 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 0) := by
    simpa using hlogscaled.mul hinv
  have hlimit := hzero.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log 2)
      atTop (𝓝 (Real.log 2)))
  have heq :
      (fun M : ℕ =>
        Real.log (scaledShellSourceMass (M + 1)) *
            (((M + 1 : ℕ) : ℝ))⁻¹ - Real.log 2) =ᶠ[atTop]
        (fun M : ℕ =>
          Real.log (shellSourceMass (M + 1)) /
            ((M + 1 : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hmass : shellSourceMass (M + 1) ≠ 0 :=
      ne_of_gt (shellSourceMass_pos (by omega))
    have hpow : (2 : ℝ) ^ (M + 1) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    rw [scaledShellSourceMass_eq,
      Real.log_mul hpow hmass, Real.log_pow]
    have hdepth_ne : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hdepth_ne]
    ring
  have hfinal :
      Tendsto
        (fun M : ℕ => Real.log (shellSourceMass (M + 1)) /
          ((M + 1 : ℕ) : ℝ))
        atTop (𝓝 (0 - Real.log 2)) :=
    hlimit.congr' heq
  simpa using hfinal

/-- Harmonic rescaling of the literal successor recovers its Xi moment reporter exactly. -/
theorem natCast_smul_xiDepthSuccessorDefect
    (u : ℂ) (M : ℕ) :
    ((M + 1 : ℕ) : ℝ) • xiDepthSuccessorDefect u M =
      xiDepthMomentReporter u M := by
  rw [xiDepthSuccessorDefect, xiHarmonicDepthWeight, smul_smul]
  have hne : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_inv_cancel₀ hne, one_smul]

/-- Exact minimal amplification in the card's source/reporter normalization. -/
theorem tendsto_woldXiDepthMinimalAmplification_rescaled
    {u : ℂ} (hu : xi u ≠ 0) :
    Tendsto
      (fun M : ℕ =>
        ((M + 1 : ℕ) : ℝ) *
          Real.sqrt (shellSourceMass (M + 1)) *
            woldXiDepthMinimalAmplification u M)
      atTop (𝓝 ‖-u * logDeriv xi u‖) := by
  have hreporter :
      Tendsto (fun M : ℕ => ‖xiDepthMomentReporter u M‖)
        atTop (𝓝 ‖-u * logDeriv xi u‖) :=
    continuous_norm.tendsto _ |>.comp (tendsto_xiDepthMomentReporter hu)
  refine hreporter.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hmass : 0 < shellSourceMass (M + 1) :=
    shellSourceMass_pos (by omega)
  have hsqrt : 0 < Real.sqrt (shellSourceMass (M + 1)) :=
    Real.sqrt_pos.2 hmass
  have hnorm := congrArg norm (natCast_smul_xiDepthSuccessorDefect u M)
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < ((M + 1 : ℕ) : ℝ))] at hnorm
  rw [woldXiDepthMinimalAmplification]
  field_simp [hsqrt.ne']
  simpa using hnorm.symm

/-- Exact level-one essential action forced by the literal Wold shell and Xi successor. -/
theorem tendsto_log_woldXiDepthMinimalAmplification_div_depth
    {u : ℂ} (hu : xi u ≠ 0)
    (hconnection : -u * logDeriv xi u ≠ 0) :
    Tendsto
      (fun M : ℕ =>
        Real.log (woldXiDepthMinimalAmplification u M) /
          ((M + 1 : ℕ) : ℝ))
      atTop (𝓝 (Real.log 2 / 2)) := by
  let B : ℕ → ℝ := fun M =>
    ((M + 1 : ℕ) : ℝ) *
      Real.sqrt (shellSourceMass (M + 1)) *
        woldXiDepthMinimalAmplification u M
  have hLpos : 0 < ‖-u * logDeriv xi u‖ := norm_pos_iff.mpr hconnection
  have hB : Tendsto B atTop (𝓝 ‖-u * logDeriv xi u‖) := by
    simpa only [B] using tendsto_woldXiDepthMinimalAmplification_rescaled hu
  have hlogB :
      Tendsto (fun M : ℕ => Real.log (B M)) atTop
        (𝓝 (Real.log ‖-u * logDeriv xi u‖)) :=
    (Real.continuousAt_log hLpos.ne').tendsto.comp hB
  have hdepth :
      Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinv :
      Tendsto (fun M : ℕ => (((M + 1 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hdepth
  have hlogBdiv :
      Tendsto
        (fun M : ℕ => Real.log (B M) / ((M + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hlogB.mul hinv
  have hlogdepth :
      Tendsto
        (fun M : ℕ => Real.log (((M + 1 : ℕ) : ℝ)) /
          ((M + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hdepth
  have hsource := tendsto_log_shellSourceMass_div_depth
  have hlimit := (hlogBdiv.sub hlogdepth).sub
    (hsource.const_mul (1 / 2 : ℝ))
  have hBne : ∀ᶠ M : ℕ in atTop, B M ≠ 0 :=
    hB.eventually_ne hLpos.ne'
  have heq :
      (fun M : ℕ =>
        Real.log (B M) / ((M + 1 : ℕ) : ℝ) -
            Real.log (((M + 1 : ℕ) : ℝ)) / ((M + 1 : ℕ) : ℝ) -
          (1 / 2 : ℝ) *
            (Real.log (shellSourceMass (M + 1)) /
              ((M + 1 : ℕ) : ℝ))) =ᶠ[atTop]
        (fun M : ℕ =>
          Real.log (woldXiDepthMinimalAmplification u M) /
            ((M + 1 : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1, hBne] with M hM hBM
    have hmass : 0 < shellSourceMass (M + 1) :=
      shellSourceMass_pos (by omega)
    have hsqrt : 0 < Real.sqrt (shellSourceMass (M + 1)) :=
      Real.sqrt_pos.2 hmass
    have hdepth_pos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    have hamp : woldXiDepthMinimalAmplification u M ≠ 0 := by
      intro hamp
      apply hBM
      simp [B, hamp]
    dsimp only [B]
    rw [Real.log_mul (mul_ne_zero hdepth_pos.ne' hsqrt.ne') hamp,
      Real.log_mul hdepth_pos.ne' hsqrt.ne', Real.log_sqrt hmass.le]
    field_simp [hdepth_pos.ne']
    ring
  have hfinal :
      Tendsto
        (fun M : ℕ =>
          Real.log (woldXiDepthMinimalAmplification u M) /
            ((M + 1 : ℕ) : ℝ))
        atTop
          (𝓝 (((0 : ℝ) - 0) - (1 / 2 : ℝ) * (-Real.log 2))) :=
    hlimit.congr' heq
  have hlimEq :
      ((0 : ℝ) - 0) - (1 / 2 : ℝ) * (-Real.log 2) =
        Real.log 2 / 2 := by
    ring
  rw [hlimEq] at hfinal
  exact hfinal

/-- Every realizing operator family eventually dominates every exponential below the forced
action `log 2 / 2`. -/
theorem eventually_exp_depth_le_norm_of_realizes_xiDepthSuccessor
    {u : ℂ} (hu : xi u ≠ 0)
    (hconnection : -u * logDeriv xi u ≠ 0)
    (T : ℕ → WoldDepthShellHilbert →L[ℂ] ℂ)
    (hT : ∀ M, T M (woldDepthShellVector M) = xiDepthSuccessorDefect u M)
    {c : ℝ} (hc : c < Real.log 2 / 2) :
    ∀ᶠ M : ℕ in atTop,
      Real.exp (c * ((M + 1 : ℕ) : ℝ)) ≤ ‖T M‖ := by
  have hrate :=
    tendsto_log_woldXiDepthMinimalAmplification_div_depth hu hconnection
  have hrateLower :
      ∀ᶠ M : ℕ in atTop,
        c < Real.log (woldXiDepthMinimalAmplification u M) /
          ((M + 1 : ℕ) : ℝ) :=
    (tendsto_order.1 hrate).1 c hc
  have hrescaled := tendsto_woldXiDepthMinimalAmplification_rescaled hu
  have hLpos : 0 < ‖-u * logDeriv xi u‖ := norm_pos_iff.mpr hconnection
  have hrescaledPos :
      ∀ᶠ M : ℕ in atTop,
        0 < ((M + 1 : ℕ) : ℝ) *
          Real.sqrt (shellSourceMass (M + 1)) *
            woldXiDepthMinimalAmplification u M :=
    (tendsto_order.1 hrescaled).1 0 hLpos
  filter_upwards [eventually_ge_atTop 1, hrateLower, hrescaledPos]
    with M hM hrateM hrescaledM
  have hmass : 0 < shellSourceMass (M + 1) :=
    shellSourceMass_pos (by omega)
  have hsqrt : 0 < Real.sqrt (shellSourceMass (M + 1)) :=
    Real.sqrt_pos.2 hmass
  have hdepth : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have hfactor :
      0 < ((M + 1 : ℕ) : ℝ) * Real.sqrt (shellSourceMass (M + 1)) :=
    mul_pos hdepth hsqrt
  have hamp : 0 < woldXiDepthMinimalAmplification u M := by
    rcases mul_pos_iff.mp hrescaledM with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hfactor.le hneg.1).elim
  have hlog :
      c * ((M + 1 : ℕ) : ℝ) <
        Real.log (woldXiDepthMinimalAmplification u M) :=
    (lt_div_iff₀ hdepth).mp hrateM
  have hexp :
      Real.exp (c * ((M + 1 : ℕ) : ℝ)) ≤
        woldXiDepthMinimalAmplification u M := by
    rw [← Real.exp_log hamp]
    exact Real.exp_le_exp.mpr hlog.le
  exact hexp.trans
    (norm_ge_xiDepthSuccessorDefect_div_woldShell hM (T M) (hT M))

end RHTower
