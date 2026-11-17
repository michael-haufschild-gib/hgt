import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateHasSquaredLogarithmicEnergyOnTheLinesOfItsDecay
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay
import GaloisForLFunctions.HTGeometry.HardyBoundary.NegativeHalfLineLaplaceHardy
import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCount
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.ZerosApproachLineAttainment

/-!
# The state decays exactly at the rate of the zeros

For the critical state `F` and `κ ≥ 0`:

  every centred zero has `Re z ≤ κ`  ⟺  `∫ F² e^{-bu} du < ∞` for every `b < 16 - 2κ`.

Equivalently the decay rate of the state is `sup {b : ∫ F² e^{-bu} < ∞} = 17 - 2Θ`, `Θ` the
supremum of the real parts of the zeros of `ζ`; unconditionally `∫ F² e^{-bu} < ∞` for
`b < 15 + 3001/12000`.

The direction `⟸` is the continuation of the transform: a zero right of the critical line is a
pole of the continuation and stops the decay. The direction `⟹` is a bootstrap in the abscissa
`σ` of decay, `P(σ)`: `∫ F² e^{-bu} < ∞` for all `b < 16 - 2σ`.

* Start: `P(1/4 + κ/2)`, where the mass of the wave `N(1/2 + p) L F(p)` on the line is paid by
  the single logarithm of the Gamma energy.
* Step: let `κ < s < σ < 1/2`. By `P(σ)` the state equation holds on a line `Re p = s₁` slightly
  right of `σ` and gives the transform two logarithms there. The Gamma energy gives one logarithm
  on `Re p = 0`. Interpolation gives `1 + s/s₁` logarithms on `Re p = s`, while `|N|²` costs
  `2θ` logarithms with `θ` close to `(1/2 - s)/(1/2 - κ)`. If
  `(1/2 + κ) σ < s (1/2 - κ + 2σ)` the mass of the wave on `Re p = s` is finite, and with the
  moment `16 - 4s < 16 - 2σ` the Agmon bound gives `∫ F² e^{-(16 - 2s)u} < ∞`, hence `P(s)`.
* The admissible `s` lie strictly below `σ` as long as `σ > κ`, so the infimum of the abscissae
  with `P(σ)` is `κ`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### One logarithm on the critical line, two on a line of decay -/

/-- The Gamma energy pays one logarithm on every line `Re p = σ ≥ 0`. -/
theorem integrable_log_mul_norm_sq_laplace_line {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {σ : ℝ} (hσ : 0 ≤ σ) :
    Integrable fun t : ℝ => Real.log (|t| + 4) *
      ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hH := criticalHalfLineEnergyDomain_exp_min_mul hF hσ
  have hP := integrable_norm_sq_paperFT_cx hH.integrable hH.sq
  have hL := integrable_log_mul_norm_sq_paperFT hH
  refine (hL.sub (hP.const_mul xiLineTwoLogDerivConstant)).congr
    (Eventually.of_forall fun t => ?_)
  show (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
      ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ)‖ ^ 2 -
    xiLineTwoLogDerivConstant *
      ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ)‖ ^ 2 =
    Real.log (|t| + 4) * ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
  rw [negativeHalfLineLaplace_add_mul_I_eq_paperFT hF.support σ t]
  ring

/-- The transform of a profile with `∫ F² e^{-bu} < ∞`, `b > 2`, moved one unit to the right is
a Hardy function of the right half-plane: it is the transform of `e^{-u} F`. -/
theorem exists_isHalfPlaneHardy_laplace_shift {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {b : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) (hb2 : 2 < b) :
    ∃ (G : ℂ → ℂ) (M : ℝ), IsHalfPlaneHardy G M ∧ ∀ x t : ℝ,
      G (((1 + x : ℝ) : ℂ) + (t : ℂ) * I) =
        negativeHalfLineLaplace (cx F) ((x : ℂ) + (t : ℂ) * I) := by
  obtain ⟨hi, h2⟩ := integrable_exp_min_mul_of_decay hFm hsupp hb (σ := -1) (by linarith)
  refine ⟨_, _, isHalfPlaneHardy_negativeHalfLineLaplace (memLp_cx_of_sq hi h2)
    (fun u hu => ?_), fun x t => ?_⟩
  · show ((Real.exp (-1 * min u 0) * F u : ℝ) : ℂ) = 0
    rw [hsupp u hu, mul_zero, Complex.ofReal_zero]
  · rw [laplace_exp_min_mul hsupp]
    congr 1
    push_cast
    ring

/-- **Interpolated energy.** If `∫ F² e^{-bu} < ∞` with `b > 16 - 2s₁` on a line
`κ < s₁ < 1/2`, then on every line `0 < s < s₁` the transform carries `1 + s/s₁` logarithms. -/
theorem integrable_log_rpow_mul_norm_sq_laplace_line_interp {κ s s₁ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hs0 : 0 < s) (hss : s < s₁)
    (hκs : κ < s₁) (hs₁ : s₁ < 1 / 2) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {b : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) (hbs : 16 - 2 * s₁ < b) :
    Integrable fun t : ℝ => Real.log (|t| + 4) ^ (1 + s / s₁) *
      ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hs₁0 : 0 < s₁ := hs0.trans hss
  obtain ⟨G, M, hG, hGeq⟩ :=
    exists_isHalfPlaneHardy_laplace_shift hd.meas hd.support hb (by linarith)
  have hE0 : Integrable fun t : ℝ => Real.log (|t| + 4) ^ (1 : ℝ) *
      ‖G (((1 + 0 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    (integrable_log_mul_norm_sq_laplace_line hd (σ := 0) le_rfl).congr
      (Eventually.of_forall fun t => by
        show Real.log (|t| + 4) *
            ‖negativeHalfLineLaplace (cx F) (((0 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 =
          Real.log (|t| + 4) ^ (1 : ℝ) * ‖G (((1 + 0 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
        rw [hGeq, Real.rpow_one])
  have hE1 : Integrable fun t : ℝ => Real.log (|t| + 4) ^ (2 : ℝ) *
      ‖G (((1 + s₁ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    (integrable_log_sq_mul_norm_sq_laplace_line hκ hzero hκs hs₁ hW hthreshold hF hb hbs).congr
      (Eventually.of_forall fun t => by
        show Real.log (|t| + 4) ^ 2 *
            ‖negativeHalfLineLaplace (cx F) ((s₁ : ℂ) + (t : ℂ) * I)‖ ^ 2 =
          Real.log (|t| + 4) ^ (2 : ℝ) * ‖G (((1 + s₁ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
        rw [hGeq, Real.rpow_two])
  have hcancel : s / s₁ * s₁ = s := by field_simp
  have h := integrable_log_rpow_mul_norm_sq_line_interp_aux hG (σ₀ := 1 + 0) (σ₁ := 1 + s₁)
    (k₀ := 1) (k₁ := 2) (τ := s / s₁) (σ := 1 + s) (k := 1 + s / s₁) (by norm_num)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) le_rfl (div_pos hs0 hs₁0)
    ((div_lt_one hs₁0).mpr hss) (by linear_combination (-1 : ℝ) * hcancel) (by ring) hE0 hE1
  refine h.congr (Eventually.of_forall fun t => ?_)
  show Real.log (|t| + 4) ^ (1 + s / s₁) * ‖G (((1 + s : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 =
    Real.log (|t| + 4) ^ (1 + s / s₁) *
      ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2
  rw [hGeq]

/-! ### The improvement step -/

theorem sq_rpow_eq_rpow_two_mul {x : ℝ} (hx : 0 ≤ x) (θ : ℝ) : (x ^ θ) ^ 2 = x ^ (2 * θ) := by
  rw [mul_comm, Real.rpow_mul hx, Real.rpow_two]

/-- The exponents of the step: with room `η`, twice the three-lines exponent of `N` between
`1/2 + κ + η` and `1 + η` is at most the interpolated number `1 + s/(σ + η)` of logarithms. -/
theorem two_mul_exponent_le {κ s σ η : ℝ} (hκ : 0 ≤ κ) (hκs : κ < s) (hsσ : s < σ)
    (hσ : σ < 1 / 2) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hη : 4 * η ≤ (1 / 2 - κ) * (σ + s) - 2 * (1 / 2 - s) * σ) :
    2 * ((1 + η - (1 / 2 + s)) / (1 + η - (1 / 2 + κ + η))) ≤ 1 + s / (σ + η) := by
  have hD : 0 < 1 + η - (1 / 2 + κ + η) := by linarith
  have hS : 0 < σ + η := by linarith
  have key : 2 * (1 + η - (1 / 2 + s)) * (σ + η) ≤
      (σ + η + s) * (1 + η - (1 / 2 + κ + η)) := by
    nlinarith [mul_nonneg hη0.le (show (0 : ℝ) ≤ 7 / 2 - κ + 2 * s - 2 * σ - 2 * η by linarith)]
  have e : 1 + s / (σ + η) = (σ + η + s) / (σ + η) := by rw [add_div, div_self hS.ne']
  rw [e, ← mul_div_assoc, div_le_div_iff₀ hD hS]
  exact key

/-- **The wave has finite mass on a line inside the region of decay.** Let `κ < s < σ < 1/2`
with `(1/2 + κ) σ < s (1/2 - κ + 2σ)`. If `∫ F² e^{-bu} < ∞` for every `b < 16 - 2σ`, then
`∫ |N(1/2 + s + it)|² |L F(s + it)|² dt < ∞`. -/
theorem integrable_norm_sq_zetaRegularLogDeriv_mul_laplace_of_decay {κ s σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκs : κ < s) (hsσ : s < σ)
    (hσ : σ < 1 / 2) (hstep : (1 / 2 + κ) * σ < s * (1 / 2 - κ + 2 * σ))
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hP : ∀ b < 16 - 2 * σ, Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) :
    Integrable fun t : ℝ => ‖zetaRegularLogDeriv (1 / 2 + ((s : ℂ) + (t : ℂ) * I))‖ ^ 2 *
      ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hs0 : 0 < s := lt_of_le_of_lt hκ hκs
  -- the room between the step condition and equality
  have hδ : 0 < (1 / 2 - κ) * (σ + s) - 2 * (1 / 2 - s) * σ := by nlinarith [hstep]
  obtain ⟨η, hη0, hη1, hηs, hησ, hηδ⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η < s - κ ∧ η < 1 / 2 - σ ∧
      4 * η ≤ (1 / 2 - κ) * (σ + s) - 2 * (1 / 2 - s) * σ := by
    refine ⟨min (min 1 ((s - κ) / 2)) (min ((1 / 2 - σ) / 2)
      (((1 / 2 - κ) * (σ + s) - 2 * (1 / 2 - s) * σ) / 4)), ?_, ?_, ?_, ?_, ?_⟩
    · exact lt_min (lt_min one_pos (by linarith)) (lt_min (by linarith) (by linarith))
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
    · exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    · have h := (min_le_right (min 1 ((s - κ) / 2)) (min ((1 / 2 - σ) / 2)
        (((1 / 2 - κ) * (σ + s) - 2 * (1 / 2 - s) * σ) / 4))).trans (min_le_right _ _)
      linarith
  -- the decay available on the line σ + η
  have hb := hP (16 - 2 * σ - η) (by linarith)
  have hE := integrable_log_rpow_mul_norm_sq_laplace_line_interp hκ hzero hs0
    (show s < σ + η by linarith) (by linarith) (by linarith) hW hthreshold hF hb (by linarith)
  obtain ⟨C, hC, hN⟩ := exists_norm_zetaRegularLogDeriv_le_rpow hκ hzero
    (a := 1 / 2 + κ + η) (b := 1 + η) (s₀ := 1 / 2 + s) (by linarith) (by linarith)
    (by linarith) (by linarith)
  have hθ := two_mul_exponent_le hκ hκs hsσ hσ hη0 hη1 hηδ
  have hI0 := integrable_norm_sq_laplace_line_of_decay hd.meas hd.support hb (σ := s)
    (by linarith)
  have hcont : Continuous fun t : ℝ =>
      ‖zetaRegularLogDeriv (1 / 2 + ((s : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
    refine (continuous_iff_continuousAt.mpr fun t => ?_).norm.pow 2
    have h1 := differentiableAt_zetaRegularLogDeriv_half_add hκ hzero
      (p := (s : ℂ) + (t : ℂ) * I) (by simpa using hκs)
    have h2 : ContinuousAt (fun t : ℝ => (s : ℂ) + (t : ℂ) * I) t := by fun_prop
    exact ContinuousAt.comp (g := fun p : ℂ => zetaRegularLogDeriv (1 / 2 + p)) h1.continuousAt h2
  refine (hE.const_mul (C ^ 2)).mono' (hcont.aestronglyMeasurable.mul hI0.aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hL := one_le_log_abs_add_four t
  have hL0 : 0 ≤ Real.log (|t| + 4) := by linarith
  have h1 : ‖zetaRegularLogDeriv (1 / 2 + ((s : ℂ) + (t : ℂ) * I))‖ ≤
      C * Real.log (|t| + 4) ^ ((1 + η - (1 / 2 + s)) / (1 + η - (1 / 2 + κ + η))) := by
    have h := hN t
    rwa [show ((1 / 2 + s : ℝ) : ℂ) + (t : ℂ) * I = 1 / 2 + ((s : ℂ) + (t : ℂ) * I) by
      push_cast
      ring] at h
  have h2 : ‖zetaRegularLogDeriv (1 / 2 + ((s : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
      C ^ 2 * Real.log (|t| + 4) ^ (1 + s / (σ + η)) := by
    calc ‖zetaRegularLogDeriv (1 / 2 + ((s : ℂ) + (t : ℂ) * I))‖ ^ 2
        ≤ (C * Real.log (|t| + 4) ^
            ((1 + η - (1 / 2 + s)) / (1 + η - (1 / 2 + κ + η)))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = C ^ 2 * Real.log (|t| + 4) ^
            (2 * ((1 + η - (1 / 2 + s)) / (1 + η - (1 / 2 + κ + η)))) := by
          rw [mul_pow, sq_rpow_eq_rpow_two_mul hL0]
      _ ≤ C ^ 2 * Real.log (|t| + 4) ^ (1 + s / (σ + η)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hθ) (sq_nonneg C)
  calc ‖zetaRegularLogDeriv (1 / 2 + ((s : ℂ) + (t : ℂ) * I))‖ ^ 2 *
        ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ C ^ 2 * Real.log (|t| + 4) ^ (1 + s / (σ + η)) *
          ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = C ^ 2 * (Real.log (|t| + 4) ^ (1 + s / (σ + η)) *
          ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2) := by ring

/-- **The improvement step.** Let `κ < s < σ < 1/2` with `σ < 2s` and
`(1/2 + κ) σ < s (1/2 - κ + 2σ)`. Decay at every rate below `16 - 2σ` improves to decay at the
rate `16 - 2s`. -/
theorem integrable_sq_mul_exp_of_decay_step {κ s σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκs : κ < s) (hsσ : s < σ)
    (hσ : σ < 1 / 2) (hstep : (1 / 2 + κ) * σ < s * (1 / 2 - κ + 2 * σ)) (hhalf : σ < 2 * s)
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hP : ∀ b < 16 - 2 * σ, Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) :
    Integrable fun u => F u ^ 2 * Real.exp (-((16 - 2 * s) * u)) :=
  integrable_sq_mul_exp_of_line_mass hκ hzero hκs (by linarith) hW hthreshold hF
    (integrable_norm_sq_zetaRegularLogDeriv_mul_laplace_of_decay hκ hzero hκs hsσ hσ hstep hW
      hthreshold hF hP)
    (hP (4 * (4 - s)) (by linarith))

/-- Below every abscissa `σ > κ` there is a line admissible for the improvement step. -/
theorem exists_improvement_line {κ σ : ℝ} (hκ : 0 ≤ κ) (hκσ : κ < σ) :
    ∃ s : ℝ, κ < s ∧ s < σ ∧ σ < 2 * s ∧ (1 / 2 + κ) * σ < s * (1 / 2 - κ + 2 * σ) := by
  have hσ0 : 0 < σ := lt_of_le_of_lt hκ hκσ
  have hden : 0 < 1 / 2 - κ + 2 * σ := by linarith
  have hden' : 1 / 2 - κ + 2 * σ ≠ 0 := hden.ne'
  have h1 : (1 / 2 + κ) * σ / (1 / 2 - κ + 2 * σ) < σ := by
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos hσ0 (sub_pos.mpr hκσ)]
  obtain ⟨m, hm⟩ : ∃ m : ℝ,
      m = max κ (max (σ / 2) ((1 / 2 + κ) * σ / (1 / 2 - κ + 2 * σ))) := ⟨_, rfl⟩
  have hmσ : m < σ := by
    rw [hm]
    exact max_lt hκσ (max_lt (by linarith) h1)
  have hκm : κ ≤ m := by
    rw [hm]
    exact le_max_left _ _
  have hσm : σ / 2 ≤ m := by
    rw [hm]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have h1m : (1 / 2 + κ) * σ / (1 / 2 - κ + 2 * σ) ≤ m := by
    rw [hm]
    exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨(σ + m) / 2, by linarith, by linarith, by linarith, ?_⟩
  calc (1 / 2 + κ) * σ
      = (1 / 2 + κ) * σ / (1 / 2 - κ + 2 * σ) * (1 / 2 - κ + 2 * σ) :=
        (div_eq_iff hden').mp rfl
    _ < (σ + m) / 2 * (1 / 2 - κ + 2 * σ) := mul_lt_mul_of_pos_right (by linarith) hden

/-! ### The decay law -/

/-- **The state decays at the rate of the zeros.** If every centred zero has `Re z ≤ κ`, the
critical state has the square moments `∫ F² e^{-bu} du < ∞` for every `b < 16 - 2κ`. -/
theorem integrable_sq_mul_exp_of_zero_abscissa_sharp {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {b : ℝ} (hb : b < 16 - 2 * κ) :
    Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  rcases le_or_gt (1 / 2) κ with hκ2 | hκ2
  · exact (criticalHalfLineGroundState_exponential_bounds hW hthreshold hF).2 b (by linarith)
  -- the abscissae of decay
  obtain ⟨S, hS⟩ : ∃ S : Set ℝ, S = {σ : ℝ | κ ≤ σ ∧ σ ≤ 1 / 4 + κ / 2 ∧
      ∀ b < 16 - 2 * σ, Integrable fun u => F u ^ 2 * Real.exp (-(b * u))} := ⟨_, rfl⟩
  have hmem : ∀ σ : ℝ, σ ∈ S ↔ (κ ≤ σ ∧ σ ≤ 1 / 4 + κ / 2 ∧
      ∀ b < 16 - 2 * σ, Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) := fun σ => by
    rw [hS, Set.mem_setOf_eq]
  have h0 : (1 / 4 + κ / 2) ∈ S := (hmem _).mpr ⟨by linarith, le_rfl, fun b hb =>
    integrable_sq_mul_exp_of_zero_abscissa hκ hzero hW hthreshold hF (by linarith)⟩
  have hbdd : BddBelow S := ⟨κ, fun σ hσ => ((hmem σ).mp hσ).1⟩
  have hne : S.Nonempty := ⟨_, h0⟩
  have hinf_ge : κ ≤ sInf S := le_csInf hne fun σ hσ => ((hmem σ).mp hσ).1
  have hinf_le : sInf S ≤ 1 / 4 + κ / 2 := csInf_le hbdd h0
  -- decay at the infimum
  have hPinf : ∀ b < 16 - 2 * sInf S, Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) := by
    intro b hb
    obtain ⟨σ, hσS, hσ⟩ := exists_lt_of_csInf_lt hne (show sInf S < (16 - b) / 2 by linarith)
    exact ((hmem σ).mp hσS).2.2 b (by linarith)
  -- the infimum is κ: otherwise the improvement step produces a smaller abscissa
  have hinf : sInf S = κ := by
    by_contra hne'
    have hlt : κ < sInf S := lt_of_le_of_ne hinf_ge (Ne.symm hne')
    obtain ⟨s, hκs, hsσ, hhalf, hstep⟩ := exists_improvement_line hκ hlt
    have hstepI := integrable_sq_mul_exp_of_decay_step hκ hzero hκs hsσ (by linarith) hstep
      hhalf hW hthreshold hF hPinf
    have hsS : s ∈ S := (hmem s).mpr ⟨hκs.le, by linarith, fun b hb =>
      integrable_sq_mul_exp_of_le hd.meas hd.support hstepI hb.le⟩
    linarith [csInf_le hbdd hsS]
  rw [hinf] at hPinf
  exact hPinf b hb

/-- **Unconditional decay**: `∫ F² e^{-bu} du < ∞` for every `b < 15 + 3001/12000`. -/
theorem integrable_sq_mul_exp_seed {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {b : ℝ}
    (hb : b < 15 + 3001 / 12000) : Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) :=
  integrable_sq_mul_exp_of_zero_abscissa_sharp (κ := 8999 / 24000) (by norm_num)
    re_centredZero_le_seed hW hthreshold hF (by linarith)

/-- **The decay law.** For `κ ≥ 0`, every centred zero has `Re z ≤ κ` if and only if the
critical state has the square moments `∫ F² e^{-bu} du < ∞` for every `b < 16 - 2κ`: the decay
rate of the state is `16 - 2κ*`, `κ*` the supremum of the real parts of the centred zeros. -/
theorem forall_re_centredZero_le_iff_integrable_sq_mul_exp {κ : ℝ} (hκ : 0 ≤ κ) {W₀ : ℝ}
    (hW : 0 < W₀) (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    (∀ q : XiZeroCopy, (centredZero q).re ≤ κ) ↔
      ∀ b < 16 - 2 * κ, Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) := by
  refine ⟨fun hzero b hb =>
    integrable_sq_mul_exp_of_zero_abscissa_sharp hκ hzero hW hthreshold hF hb, fun hdec q => ?_⟩
  by_contra hq
  have hlt : κ < (centredZero q).re := not_le.mp hq
  have h3 : (centredZero q).re = ((q.1 : ℂ)).re - 1 / 2 := by simp [centredZero]
  exact criticalState_not_integrable_of_zero hW hthreshold hF (riemannZeta_xiZeroCopy_eq_zero q)
    (by linarith) (b := 16 - (centredZero q).re - κ) (by linarith) (hdec _ (by linarith))

/-- A finite window threshold puts a zero of `ζ` right of the critical line. -/
theorem exists_riemannZeta_zero_right_of_threshold {W₀ : ℝ}
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re := by
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis
    (not_riemannHypothesis_of_threshold hthreshold)
  exact ⟨(q.1 : ℂ), riemannZeta_xiZeroCopy_eq_zero q, hq⟩

/-- Below the rate `17 - 2Θ` the square moments of the critical state are finite. -/
theorem integrable_sq_mul_exp_of_lt_decayRate {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {b : ℝ}
    (hb : b < 17 - 2 * zetaZeroAbscissa) :
    Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) := by
  refine integrable_sq_mul_exp_of_zero_abscissa_sharp (κ := zetaZeroAbscissa - 1 / 2)
    (by linarith [half_le_zetaZeroAbscissa]) (fun q => ?_) hW hthreshold hF (by linarith)
  have h3 : (centredZero q).re = ((q.1 : ℂ)).re - 1 / 2 := by simp [centredZero]
  have h := re_le_zetaZeroAbscissa (riemannZeta_xiZeroCopy_eq_zero q)
  rw [h3]
  linarith

/-- Above the rate `17 - 2Θ` the square moments of the critical state are infinite. -/
theorem not_integrable_sq_mul_exp_of_decayRate_lt {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {b : ℝ}
    (hb : 17 - 2 * zetaZeroAbscissa < b) :
    ¬ Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) := by
  obtain ⟨ρ₀, hζ₀, hρ₀⟩ := exists_riemannZeta_zero_right_of_threshold hthreshold
  rcases lt_or_ge (17 - 2 * ρ₀.re) b with h | h
  · exact criticalState_not_integrable_of_zero hW hthreshold hF hζ₀ hρ₀ h
  · obtain ⟨ρ, hζ, hρ⟩ :=
      exists_zetaZero_lt_re (show (17 - b) / 2 < zetaZeroAbscissa by linarith)
    exact criticalState_not_integrable_of_zero hW hthreshold hF hζ (by linarith) (by linarith)

/-- **The decay rate of the critical state is `17 - 2Θ`**, `Θ` the supremum of the real parts
of the zeros of `ζ`: the exponents `b` with `∫ F² e^{-bu} du < ∞` have supremum `17 - 2Θ`. -/
theorem isLUB_integrable_sq_mul_exp {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    IsLUB {b : ℝ | Integrable fun u => F u ^ 2 * Real.exp (-(b * u))}
      (17 - 2 * zetaZeroAbscissa) := by
  constructor
  · intro b hb
    by_contra hlt
    exact not_integrable_sq_mul_exp_of_decayRate_lt hW hthreshold hF (not_le.mp hlt) hb
  · intro c hc
    by_contra hlt
    have hlt' : c < 17 - 2 * zetaZeroAbscissa := not_le.mp hlt
    have hmem : (c + (17 - 2 * zetaZeroAbscissa)) / 2 ∈
        {b : ℝ | Integrable fun u => F u ^ 2 * Real.exp (-(b * u))} :=
      integrable_sq_mul_exp_of_lt_decayRate hW hthreshold hF (by linarith)
    have hle := hc hmem
    linarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
