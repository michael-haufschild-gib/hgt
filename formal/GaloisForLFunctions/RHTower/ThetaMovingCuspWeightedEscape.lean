import GaloisForLFunctions.RHTower.ThetaMovingCuspSpectralShear
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionWeightedAdmission
import GaloisForLFunctions.RHTower.ThetaArithmeticTerminalCusp

/-!
# Moving-cusp reflection: the terminal Hilbert scale is the moving scale

At the sharp admissible grade `q_P = c/P²` the theta weight seen from the moving cusp converges:
`k(−log P − u)^{−c/P²} → exp(cπ e^{2u})` (6).  The limiting density `|R_∞|² exp(cπe^{2u})` has an
integrable positive tail exactly when `c < 2`.  On the negative tail `R_∞ ∉ L²`: otherwise its
Mellin transform would be holomorphic on `Re w > 0`, and `ζ(w − 1/2) ℒR_∞(w) = F(w)` would fail at
`w = ρ + 1/2` for a nontrivial zeta zero `ρ`.  By Fatou's lemma the normalized finite energies
`P ‖k_S‖²_{H_{c/P²}}`, each finite, diverge along every prime exhaustion (7).
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## (6) The moving weight -/

theorem tendsto_log_thetaCuspFullSource_sub_envelope :
    Tendsto (fun x => Real.log (thetaCuspFullSource x) -
      (9 * x / 2 - Real.pi * Real.exp (2 * x))) atTop (𝓝 (Real.log (4 * Real.pi ^ 2))) := by
  have h := (Real.continuousAt_log (by positivity : (4 * Real.pi ^ 2 : ℝ) ≠ 0)).tendsto.comp
    thetaCuspFullSource_div_envelope_tendsto
  refine h.congr' ?_
  filter_upwards with x
  simp only [Function.comp]
  rw [Real.log_div (thetaCuspFullSource_pos x).ne' (HedenmalmThetaSource.thetaEnvelope_pos x).ne',
    HedenmalmThetaSource.thetaEnvelope, Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp]
  ring

/-- **(6)** `k(−log P − u)^{−c/P²} → exp(cπ e^{2u})` as `P → ∞`. -/
theorem tendsto_thetaCuspFullSource_moving_rpow (c u : ℝ) :
    Tendsto (fun P : ℝ => thetaCuspFullSource (-Real.log P - u) ^ (-(c / P ^ 2))) atTop
      (𝓝 (Real.exp (c * Real.pi * Real.exp (2 * u)))) := by
  have hx : Tendsto (fun P : ℝ => Real.log P + u) atTop atTop :=
    tendsto_atTop_add_const_right _ u Real.tendsto_log_atTop
  have hL := tendsto_log_thetaCuspFullSource_sub_envelope.comp hx
  have hP2 : Tendsto (fun P : ℝ => c / P ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop (tendsto_pow_atTop (n := 2) two_ne_zero)
  have hlogP : Tendsto (fun P : ℝ => (Real.log P + u) / P ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun P : ℝ => Real.log P / P ^ 2) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).tendsto_div_nhds_zero
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with P hP
      rw [Real.rpow_two]
    have h2 : Tendsto (fun P : ℝ => u / P ^ 2) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_pow_atTop (n := 2) two_ne_zero)
    simpa [add_div] using h1.add h2
  have hexp : Tendsto (fun P : ℝ => -(c / P ^ 2) * (Real.log (thetaCuspFullSource (Real.log P + u)) -
      (9 * (Real.log P + u) / 2 - Real.pi * Real.exp (2 * (Real.log P + u)))) -
        c * (9 / 2) * ((Real.log P + u) / P ^ 2)) atTop (𝓝 (-(0 : ℝ) * Real.log (4 * Real.pi ^ 2) -
          c * (9 / 2) * 0)) := ((hP2.neg.mul hL).sub (hlogP.const_mul _))
  rw [neg_zero, zero_mul, mul_zero, sub_zero] at hexp
  have hfin := (Real.continuous_exp.tendsto _).comp (hexp.const_add (c * Real.pi * Real.exp (2 * u)))
  rw [add_zero] at hfin
  refine hfin.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with P hP
  simp only [Function.comp]
  have hk := thetaCuspFullSource_pos (Real.log P + u)
  rw [show -Real.log P - u = -(Real.log P + u) by ring, thetaCuspFullSource_neg,
    Real.rpow_def_of_pos hk]
  congr 1
  have he : Real.exp (2 * (Real.log P + u)) = P ^ 2 * Real.exp (2 * u) := by
    rw [mul_add, Real.exp_add, show 2 * Real.log P = Real.log P * 2 by ring, Real.exp_mul,
      Real.exp_log hP]
    norm_num
  rw [he]
  field_simp
  ring

/-! ## The limiting density -/

/-- **(6), positive tail.**  `|R_∞(u)|² exp(cπ e^{2u})` is integrable on `(0, ∞)` iff `c < 2`. -/
theorem integrableOn_movingCuspDualLimit_sq_mul_exp_iff (c : ℝ) :
    IntegrableOn (fun u => movingCuspDualLimit u ^ 2 * Real.exp (c * Real.pi * Real.exp (2 * u)))
      (Ioi 0) ↔ c < 2 := by
  constructor
  · intro hint
    by_contra hc
    push Not at hc
    obtain ⟨U, hU⟩ := eventually_atTop.1 ((tendsto_movingCuspDualLimit_div_thetaCuspFullSource.eventually
      (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))))
    set U₀ : ℝ := max U 1
    have hL := HedenmalmThetaSource.thetaEnvelopeLower_pos
    set m : ℝ := (HedenmalmThetaSource.thetaEnvelopeLower / 2) ^ 2
    have hm : 0 < m := by positivity
    have hlow : ∀ u ∈ Ioi U₀, m ≤ movingCuspDualLimit u ^ 2 * Real.exp (c * Real.pi * Real.exp (2 * u)) := by
      intro u hu
      have hu1 : 1 < u := lt_of_le_of_lt (le_max_right _ _) hu
      have hk := thetaCuspFullSource_pos u
      have hr := hU u (le_trans (le_max_left _ _) hu.le)
      have hR : thetaCuspFullSource u / 2 ≤ movingCuspDualLimit u := by
        rw [lt_div_iff₀ hk] at hr; linarith
      have hge := HedenmalmThetaSource.thetaCuspFullSource_ge_envelope (show 0 < u by linarith)
      have hRpos : HedenmalmThetaSource.thetaEnvelopeLower / 2 * HedenmalmThetaSource.thetaEnvelope u ≤
          movingCuspDualLimit u := by linarith
      have hE := HedenmalmThetaSource.thetaEnvelope_pos u
      have hsq : (HedenmalmThetaSource.thetaEnvelopeLower / 2 * HedenmalmThetaSource.thetaEnvelope u) ^ 2 ≤
          movingCuspDualLimit u ^ 2 := pow_le_pow_left₀ (by positivity) hRpos 2
      have henv : HedenmalmThetaSource.thetaEnvelope u ^ 2 * Real.exp (c * Real.pi * Real.exp (2 * u)) ≥ 1 := by
        rw [HedenmalmThetaSource.thetaEnvelope, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
          mul_assoc, ← Real.exp_add, ← Real.exp_add]
        refine Real.one_le_exp ?_
        have he := Real.exp_pos (2 * u)
        push_cast
        nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right (sub_nonneg.2 hc) (mul_pos Real.pi_pos he).le]
      calc m = (HedenmalmThetaSource.thetaEnvelopeLower / 2) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (HedenmalmThetaSource.thetaEnvelopeLower / 2) ^ 2 *
            (HedenmalmThetaSource.thetaEnvelope u ^ 2 * Real.exp (c * Real.pi * Real.exp (2 * u))) :=
            mul_le_mul_of_nonneg_left henv (by positivity)
        _ = (HedenmalmThetaSource.thetaEnvelopeLower / 2 * HedenmalmThetaSource.thetaEnvelope u) ^ 2 *
            Real.exp (c * Real.pi * Real.exp (2 * u)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    have hsub : IntegrableOn (fun u => movingCuspDualLimit u ^ 2 * Real.exp (c * Real.pi * Real.exp (2 * u)))
        (Ioi U₀) := hint.mono_set (Ioi_subset_Ioi (le_trans zero_le_one (le_max_right _ _)))
    have hconst : IntegrableOn (fun _ : ℝ => m) (Ioi U₀) :=
      hsub.mono' aestronglyMeasurable_const ((ae_restrict_iff' measurableSet_Ioi).2
        (ae_of_all _ fun u hu => by rw [Real.norm_eq_abs, abs_of_pos hm]; exact hlow u hu))
    rw [integrableOn_const_iff] at hconst
    rcases hconst with h | h
    · exact hm.ne' (by simpa using h)
    · simp at h
  · intro hc
    obtain ⟨B, D, hB, hR⟩ := exists_abs_movingCuspDualLimit_le_gaussian
    have hmaj : Integrable fun u : ℝ => B ^ 2 * (Real.exp ((2 * D + 1) * u) *
        Real.exp (-((2 - c) * Real.pi * Real.exp (2 * u)))) :=
      (integrable_exp_mul_exp_neg_mul_exp_two_mul (by positivity)
        (by nlinarith [Real.pi_pos])).const_mul _
    refine hmaj.integrableOn.mono' (((continuous_movingCuspDualLimit.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))))).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_))
    have hu : (0 : ℝ) < u := hu
    have h1 := hR u hu.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    have hsq : |movingCuspDualLimit u| ^ 2 ≤ (B * Real.exp (D * u) * Real.exp (-Real.pi * Real.exp (2 * u))) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc |movingCuspDualLimit u| ^ 2 * Real.exp (c * Real.pi * Real.exp (2 * u))
        ≤ (B * Real.exp (D * u) * Real.exp (-Real.pi * Real.exp (2 * u))) ^ 2 *
            Real.exp (c * Real.pi * Real.exp (2 * u)) := mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
      _ = B ^ 2 * (Real.exp (2 * D * u) * Real.exp (-((2 - c) * Real.pi * Real.exp (2 * u)))) := by
          rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_assoc (B ^ 2),
            mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 2; push_cast; ring
      _ ≤ _ := by
          gcongr
          nlinarith

/-! ## (7) The negative tail is not square integrable -/

theorem abs_mul_le_half_sq_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- Under an `L²` hypothesis on the negative ray, the negative-ray Mellin integrand is integrable
for every `Re w > 0`. -/
theorem integrableOn_cexp_mul_movingCuspDualLimit_Iic
    (hL2 : IntegrableOn (fun u => movingCuspDualLimit u ^ 2) (Iic 0)) {σ : ℝ} (hσ : 0 < σ)
    {w : ℂ} (hw : σ ≤ w.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (w * u) * (movingCuspDualLimit u : ℂ)) (Iic 0) := by
  have hexp : IntegrableOn (fun u : ℝ => Real.exp (2 * σ * u)) (Iic 0) :=
    integrableOn_exp_mul_Iic (by linarith) 0
  refine ((hexp.add hL2).div_const 2).mono'
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (Complex.continuous_ofReal.comp continuous_movingCuspDualLimit)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Iic).2 (ae_of_all _ fun u hu => ?_))
  have hu : u ≤ 0 := hu
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h1 : Real.exp (w.re * u) ≤ Real.exp (σ * u) := Real.exp_le_exp.2 (by nlinarith)
  have h2 := abs_mul_le_half_sq_add_sq (Real.exp (σ * u)) (movingCuspDualLimit u)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h2
  have h3 : Real.exp (σ * u) ^ 2 = Real.exp (2 * σ * u) := by
    rw [← Real.exp_nat_mul]; ring_nf
  calc Real.exp (w.re * u) * |movingCuspDualLimit u|
      ≤ Real.exp (σ * u) * |movingCuspDualLimit u| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ _ := by rw [h3] at h2; simpa [Pi.add_apply] using h2

/-- **(7)** `R_∞ ∉ L²((−∞, 0))`. -/
theorem not_integrableOn_movingCuspDualLimit_sq_Iio :
    ¬ IntegrableOn (fun u => movingCuspDualLimit u ^ 2) (Iio 0) := by
  intro hL2'
  have hL2 : IntegrableOn (fun u => movingCuspDualLimit u ^ 2) (Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio).2 hL2'
  set N : ℂ → ℂ := fun w => ∫ u in Iic (0 : ℝ), Complex.exp (w * u) * (movingCuspDualLimit u : ℂ)
  -- holomorphy of the negative-ray transform on `Re w > 0`
  have hNd : ∀ w₀ : ℂ, 0 < w₀.re → DifferentiableAt ℂ N w₀ := by
    intro w₀ hw₀
    set σ₁ : ℝ := w₀.re / 2
    have hσ₁ : 0 < σ₁ := by simp only [σ₁]; linarith
    have hball : ∀ w ∈ Metric.ball w₀ σ₁, σ₁ ≤ w.re := fun w hw => by
      have := (Complex.abs_re_le_norm (w - w₀)).trans (le_of_lt (by rwa [← dist_eq_norm]))
      rw [Complex.sub_re] at this
      have := neg_abs_le (w.re - w₀.re)
      simp only [σ₁] at *; linarith
    have hcont : ∀ w : ℂ, Continuous fun u : ℝ => Complex.exp (w * u) * (movingCuspDualLimit u : ℂ) :=
      fun w => (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
        (Complex.continuous_ofReal.comp continuous_movingCuspDualLimit)
    have hmaj : IntegrableOn (fun u : ℝ => 2 / σ₁ * ((Real.exp (2 * (σ₁ / 2) * u) +
        movingCuspDualLimit u ^ 2) / 2)) (Iic 0) :=
      (((integrableOn_exp_mul_Iic (by positivity) 0).add hL2).div_const 2).const_mul _
    have hderiv_bound : ∀ u : ℝ, u ≤ 0 → ∀ w : ℂ, σ₁ ≤ w.re →
        ‖(u : ℂ) * (Complex.exp (w * u) * (movingCuspDualLimit u : ℂ))‖ ≤
          2 / σ₁ * ((Real.exp (2 * (σ₁ / 2) * u) + movingCuspDualLimit u ^ 2) / 2) := by
      intro u hu w hw
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      have h1 : Real.exp (w.re * u) ≤ Real.exp (σ₁ * u) := Real.exp_le_exp.2 (by nlinarith)
      have hlin : |u| * Real.exp (σ₁ * u) ≤ 2 / σ₁ * Real.exp (σ₁ / 2 * u) := by
        have hexp := Real.add_one_le_exp (-(σ₁ / 2) * u)
        have hpos := Real.exp_pos (σ₁ / 2 * u)
        have e1 : Real.exp (σ₁ * u) = Real.exp (σ₁ / 2 * u) * Real.exp (σ₁ / 2 * u) := by
          rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp (-(σ₁ / 2) * u) * Real.exp (σ₁ / 2 * u) = 1 := by
          rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
        have key : -u * Real.exp (σ₁ / 2 * u) ≤ 2 / σ₁ := by
          rw [le_div_iff₀ hσ₁]
          have := mul_le_mul_of_nonneg_right hexp hpos.le
          rw [e2] at this
          nlinarith
        rw [abs_of_nonpos hu, e1, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right key hpos.le
      have h2 := abs_mul_le_half_sq_add_sq (Real.exp (σ₁ / 2 * u)) (movingCuspDualLimit u)
      rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h2
      have h3 : Real.exp (σ₁ / 2 * u) ^ 2 = Real.exp (2 * (σ₁ / 2) * u) := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [h3] at h2
      calc |u| * (Real.exp (w.re * u) * |movingCuspDualLimit u|)
          ≤ |u| * Real.exp (σ₁ * u) * |movingCuspDualLimit u| := by
            rw [← mul_assoc]; gcongr
        _ ≤ 2 / σ₁ * Real.exp (σ₁ / 2 * u) * |movingCuspDualLimit u| := by gcongr
        _ = 2 / σ₁ * (Real.exp (σ₁ / 2 * u) * |movingCuspDualLimit u|) := by ring
        _ ≤ _ := by gcongr
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Iic (0 : ℝ)))
      (F := fun w u => Complex.exp (w * u) * (movingCuspDualLimit u : ℂ))
      (F' := fun w u => (u : ℂ) * (Complex.exp (w * u) * (movingCuspDualLimit u : ℂ)))
      (bound := fun u => 2 / σ₁ * ((Real.exp (2 * (σ₁ / 2) * u) + movingCuspDualLimit u ^ 2) / 2))
      (Metric.ball_mem_nhds w₀ hσ₁) (Eventually.of_forall fun w => (hcont w).aestronglyMeasurable)
      (integrableOn_cexp_mul_movingCuspDualLimit_Iic hL2 hσ₁ (by simp only [σ₁]; linarith))
      ((Complex.continuous_ofReal.mul (hcont w₀)).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Iic).2 (ae_of_all _ fun u hu w hw =>
        hderiv_bound u hu w (hball w hw)))
      hmaj (ae_of_all _ fun u w _ => by
        have := ((hasDerivAt_id w).mul_const (u : ℂ)).cexp.mul_const (movingCuspDualLimit u : ℂ)
        refine this.congr_deriv ?_
        simp only [id, one_mul]
        ring)
    exact h.2.differentiableAt
  -- the positive-ray piece and the full transform
  obtain ⟨B, D, hB, hR⟩ := exists_abs_movingCuspDualLimit_le_gaussian
  have hpos : ∀ w : ℂ, 0 < w.re →
      IntegrableOn (fun u : ℝ => Complex.exp (w * u) * (movingCuspDualLimit u : ℂ)) (Ioi 0) := by
    intro w hw
    have hmaj : Integrable fun u : ℝ => B * (Real.exp ((w.re + D) * u) *
        Real.exp (-(Real.pi * Real.exp (2 * u)))) :=
      (integrable_exp_mul_exp_neg_mul_exp_two_mul (by positivity) Real.pi_pos).const_mul B
    refine hmaj.integrableOn.mono'
      ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
        (Complex.continuous_ofReal.comp continuous_movingCuspDualLimit)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_))
    have hu : (0 : ℝ) < u := hu
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc Real.exp (w.re * u) * |movingCuspDualLimit u|
        ≤ Real.exp (w.re * u) * (B * Real.exp (D * u) * Real.exp (-Real.pi * Real.exp (2 * u))) :=
          mul_le_mul_of_nonneg_left (hR u hu.le) (Real.exp_pos _).le
      _ = B * (Real.exp ((w.re + D) * u) * Real.exp (-(Real.pi * Real.exp (2 * u)))) := by
          rw [add_mul, Real.exp_add, neg_mul]; ring
  set L : ℂ → ℂ := fun w => movingCuspHeadTransform w + N w
  have hLsplit : ∀ w : ℂ, 0 < w.re →
      (∫ u : ℝ, Complex.exp (w * u) * (movingCuspDualLimit u : ℂ)) = L w := by
    intro w hw
    have hint : Integrable fun u : ℝ => Complex.exp (w * u) * (movingCuspDualLimit u : ℂ) := by
      rw [← integrableOn_univ, show (Set.univ : Set ℝ) = Ioi 0 ∪ Iic 0 by
        ext u; simp only [mem_univ, mem_union, mem_Ioi, mem_Iic, true_iff]; exact lt_or_ge 0 u |>.imp id id]
      exact (hpos w hw).union (integrableOn_cexp_mul_movingCuspDualLimit_Iic hL2 hw le_rfl)
    have := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hint
    rw [compl_Ioi] at this
    rw [← this]
    rfl
  have hLd : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ L w := fun w hw =>
    (differentiable_movingCuspHeadTransform w).add (hNd w hw)
  -- analytic continuation of `ζ(w − 1/2) L(w) = F(w)`
  set f : ℂ → ℂ := fun w => riemannZeta (w - 1 / 2) * L w - XiC (Complex.I * w)
  set U : Set ℂ := {w : ℂ | 0 < w.re} \ {3 / 2}
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have h2U : (2 : ℂ) ∈ U := ⟨by simp, by norm_num⟩
  have hUc : IsPreconnected U :=
    GaloisForLFunctions.HTGeometry.isPreconnected_diff_of_countable_of_convex_complex
      (convex_halfSpace_re_gt 0) (isOpen_lt continuous_const Complex.continuous_re)
      (Set.countable_singleton _) h2U
  have hfan : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hw1 : w - 1 / 2 ≠ 1 := fun h => hw.2 (by rw [Set.mem_singleton_iff]; linear_combination h)
    have hz : DifferentiableAt ℂ (fun w => riemannZeta (w - 1 / 2)) w :=
      (differentiableAt_riemannZeta hw1).comp w (differentiableAt_id.sub_const _)
    exact ((hz.mul (hLd w hw.1)).sub ((XiC_differentiable _).comp w
      (differentiableAt_id.const_mul _))).differentiableWithinAt
  have hev : f =ᶠ[𝓝 2] 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (3 / 2 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    have hw' : 3 / 2 < w.re := hw
    have hz : riemannZeta (w - 1 / 2) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
    simp only [f, Pi.zero_apply]
    rw [← hLsplit w (by linarith), (integral_cexp_mul_movingCuspDualLimit hw').2, mul_comm,
      mul_assoc, inv_mul_cancel₀ hz, mul_one, sub_self]
  have hzero := hfan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc h2U hev
  obtain ⟨ρ, h0, h1, hζ⟩ := exists_riemannZeta_zero_mem_openStrip
  have hρU : ρ + 1 / 2 ∈ U := ⟨by simp; linarith, fun h => by
    rw [Set.mem_singleton_iff] at h
    have := congrArg Complex.re h; simp at this; linarith⟩
  have hf := hzero hρU
  simp only [f, Pi.zero_apply, show ρ + 1 / 2 - 1 / 2 = ρ by ring, hζ, zero_mul, zero_sub,
    neg_eq_zero] at hf
  rw [XiC_I_mul_eq_xi_half_add, show (1 / 2 : ℂ) + (ρ + 1 / 2) = 1 + ρ by ring] at hf
  exact xi_ne_zero_of_one_lt_re (by simp; linarith) hf

theorem lintegral_ofReal_movingCuspDualLimit_sq_Iio :
    ∫⁻ u in Iio (0 : ℝ), ENNReal.ofReal (movingCuspDualLimit u ^ 2) = ⊤ := by
  by_contra h
  apply not_integrableOn_movingCuspDualLimit_sq_Iio
  refine ⟨(continuous_movingCuspDualLimit.pow 2).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun u => ?_)) (lt_top_iff_ne_top.2 h)
  exact Real.enorm_of_nonneg (sq_nonneg _)

theorem continuous_movingCuspSource_theta (S : Finset ℕ) :
    Continuous (movingCuspSource S thetaCuspFullSource) := by
  unfold movingCuspSource
  exact continuous_finsetSum _ fun T _ => continuous_const.mul (continuous_const.mul
    (contDiff_thetaCuspFullSource.continuous.comp (continuous_id.add continuous_const)))

/-- **(6), moving density.**  Along every prime exhaustion the normalized weighted energy density
`|R_S(u)|² k(−log P − u)^{−c/P²}` converges pointwise to `|R_∞(u)|² exp(cπ e^{2u})`. -/
theorem PrimeExhaustion.tendsto_moving_density {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) (c u : ℝ) :
    Tendsto (fun N => movingCuspSource (S N) thetaCuspFullSource u ^ 2 *
        thetaCuspFullSource (-Real.log ((∏ p ∈ S N, p : ℕ) : ℝ) - u) ^
          (-(c / ((∏ p ∈ S N, p : ℕ) : ℝ) ^ 2))) atTop
      (𝓝 (movingCuspDualLimit u ^ 2 * Real.exp (c * Real.pi * Real.exp (2 * u)))) := by
  have h1 : Tendsto (fun N => movingCuspSource (S N) thetaCuspFullSource u) atTop
      (𝓝 (movingCuspDualLimit u)) :=
    (hS.tendstoUniformlyOn_movingCuspSource u u).tendsto_at ⟨le_rfl, le_rfl⟩
  exact (h1.pow 2).mul ((tendsto_thetaCuspFullSource_moving_rpow c u).comp
    (tendsto_natCast_atTop_atTop.comp hS.tendsto_primeProduct))

/-- **(7)** Along every prime exhaustion and for every `0 < c < 2`, the normalized terminal
energies `P ‖k_S‖²_{H_{c/P²}}` are finite but diverge. -/
theorem PrimeExhaustion.tendsto_moving_weighted_energy {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    {c : ℝ} (hc0 : 0 < c) (hc2 : c < 2) :
    (∀ N, ∫⁻ x, ENNReal.ofReal (((∏ p ∈ S N, p : ℕ) : ℝ) * thetaPowerWeightedEnergy
        (c / ((∏ p ∈ S N, p : ℕ) : ℝ) ^ 2) (thetaPrimeDeletion (S N) thetaCuspFullSource) x) < ⊤) ∧
    Tendsto (fun N => ∫⁻ x, ENNReal.ofReal (((∏ p ∈ S N, p : ℕ) : ℝ) * thetaPowerWeightedEnergy
        (c / ((∏ p ∈ S N, p : ℕ) : ℝ) ^ 2) (thetaPrimeDeletion (S N) thetaCuspFullSource) x)) atTop
      (𝓝 ⊤) := by
  set P : ℕ → ℝ := fun N => ((∏ p ∈ S N, p : ℕ) : ℝ)
  have hP : ∀ N, 1 ≤ P N := fun N => by
    simp only [P]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun p hp => (hS.prime N p hp).ne_zero)
  refine ⟨fun N => ?_, ?_⟩
  · have hq : 0 < c / P N ^ 2 := by have := hP N; positivity
    have hlt : c / P N ^ 2 < 2 / P N ^ 2 := by
      have := hP N; exact div_lt_div_of_pos_right hc2 (by positivity)
    have hmem := (thetaPrimeDeletion_memLp_iff (S N) (hS.prime N) _ hq).2 hlt
    have hint := (memLp_thetaPowerWeightedMeasure_iff _
      (continuous_thetaPrimeDeletion _ contDiff_thetaCuspFullSource.continuous)).1 hmem
    exact (hint.const_mul (P N)).lintegral_lt_top
  -- change of variables to the moving frame
  set G : ℕ → ℝ → ℝ := fun N u => movingCuspSource (S N) thetaCuspFullSource u ^ 2 *
    thetaCuspFullSource (-Real.log (P N) - u) ^ (-(c / P N ^ 2))
  have hchange : ∀ N, ∫⁻ x, ENNReal.ofReal (P N * thetaPowerWeightedEnergy (c / P N ^ 2)
      (thetaPrimeDeletion (S N) thetaCuspFullSource) x) = ∫⁻ u, ENNReal.ofReal (G N u) := by
    intro N
    rw [← lintegral_sub_left_eq_self (μ := volume)
      (fun x => ENNReal.ofReal (P N * thetaPowerWeightedEnergy (c / P N ^ 2)
        (thetaPrimeDeletion (S N) thetaCuspFullSource) x)) (-Real.log (P N))]
    refine lintegral_congr fun u => ?_
    congr 1
    have hR := movingCuspSource_eq_moebius_mul_deletion (hS.prime N) thetaCuspFullSource_neg u
    have hμ : ((ArithmeticFunction.moebius (∏ p ∈ S N, p) : ℤ) : ℝ) ^ 2 = 1 := by
      rw [moebius_prod_of_primes (hS.prime N)]; push_cast; rw [← pow_mul, mul_comm, pow_mul]; simp
    have hs : (((∏ p ∈ S N, p : ℕ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = P N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num [P]
    simp only [G, thetaPowerWeightedEnergy, hR, mul_pow, hμ, hs, one_mul]
    ring
  -- pointwise convergence of the moving densities
  have hPt : Tendsto P atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hS.tendsto_primeProduct
  have hGlim : ∀ u, Tendsto (fun N => G N u) atTop
      (𝓝 (movingCuspDualLimit u ^ 2 * Real.exp (c * Real.pi * Real.exp (2 * u)))) := by
    intro u
    have h1 : Tendsto (fun N => movingCuspSource (S N) thetaCuspFullSource u) atTop
        (𝓝 (movingCuspDualLimit u)) :=
      (hS.tendstoUniformlyOn_movingCuspSource u u).tendsto_at ⟨le_rfl, le_rfl⟩
    exact (h1.pow 2).mul ((tendsto_thetaCuspFullSource_moving_rpow c u).comp hPt)
  -- Fatou
  have hmeas : ∀ N, Measurable fun u => ENNReal.ofReal (G N u) := fun N => by
    refine (Continuous.measurable ?_).ennreal_ofReal
    exact ((continuous_movingCuspSource_theta _).pow 2).mul
      ((contDiff_thetaCuspFullSource.continuous.comp (continuous_const.sub continuous_id)).rpow_const
        fun u => Or.inl (thetaCuspFullSource_pos _).ne')
  have hliminf : ∀ u, liminf (fun N => ENNReal.ofReal (G N u)) atTop =
      ENNReal.ofReal (movingCuspDualLimit u ^ 2 * Real.exp (c * Real.pi * Real.exp (2 * u))) :=
    fun u => ((ENNReal.continuous_ofReal.tendsto _).comp (hGlim u)).liminf_eq
  have hfatou : ∫⁻ u, ENNReal.ofReal (movingCuspDualLimit u ^ 2 *
      Real.exp (c * Real.pi * Real.exp (2 * u))) ≤
        liminf (fun N => ∫⁻ u, ENNReal.ofReal (G N u)) atTop :=
    le_trans (le_of_eq (lintegral_congr fun u => (hliminf u).symm))
      (lintegral_liminf_le (μ := volume) (u := atTop) hmeas)
  have htop : ∫⁻ u, ENNReal.ofReal (movingCuspDualLimit u ^ 2 * Real.exp (c * Real.pi * Real.exp (2 * u))) = ⊤ := by
    refine top_le_iff.1 (le_trans (le_of_eq lintegral_ofReal_movingCuspDualLimit_sq_Iio.symm) ?_)
    refine le_trans (setLIntegral_mono' measurableSet_Iio fun u _ => ?_)
      (setLIntegral_le_lintegral (Iio 0) _)
    refine ENNReal.ofReal_le_ofReal ?_
    have : 1 ≤ Real.exp (c * Real.pi * Real.exp (2 * u)) := Real.one_le_exp (by positivity)
    nlinarith [sq_nonneg (movingCuspDualLimit u)]
  rw [htop] at hfatou
  refine (show Tendsto (fun N => ∫⁻ u, ENNReal.ofReal (G N u)) atTop (𝓝 ⊤) from ?_).congr
    fun N => (hchange N).symm
  rw [ENNReal.tendsto_nhds_top_iff_nat]
  intro n
  exact Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le (ENNReal.natCast_lt_top n) hfatou)

end

end RHTower
