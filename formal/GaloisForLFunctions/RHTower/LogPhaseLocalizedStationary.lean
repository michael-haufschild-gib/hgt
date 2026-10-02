import GaloisForLFunctions.RHTower.LogPhaseMorseSubstitution
import GaloisForLFunctions.RHTower.VanDerCorputLocal
import GaloisForLFunctions.RHTower.QuadraticPhaseStationary

/-!
# Signed remainder of the localized logarithmic saddle

After dividing out a vanishing saddle value, exact integration by parts retains
quadratic cancellation in the remainder. The actual analytic inverse of the
logarithmic Morse coordinate supplies all regularity for its localized Jacobian.
The capstone compares the complete localized logarithmic integral with its smooth
quadratic main; it does not assert positivity of the BAG self-target kernel.
-/

noncomputable section
open Set Complex MeasureTheory Filter
open scoped Topology ContDiff
namespace GaloisForLFunctions.RHTower

private theorem hasDerivAt_quadPhase (lam x : ℝ) :
    HasDerivAt (quadPhase lam)
      ((Complex.I * (lam : ℂ)) * (x : ℂ) * quadPhase lam x) x := by
  have hq : HasDerivAt (fun t : ℝ => lam * t ^ 2 / 2) (lam * x) x := by
    convert! ((hasDerivAt_pow 2 x).const_mul lam).div_const 2 using 1
    norm_num
    ring
  have he := (hq.ofReal_comp.mul_const Complex.I).cexp
  apply he.congr_deriv
  unfold quadPhase
  push_cast
  ring

/-- Exact cancellation of the saddle value leaves the derivative of its removable
first divided difference, retaining both signed endpoints. -/
theorem integral_quadratic_divided_remainder
    (lam a b : ℝ) {c c' : ℝ → ℂ}
    (hc : ∀ x ∈ uIcc a b, HasDerivAt c (c' x) x)
    (hc' : IntervalIntegrable c' volume a b) :
    (Complex.I * (lam : ℂ)) *
      (∫ x in a..b, (x : ℂ) * c x * quadPhase lam x) =
      c b * quadPhase lam b - c a * quadPhase lam a -
        ∫ x in a..b, c' x * quadPhase lam x := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hc
    (fun x _ => hasDerivAt_quadPhase lam x) hc'
    (show IntervalIntegrable
      (fun x => (Complex.I * (lam : ℂ)) * (x : ℂ) * quadPhase lam x)
      volume a b from (by unfold quadPhase; fun_prop : Continuous _).intervalIntegrable a b)
  rw [← hibp, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  ring

/-- The signed divided remainder retains quadratic oscillation after integration by parts.
This is the mechanism needed for a physical stationary error smaller than one per matrix entry. -/
theorem norm_integral_quadratic_divided_remainder_le
    {lam a b : ℝ} (hlam : 0 < lam) (hab : a ≤ b) {c c' c'' : ℝ → ℂ}
    (hc : ∀ x ∈ uIcc a b, HasDerivAt c (c' x) x)
    (hc' : ∀ x ∈ uIcc a b, HasDerivAt c' (c'' x) x)
    (hc'' : ContinuousOn c'' (uIcc a b)) :
    ‖∫ x in a..b, (x : ℂ) * c x * quadPhase lam x‖ ≤
      (‖c b‖ + ‖c a‖) / lam +
        32 * (‖c' b‖ + ‖c' a‖ + ∫ x in a..b, ‖c'' x‖) /
          (lam * Real.sqrt lam) := by
  have hcc : ContinuousOn c' (uIcc a b) :=
    fun x hx => (hc' x hx).continuousAt.continuousWithinAt
  have hi := integral_quadratic_divided_remainder lam a b hc
    hcc.intervalIntegrable
  have htest := _root_.RHTower.secondDerivTestOn hab hlam
    (φ := fun x => lam * x ^ 2 / 2) (φ' := fun x => lam * x) (φ'' := fun _ => lam)
    (A := c') (A' := c'')
    (fun x _ => by
      convert! ((hasDerivAt_pow 2 x).const_mul lam).div_const 2 using 1
      norm_num
      ring)
    (fun x _ => by simpa using (hasDerivAt_id' x).const_mul lam)
    continuousOn_const
    (fun x hx => hc' x (by rwa [uIcc_of_le hab]))
    (by simpa only [uIcc_of_le hab] using hc'') (fun _ _ => le_rfl)
  have hkernel (x : ℝ) : Complex.exp (Complex.I * ((lam * x ^ 2 / 2 : ℝ) : ℂ)) =
      quadPhase lam x := by unfold quadPhase; rw [mul_comm]
  simp_rw [hkernel] at htest
  have hn : ∀ x, ‖quadPhase lam x‖ = 1 := by
    intro x
    simp only [quadPhase, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  have hnorm : lam * ‖∫ x in a..b, (x : ℂ) * c x * quadPhase lam x‖ ≤
      ‖c b‖ + ‖c a‖ +
        32 * (‖c' b‖ + ‖c' a‖ + ∫ x in a..b, ‖c'' x‖) / Real.sqrt lam := by
    calc
      _ = ‖(Complex.I * (lam : ℂ)) *
          (∫ x in a..b, (x : ℂ) * c x * quadPhase lam x)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hlam]
      _ = _ := congrArg norm hi
      _ ≤ ‖c b * quadPhase lam b - c a * quadPhase lam a‖ +
          ‖∫ x in a..b, c' x * quadPhase lam x‖ := norm_sub_le _ _
      _ ≤ ‖c b‖ + ‖c a‖ +
          32 * (‖c' b‖ + ‖c' a‖ + ∫ x in a..b, ‖c'' x‖) / Real.sqrt lam := by
        apply add_le_add _ htest
        simpa only [norm_mul, hn, mul_one] using
          norm_sub_le (c b * quadPhase lam b) (c a * quadPhase lam a)
  calc
    _ ≤ (‖c b‖ + ‖c a‖ +
          32 * (‖c' b‖ + ‖c' a‖ + ∫ x in a..b, ‖c'' x‖) / Real.sqrt lam) / lam :=
      (le_div_iff₀ hlam).mpr (by simpa only [mul_comm] using hnorm)
    _ = _ := by field_simp

private theorem contDiff_dslope_of_analytic_center {B : ℝ → ℂ}
    (hB : ContDiff ℝ ∞ B) (ha : AnalyticAt ℝ B 0) :
    ContDiff ℝ ∞ (dslope B 0) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · obtain ⟨p, hp⟩ := ha
    exact hp.has_fpower_series_dslope_fslope.analyticAt.contDiffAt
  · have hm : ContDiffAt ℝ ∞ (fun t : ℝ => t⁻¹ • (B t - B 0)) x :=
      (contDiffAt_id.inv hx).smul (hB.contDiffAt.sub contDiffAt_const)
    apply hm.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hx] with t ht
    rw [dslope_of_ne B ht, slope_def_module, sub_zero]

private theorem hasCompactSupport_dslope_of_zero {B : ℝ → ℂ}
    (hc : HasCompactSupport B) (h0 : B 0 = 0) : HasCompactSupport (dslope B 0) := by
  apply hc.mono'
  intro x hx
  by_contra hn
  have hz : dslope B 0 x = 0 := by
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [dslope_same, deriv_of_notMem_tsupport hn]
    · rw [dslope_of_ne B hx0, slope_def_module, h0,
        image_eq_zero_of_notMem_tsupport hn, sub_self, smul_zero]
  exact hx hz

/-- A smooth compact amplitude whose saddle value vanishes has a full extra inverse-frequency
factor. The statement integrates the entire amplitude; no neighborhood or tail is deleted. -/
theorem exists_quadratic_zero_saddle_remainder {B : ℝ → ℂ}
    (hB : ContDiff ℝ ∞ B) (ha : AnalyticAt ℝ B 0)
    (hs : HasCompactSupport B) (h0 : B 0 = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      ‖∫ x : ℝ, B x * quadPhase lam x‖ ≤ C / (lam * Real.sqrt lam) := by
  let c := dslope B 0
  have hc : ContDiff ℝ ∞ c := contDiff_dslope_of_analytic_center hB ha
  have hc1 : ContDiff ℝ ∞ (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
  have hc2 : ContDiff ℝ ∞ (deriv (deriv c)) := (contDiff_infty_iff_deriv.mp hc1).2
  have hcs : HasCompactSupport c := hasCompactSupport_dslope_of_zero hs h0
  have hi2 : Integrable (fun x : ℝ => ‖deriv (deriv c) x‖) :=
    (hc2.continuous.integrable_of_hasCompactSupport hcs.deriv.deriv).norm
  let V := ∫ x : ℝ, ‖deriv (deriv c) x‖
  have hV : 0 ≤ V := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨1 + 32 * V, by positivity, ?_⟩
  intro lam hlam
  obtain ⟨R, hR, hbound⟩ := hcs.isCompact.isBounded.exists_pos_norm_le
  let L := R + 1
  have hL : 0 < L := by dsimp [L]; linarith
  have hn (x : ℝ) (hx : L ≤ |x|) : x ∉ tsupport c := by
    intro hmem
    have hh := hbound x hmem
    rw [Real.norm_eq_abs] at hh
    dsimp [L] at hx
    linarith
  have hcz (x : ℝ) (hx : L ≤ |x|) : c x = 0 :=
    image_eq_zero_of_notMem_tsupport (hn x hx)
  have hc1z (x : ℝ) (hx : L ≤ |x|) : deriv c x = 0 :=
    deriv_of_notMem_tsupport (hn x hx)
  have hc2z (x : ℝ) (hx : L ≤ |x|) : deriv (deriv c) x = 0 :=
    deriv_of_notMem_tsupport (fun hm => hn x hx (tsupport_deriv_subset hm))
  have hshape (x : ℝ) : B x = (x : ℂ) * c x := by
    have hh := sub_smul_dslope B 0 x
    simpa only [sub_zero, h0, Complex.real_smul] using hh.symm
  have hout (x : ℝ) (hx : x ∉ Ioc (-L) L) : L ≤ |x| := by
    by_contra hh
    have hh' := abs_lt.mp (lt_of_not_ge hh)
    exact hx ⟨hh'.1, hh'.2.le⟩
  have hfinite : (∫ x in (-L)..L, (x : ℂ) * c x * quadPhase lam x) =
      ∫ x : ℝ, B x * quadPhase lam x := by
    rw [intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hcz x (hout x hx), mul_zero, zero_mul])]
    simp_rw [hshape]
  have hVfinite : (∫ x in (-L)..L, ‖deriv (deriv c) x‖) = V := by
    rw [intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hc2z x (hout x hx), norm_zero])
  have hb := norm_integral_quadratic_divided_remainder_le hlam (by linarith : -L ≤ L)
    (c := c) (c' := deriv c) (c'' := deriv (deriv c))
    (fun x _ => (hc.differentiable (by simp) x).hasDerivAt)
    (fun x _ => (hc1.differentiable (by simp) x).hasDerivAt)
    hc2.continuous.continuousOn
  have hLp : L ≤ |L| := le_abs_self _
  have hLn : L ≤ |-L| := by rw [abs_neg]; exact hLp
  rw [hfinite, hcz L hLp, hcz (-L) hLn, hc1z L hLp, hc1z (-L) hLn,
    norm_zero, zero_add, zero_div, zero_add, hVfinite] at hb
  exact hb.trans (by apply div_le_div_of_nonneg_right _ (by positivity); linarith)

/-- The actual inverse logarithmic coordinate has a localized Jacobian correction with
vanishing saddle value. All smoothness and support properties are constructed here. -/
theorem exists_logPhaseMorse_jacobian_remainder :
    ∃ (r C : ℝ) (j : ℝ → ℝ) (cutoff : ContDiffBump (0 : ℝ)),
      0 < r ∧ 0 < C ∧ cutoff.rOut < r ∧ j 0 = 0 ∧ deriv j 0 = 1 ∧
      (∀ w ∈ Icc (-r) r, AnalyticAt ℝ j w ∧ 0 < deriv j w ∧ -1 < j w ∧
        logPhaseMorse (j w) = w ∧ logPhaseProfile (j w) = -(w ^ 2) / 2) ∧
      ∀ lam : ℝ, 0 < lam →
        ‖∫ w : ℝ, (cutoff w : ℂ) * ((deriv j w - 1 : ℝ) : ℂ) * quadPhase lam w‖ ≤
          C / (lam * Real.sqrt lam) := by
  obtain ⟨r, j, hr, hj0, hjd, hj⟩ := exists_logPhaseMorse_inverse
  let cutoff : ContDiffBump (0 : ℝ) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let B : ℝ → ℂ := fun w => (cutoff w : ℂ) * ((deriv j w - 1 : ℝ) : ℂ)
  have hB : ContDiff ℝ ∞ B := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w ∈ Icc (-r) r
    · have hd : ContDiffAt ℝ ∞ (fun v => ((deriv j v - 1 : ℝ) : ℂ)) w :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp w
          ((hj w hw).1.deriv.contDiffAt.sub contDiffAt_const)
      exact (Complex.ofRealCLM.contDiff.contDiffAt.comp w cutoff.contDiffAt).mul hd
    · have hn : w ∉ tsupport cutoff := by
        rw [cutoff.tsupport_eq]
        intro hmem
        have hdist : |w| ≤ r / 2 := by
          simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, cutoff] using hmem
        have habs := abs_le.mp hdist
        apply hw
        constructor <;> linarith
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hn)
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hz] with v hv
      dsimp [B]
      rw [hv]
      simp
  have ha : AnalyticAt ℝ B 0 := by
    have hbase : AnalyticAt ℝ (fun w => ((deriv j w - 1 : ℝ) : ℂ)) 0 :=
      (Complex.ofRealCLM.analyticAt _).comp
        ((hj 0 ⟨by linarith, by linarith⟩).1.deriv.sub analyticAt_const)
    apply hbase.congr
    filter_upwards [cutoff.eventuallyEq_one] with w hw
    dsimp [B]
    rw [hw]
    simp
  have hs : HasCompactSupport B := by
    apply cutoff.hasCompactSupport.mono'
    intro w hw
    by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    apply hw
    dsimp [B]
    rw [hz]
    simp
  have h0 : B 0 = 0 := by simp [B, hjd]
  obtain ⟨C, hC, hbound⟩ := exists_quadratic_zero_saddle_remainder hB ha hs h0
  refine ⟨r, C, j, cutoff, hr, hC, by dsimp [cutoff]; linarith, hj0, hjd,
    hj, ?_⟩
  exact hbound

/-- A complete smooth localization of the actual logarithmic phase has the universal
quadratic main with a source-derived, oscillatory Jacobian remainder. -/
theorem exists_logPhaseMorse_localized_stationary :
    ∃ (r C : ℝ) (j : ℝ → ℝ) (cutoff : ContDiffBump (0 : ℝ)),
      0 < r ∧ 0 < C ∧ cutoff.rOut < r ∧ j 0 = 0 ∧ deriv j 0 = 1 ∧
      ∀ lam : ℝ, 0 < lam →
        ‖(∫ v in j (-r)..j r, (cutoff (logPhaseMorse v) : ℂ) *
            Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ))) -
          ∫ w in (-r)..r, (cutoff w : ℂ) * quadPhase (-lam) w‖ ≤
            C / (lam * Real.sqrt lam) := by
  obtain ⟨r, C, j, cutoff, hr, hC, hcut, hj0, hjd, hj, hbound⟩ :=
    exists_logPhaseMorse_jacobian_remainder
  refine ⟨r, C, j, cutoff, hr, hC, hcut, hj0, hjd, ?_⟩
  intro lam hlam
  let B : ℝ → ℂ := fun w => (cutoff w : ℂ) * ((deriv j w - 1 : ℝ) : ℂ)
  have hconj (w : ℝ) :
      B w * quadPhase (-lam) w = (starRingEnd ℂ) (B w * quadPhase lam w) := by
    dsimp [B, quadPhase]
    rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 2
    push_cast
    ring
  have hnegative : ‖∫ w : ℝ, B w * quadPhase (-lam) w‖ ≤
      C / (lam * Real.sqrt lam) := by
    simp_rw [hconj]
    rw [integral_conj, RCLike.norm_conj]
    exact hbound lam hlam
  have hfinite : (∫ w in (-r)..r, B w * quadPhase (-lam) w) =
      ∫ w : ℝ, B w * quadPhase (-lam) w := by
    rw [intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    have hwr : r ≤ |w| := by
      by_contra hn
      have hh := abs_lt.mp (lt_of_not_ge hn)
      exact hw ⟨hh.1, hh.2.le⟩
    have hz := cutoff.zero_of_le_dist
      (by simpa only [Real.dist_eq, sub_zero] using hcut.le.trans hwr)
    simp [B, hz]
  have hsub : uIcc (-r) r = Icc (-r) r := uIcc_of_le (by linarith)
  have hcont : ContinuousOn j (uIcc (-r) r) := by
    rw [hsub]
    exact fun w hw => (hj w hw).1.continuousAt.continuousWithinAt
  have hdcont : ContinuousOn (deriv j) (uIcc (-r) r) := by
    rw [hsub]
    exact fun w hw => (hj w hw).1.deriv.continuousAt.continuousWithinAt
  have hmem {w : ℝ} (hw : w ∈ Ioo (min (-r) r) (max (-r) r)) :
      w ∈ Icc (-r) r := by
    simpa only [min_eq_left (by linarith : -r ≤ r),
      max_eq_right (by linarith : -r ≤ r)] using
      (show w ∈ Icc (min (-r) r) (max (-r) r) from ⟨hw.1.le, hw.2.le⟩)
  have he := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := fun v => (cutoff (logPhaseMorse v) : ℂ) *
      Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ))) hcont
    (fun w hw => (hj w (hmem hw)).1.differentiableAt.hasDerivAt)
    (fun w hw => (hj w (hmem hw)).2.1.le)
  have hpoint (w : ℝ) (hw : w ∈ uIcc (-r) r) :
      deriv j w • ((fun v => (cutoff (logPhaseMorse v) : ℂ) *
        Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ))) ∘ j) w =
      (cutoff w : ℂ) * ((deriv j w : ℝ) : ℂ) * quadPhase (-lam) w := by
    rw [hsub] at hw
    obtain ⟨_, _, _, hright, hphase⟩ := hj w hw
    simp only [Function.comp_apply, hright, hphase, Complex.real_smul, quadPhase]
    have hp : Complex.I * ((lam * (-(w ^ 2) / 2) : ℝ) : ℂ) =
        (((-lam) * w ^ 2 / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hp]
    ring
  have horiginal : (∫ v in j (-r)..j r, (cutoff (logPhaseMorse v) : ℂ) *
      Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ))) =
      ∫ w in (-r)..r, (cutoff w : ℂ) * ((deriv j w : ℝ) : ℂ) *
        quadPhase (-lam) w := by
    rw [← he]
    exact intervalIntegral.integral_congr hpoint
  have hcutc : Continuous (fun w : ℝ => (cutoff w : ℂ)) :=
    Complex.continuous_ofReal.comp cutoff.continuous
  have hfirst : IntervalIntegrable
      (fun w => (cutoff w : ℂ) * ((deriv j w : ℝ) : ℂ) * quadPhase (-lam) w)
      volume (-r) r :=
    ((hcutc.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hdcont)).mul
      (continuous_quadPhase (-lam)).continuousOn).intervalIntegrable
  have hsecond : IntervalIntegrable (fun w => (cutoff w : ℂ) * quadPhase (-lam) w)
      volume (-r) r := (hcutc.mul (continuous_quadPhase (-lam))).intervalIntegrable _ _
  rw [horiginal, ← intervalIntegral.integral_sub hfirst hsecond]
  have hdiff : (∫ w in (-r)..r,
      (cutoff w : ℂ) * ((deriv j w : ℝ) : ℂ) * quadPhase (-lam) w -
        (cutoff w : ℂ) * quadPhase (-lam) w) =
      ∫ w in (-r)..r, B w * quadPhase (-lam) w := by
    apply intervalIntegral.integral_congr
    intro w _
    dsimp [B]
    push_cast
    ring
  rw [hdiff, hfinite]
  exact hnegative

end GaloisForLFunctions.RHTower
