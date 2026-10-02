import GaloisForLFunctions.RHTower.LogPhaseLocalizedStationary
import GaloisForLFunctions.HTGeometry.PowerTailIntegral

/-!
# Full Fresnel main for the smooth logarithmic saddle

The smooth cutoff has a full oriented Fresnel main. Its divided remainder has
explicit inverse-power tails on both rays; signed integration by parts retains
those tails before the outer truncation tends to infinity. The actual logarithmic
Morse substitution then gives the complete localized stationary integral.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff
namespace GaloisForLFunctions.RHTower

private def smoothFresnelSlope (cutoff : ContDiffBump (0 : ℝ)) (x : ℝ) : ℂ :=
  (((cutoff x - 1) / x : ℝ) : ℂ)

private theorem contDiff_smoothFresnelSlope (cutoff : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ ∞ (smoothFresnelSlope cutoff) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [cutoff.eventuallyEq_one] with x hx
    simp [smoothFresnelSlope, hx]
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((cutoff.contDiffAt.sub contDiffAt_const).div contDiffAt_id hx)

private theorem smoothFresnelSlope_identity (cutoff : ContDiffBump (0 : ℝ)) (x : ℝ) :
    (x : ℂ) * smoothFresnelSlope cutoff x = (cutoff x : ℂ) - 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : cutoff 0 = 1 := cutoff.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall, dist_self] using cutoff.rIn_pos.le)
    simp [h0]
  · unfold smoothFresnelSlope
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hx]

private theorem smoothFresnelSlope_tail (cutoff : ContDiffBump (0 : ℝ))
    {x : ℝ} (hx : cutoff.rOut < |x|) :
    smoothFresnelSlope cutoff =ᶠ[𝓝 x] fun t : ℝ => ((-t⁻¹ : ℝ) : ℂ) := by
  have hn : x ∉ tsupport cutoff := by
    rw [cutoff.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact not_le.mpr hx
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with t ht
  simp [smoothFresnelSlope, ht, div_eq_mul_inv]

private theorem hasDerivAt_negative_inverse (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => ((-t⁻¹ : ℝ) : ℂ)) (((x ^ 2)⁻¹ : ℝ) : ℂ) x := by
  simpa using ((hasDerivAt_inv hx).neg).ofReal_comp

private theorem hasDerivAt_inverse_square (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => (((t ^ 2)⁻¹ : ℝ) : ℂ)) ((-2 / x ^ 3 : ℝ) : ℂ) x := by
  have hd := ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx)).ofReal_comp
  apply hd.congr_deriv
  push_cast
  field_simp

private theorem smoothFresnelSlope_tail_jets (cutoff : ContDiffBump (0 : ℝ))
    {x : ℝ} (hx : cutoff.rOut < |x|) :
    smoothFresnelSlope cutoff x = ((-x⁻¹ : ℝ) : ℂ) ∧
      deriv (smoothFresnelSlope cutoff) x = (((x ^ 2)⁻¹ : ℝ) : ℂ) ∧
      deriv (deriv (smoothFresnelSlope cutoff)) x = ((-2 / x ^ 3 : ℝ) : ℂ) := by
  have hx0 : x ≠ 0 := by intro hz; subst x; simp only [abs_zero] at hx; linarith [cutoff.rOut_pos]
  have he := smoothFresnelSlope_tail cutoff hx
  have hmodel : deriv (fun t : ℝ => ((-t⁻¹ : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun t : ℝ => (((t ^ 2)⁻¹ : ℝ) : ℂ) := by
    filter_upwards [isOpen_ne.mem_nhds hx0] with t ht
    exact (hasDerivAt_negative_inverse t ht).deriv
  refine ⟨he.eq_of_nhds, he.deriv_eq.trans (hasDerivAt_negative_inverse x hx0).deriv, ?_⟩
  rw [he.deriv.deriv_eq, hmodel.deriv_eq]
  exact (hasDerivAt_inverse_square x hx0).deriv

private theorem integrable_smoothFresnelSlope_second (cutoff : ContDiffBump (0 : ℝ)) :
    Integrable (fun x => ‖deriv (deriv (smoothFresnelSlope cutoff)) x‖) := by
  have hc := contDiff_smoothFresnelSlope cutoff
  have hc1 := (contDiff_infty_iff_deriv.mp hc).2
  have hc2 := (contDiff_infty_iff_deriv.mp hc1).2
  let R := cutoff.rOut + 1
  have hR : 0 < R := by dsimp [R]; linarith [cutoff.rOut_pos]
  have htail : IntegrableOn (fun x => ‖deriv (deriv (smoothFresnelSlope cutoff)) x‖)
      {x : ℝ | R ≤ |x|} := by
    have hb : IntegrableOn (fun x : ℝ => 2 * |x| ^ (-3 : ℝ))
        {x : ℝ | R ≤ |x|} volume :=
      (GaloisForLFunctions.HTGeometry.integrableOn_powerTail hR
      (show (1 : ℝ) < 3 by norm_num)).const_mul 2
    apply hb.congr_fun _ (GaloisForLFunctions.HTGeometry.measurableSet_centralTail R)
    intro x hx
    have hxx : cutoff.rOut < |x| := by dsimp [R] at hx; linarith
    dsimp only
    rw [(smoothFresnelSlope_tail_jets cutoff hxx).2.2]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow]
    rw [Real.rpow_neg (abs_nonneg x)]
    norm_num
    ring
  have hcenter : IntegrableOn (fun x => ‖deriv (deriv (smoothFresnelSlope cutoff)) x‖)
      (Icc (-R) R) volume :=
    hc2.continuous.norm.continuousOn.integrableOn_compact isCompact_Icc
  have hcover : Icc (-R) R ∪ {x : ℝ | R ≤ |x|} = univ := by
    ext x
    simp only [mem_union, mem_Icc, mem_setOf_eq, mem_univ, iff_true]
    by_cases hx : R ≤ |x|
    · exact Or.inr hx
    · have hb := abs_lt.mp (lt_of_not_ge hx)
      exact Or.inl ⟨hb.1.le, hb.2.le⟩
  have hu := hcenter.union htail
  rw [hcover] at hu
  exact integrableOn_univ.mp hu

/-- Every source smooth plateau cutoff has the full Fresnel main, with the complete
oscillatory tail and divided-remainder variation retained. -/
theorem exists_smoothCutoff_fresnel_remainder (cutoff : ContDiffBump (0 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      ‖(∫ x : ℝ, (cutoff x : ℂ) * quadPhase lam x) -
        (Real.sqrt (2 * Real.pi / lam) : ℂ) *
          Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I)‖ ≤ C / (lam * Real.sqrt lam) := by
  let c := smoothFresnelSlope cutoff
  have hc := contDiff_smoothFresnelSlope cutoff
  have hc1 := (contDiff_infty_iff_deriv.mp hc).2
  have hc2 := (contDiff_infty_iff_deriv.mp hc1).2
  have hi := integrable_smoothFresnelSlope_second cutoff
  let V := ∫ x : ℝ, ‖deriv (deriv c) x‖
  have hV : 0 ≤ V := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨1 + 32 * V, by positivity, ?_⟩
  intro lam hlam
  let M : ℂ := (Real.sqrt (2 * Real.pi / lam) : ℂ) *
    Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I)
  let J : ℂ := ∫ x : ℝ, (cutoff x : ℂ) * quadPhase lam x
  have hfinite (R : ℝ) (hR : cutoff.rOut + 1 ≤ R) :
      ‖J - M‖ ≤ (10 / lam) * R⁻¹ +
        (32 / (lam * Real.sqrt lam)) * (2 * (R⁻¹) ^ 2 + V) := by
    have hR0 : 0 < R := by linarith [cutoff.rOut_pos]
    have hRout : cutoff.rOut < R := by linarith
    have hRp : cutoff.rOut < |R| := by rwa [abs_of_pos hR0]
    have hRn : cutoff.rOut < |-R| := by rwa [abs_neg]
    have hjetsP := smoothFresnelSlope_tail_jets cutoff hRp
    have hjetsN := smoothFresnelSlope_tail_jets cutoff hRn
    have hce : ‖c R‖ = R⁻¹ ∧ ‖c (-R)‖ = R⁻¹ := by
      constructor
      · rw [show c R = ((-R⁻¹ : ℝ) : ℂ) from hjetsP.1, Complex.norm_real,
          Real.norm_eq_abs, abs_neg, abs_inv, abs_of_pos hR0]
      · rw [show c (-R) = ((-(-R)⁻¹ : ℝ) : ℂ) from hjetsN.1, Complex.norm_real,
          Real.norm_eq_abs, abs_neg, abs_inv, abs_neg, abs_of_pos hR0]
    have hc1e : ‖deriv c R‖ = (R⁻¹) ^ 2 ∧ ‖deriv c (-R)‖ = (R⁻¹) ^ 2 := by
      constructor
      · rw [show deriv c R = (((R ^ 2)⁻¹ : ℝ) : ℂ) from hjetsP.2.1,
          Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos hR0, inv_pow]
      · rw [show deriv c (-R) = ((((-R) ^ 2)⁻¹ : ℝ) : ℂ) from hjetsN.2.1,
          Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_pow, abs_neg,
          abs_of_pos hR0, inv_pow]
    have hint : (∫ x in (-R)..R, (cutoff x : ℂ) * quadPhase lam x) = J := by
      rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hRx : R ≤ |x| := by
        by_contra hn
        have hh := abs_lt.mp (lt_of_not_ge hn)
        exact hx ⟨hh.1, hh.2.le⟩
      have hz := cutoff.zero_of_le_dist
        (by simpa only [Real.dist_eq, sub_zero] using hRout.le.trans hRx)
      simp [hz]
    have hcutc : Continuous (fun x : ℝ => (cutoff x : ℂ)) :=
      Complex.continuous_ofReal.comp cutoff.continuous
    have hcuti : IntervalIntegrable (fun x => (cutoff x : ℂ) * quadPhase lam x) volume (-R) R :=
      (hcutc.mul (continuous_quadPhase lam)).intervalIntegrable (-R) R
    have hquadi : IntervalIntegrable (quadPhase lam) volume (-R) R :=
      (continuous_quadPhase lam).intervalIntegrable (-R) R
    have hsplit : J - (∫ x in (-R)..R, quadPhase lam x) =
        ∫ x in (-R)..R, (x : ℂ) * c x * quadPhase lam x := by
      rw [← hint, ← intervalIntegral.integral_sub hcuti hquadi]
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [show (x : ℂ) * c x = (cutoff x : ℂ) - 1 from smoothFresnelSlope_identity cutoff x]
      ring
    have hrem := norm_integral_quadratic_divided_remainder_le hlam (by linarith : -R ≤ R)
      (c := c) (c' := deriv c) (c'' := deriv (deriv c))
      (fun x _ => (hc.differentiable (by simp) x).hasDerivAt)
      (fun x _ => (hc1.differentiable (by simp) x).hasDerivAt) hc2.continuous.continuousOn
    have hmass : (∫ x in (-R)..R, ‖deriv (deriv c) x‖) ≤ V := by
      rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
      exact setIntegral_le_integral hi (Eventually.of_forall (fun _ => norm_nonneg _))
    rw [hce.1, hce.2, hc1e.1, hc1e.2] at hrem
    have hquad := norm_integral_quadPhase_sub_le hlam hR0
    calc
      ‖J - M‖ = ‖(J - (∫ x in (-R)..R, quadPhase lam x)) +
          ((∫ x in (-R)..R, quadPhase lam x) - M)‖ := by congr 1; ring
      _ ≤ ‖J - (∫ x in (-R)..R, quadPhase lam x)‖ +
          ‖(∫ x in (-R)..R, quadPhase lam x) - M‖ := norm_add_le _ _
      _ ≤ (R⁻¹ + R⁻¹) / lam +
          32 * ((R⁻¹) ^ 2 + (R⁻¹) ^ 2 + V) / (lam * Real.sqrt lam) +
            8 / (lam * R) := by
        apply add_le_add _ hquad
        rw [hsplit]
        apply hrem.trans
        gcongr
      _ = _ := by ring
  have ht : Tendsto (fun R : ℝ => (10 / lam) * R⁻¹ +
      (32 / (lam * Real.sqrt lam)) * (2 * (R⁻¹) ^ 2 + V)) atTop
      (nhds (32 * V / (lam * Real.sqrt lam))) := by
    convert (tendsto_inv_atTop_zero.const_mul (10 / lam)).add
      (((tendsto_inv_atTop_zero.pow 2).const_mul 2).add_const V |>.const_mul
        (32 / (lam * Real.sqrt lam))) using 1
    simp
    ring
  have hlimit : ‖J - M‖ ≤ 32 * V / (lam * Real.sqrt lam) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds ht (eventually_atTop.2 ⟨cutoff.rOut + 1, hfinite⟩)
  exact hlimit.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))

/-- Reversing the entire smooth phase conjugates its full Fresnel main and remainder. -/
theorem exists_smoothCutoff_fresnel_negative_remainder (cutoff : ContDiffBump (0 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      ‖(∫ x : ℝ, (cutoff x : ℂ) * quadPhase (-lam) x) -
        (Real.sqrt (2 * Real.pi / lam) : ℂ) *
          Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)‖ ≤ C / (lam * Real.sqrt lam) := by
  obtain ⟨C, hC, hbound⟩ := exists_smoothCutoff_fresnel_remainder cutoff
  refine ⟨C, hC, ?_⟩
  intro lam hlam
  have he (x : ℝ) : (cutoff x : ℂ) * quadPhase (-lam) x =
      (starRingEnd ℂ) ((cutoff x : ℂ) * quadPhase lam x) := by
    unfold quadPhase
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    congr 2
    push_cast
    ring
  have hm : (Real.sqrt (2 * Real.pi / lam) : ℂ) *
      Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I) =
      (starRingEnd ℂ) ((Real.sqrt (2 * Real.pi / lam) : ℂ) *
        Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I)) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    congr 2
    push_cast
    ring
  simp_rw [he]
  rw [integral_conj, hm, ← map_sub, RCLike.norm_conj]
  exact hbound lam hlam

/-- The actual smooth logarithmic saddle has its full oriented Fresnel main.
Its complete localized remainder gains three half powers of the oscillation scale. -/
theorem exists_logPhaseMorse_full_fresnel_stationary :
    ∃ (r C : ℝ) (j : ℝ → ℝ) (cutoff : ContDiffBump (0 : ℝ)),
      0 < r ∧ 0 < C ∧ cutoff.rOut < r ∧ j 0 = 0 ∧ deriv j 0 = 1 ∧
      ∀ lam : ℝ, 0 < lam →
        ‖(∫ v in j (-r)..j r, (cutoff (logPhaseMorse v) : ℂ) *
            Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ))) -
          (Real.sqrt (2 * Real.pi / lam) : ℂ) *
            Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)‖ ≤ C / (lam * Real.sqrt lam) := by
  obtain ⟨r, Cj, j, cutoff, hr, hCj, hcut, hj0, hjd, hbound⟩ :=
    exists_logPhaseMorse_localized_stationary
  obtain ⟨Cf, hCf, hfres⟩ := exists_smoothCutoff_fresnel_negative_remainder cutoff
  refine ⟨r, Cj + Cf, j, cutoff, hr, add_pos hCj hCf, hcut, hj0, hjd, ?_⟩
  intro lam hlam
  have hmain : (∫ w in (-r)..r, (cutoff w : ℂ) * quadPhase (-lam) w) =
      ∫ w : ℝ, (cutoff w : ℂ) * quadPhase (-lam) w := by
    rw [intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    have hh : r ≤ |w| := by
      by_contra hn
      have hh := abs_lt.mp (lt_of_not_ge hn)
      exact hw ⟨hh.1, hh.2.le⟩
    have hz := cutoff.zero_of_le_dist
      (by simpa only [Real.dist_eq, sub_zero] using hcut.le.trans hh)
    simp [hz]
  have hb := hbound lam hlam
  rw [hmain] at hb
  calc
    _ ≤ ‖(∫ v in j (-r)..j r, (cutoff (logPhaseMorse v) : ℂ) *
          Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ))) -
            ∫ w : ℝ, (cutoff w : ℂ) * quadPhase (-lam) w‖ +
        ‖(∫ w : ℝ, (cutoff w : ℂ) * quadPhase (-lam) w) -
          (Real.sqrt (2 * Real.pi / lam) : ℂ) *
            Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Cj / (lam * Real.sqrt lam) + Cf / (lam * Real.sqrt lam) :=
      add_le_add hb (hfres lam hlam)
    _ = _ := by ring

end GaloisForLFunctions.RHTower
