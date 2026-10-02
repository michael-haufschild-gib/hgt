import GaloisForLFunctions.RHTower.SmoothQuadraticFamily

/-!
# The logarithmic saddle with a fixed physical height window

The actual Morse inverse and a smooth family stationary theorem retain the
physical cutoff at every saddle ratio, including its transition regions.
A source-defined window supported in [1,2] supplies all regularity inputs.
This leaf treats the complete localized saddle; the complementary window
is still required before a full physical-kernel theorem.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff
namespace GaloisForLFunctions.RHTower

/-- A single logarithmic localization works for every smooth physical height window.
Its complete stationary remainder is uniform across a compact set of saddle-to-height ratios,
including every smooth cutoff transition. -/
theorem exists_logPhaseMorse_physical_window_family :
    ∃ (r : ℝ) (j : ℝ → ℝ) (eta : ContDiffBump (0 : ℝ)),
      0 < r ∧ eta.rOut < r ∧ j 0 = 0 ∧ deriv j 0 = 1 ∧
      (∀ w ∈ Icc (-r) r, AnalyticAt ℝ j w ∧ 0 < deriv j w ∧ -1 < j w ∧
        logPhaseMorse (j w) = w ∧ logPhaseProfile (j w) = -(w ^ 2) / 2) ∧
      ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → ∀ (K : Set ℝ), IsCompact K →
        ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ lam : ℝ, 0 < lam →
          ‖(∫ v in j (-r)..j r, (eta (logPhaseMorse v) : ℂ) * W (p * (1 + v)) *
              Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ))) -
            W p * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
              Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)‖ ≤
                C / (lam * Real.sqrt lam) := by
  obtain ⟨r, j, hr, hj0, hjd, hj⟩ := exists_logPhaseMorse_inverse
  let eta : ContDiffBump (0 : ℝ) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have heta : eta.rOut < r := by dsimp [eta]; linarith
  refine ⟨r, j, eta, hr, heta, hj0, hjd, hj, ?_⟩
  intro W hW K hK
  let B : ℝ × ℝ → ℂ := fun q =>
    (eta q.2 : ℂ) * ((deriv j q.2 : ℝ) : ℂ) * W (q.1 * (1 + j q.2))
  have hB : ContDiff ℝ ∞ B := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q.2 ∈ Icc (-r) r
    · have hjq : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => j z.2) q :=
        (hj q.2 hq).1.contDiffAt.comp q contDiffAt_snd
      have hdq : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => ((deriv j z.2 : ℝ) : ℂ)) q :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp q
          ((hj q.2 hq).1.deriv.contDiffAt.comp q contDiffAt_snd)
      have heq : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (eta z.2 : ℂ)) q :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp q
          (eta.contDiffAt.comp q contDiffAt_snd)
      exact (heq.mul hdq).mul
        (hW.contDiffAt.comp q (contDiffAt_fst.mul (contDiffAt_const.add hjq)))
    · have hn : q.2 ∉ tsupport eta := by
        rw [eta.tsupport_eq]
        intro hm
        have hb : |q.2| ≤ r / 2 := by
          simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, eta] using hm
        have ha := abs_le.mp hb
        exact hq ⟨by linarith, by linarith⟩
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
        (continuous_snd.tendsto q)
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hz] with z hz
      simp only [Function.comp_apply, Pi.zero_apply] at hz
      simp [B, hz]
  have hBs (p : ℝ) (_ : p ∈ K) (x : ℝ) (hx : r ≤ |x|) : B (p, x) = 0 := by
    have hz := eta.zero_of_le_dist
      (show eta.rOut ≤ dist x 0 by simpa only [Real.dist_eq, sub_zero] using heta.le.trans hx)
    simp [B, hz]
  obtain ⟨C, hC, hbound⟩ := exists_uniform_quadratic_fresnel_negative_remainder hB hK hr hBs
  refine ⟨C, hC, ?_⟩
  intro p hp lam hlam
  have hB0 : B (p, 0) = W p := by
    simp only [B, hj0, hjd, eta.one_of_mem_closedBall (Metric.mem_closedBall_self eta.rIn_pos.le),
      Complex.ofReal_one, one_mul, add_zero, mul_one]
  have hu : uIcc (-r) r = Icc (-r) r := uIcc_of_le (by linarith)
  have hcont : ContinuousOn j (uIcc (-r) r) := by
    rw [hu]
    exact fun w hw => (hj w hw).1.continuousAt.continuousWithinAt
  have hder : ∀ w ∈ Ioo (min (-r) r) (max (-r) r), HasDerivAt j (deriv j w) w := by
    intro w hw
    have hm : w ∈ uIcc (-r) r := ⟨hw.1.le, hw.2.le⟩
    exact (hj w (hu ▸ hm)).1.differentiableAt.hasDerivAt
  have hpos : ∀ w ∈ Ioo (min (-r) r) (max (-r) r), 0 ≤ deriv j w := by
    intro w hw
    have hm : w ∈ uIcc (-r) r := ⟨hw.1.le, hw.2.le⟩
    exact (hj w (hu ▸ hm)).2.1.le
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := fun v => (eta (logPhaseMorse v) : ℂ) * W (p * (1 + v)) *
      Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ))) hcont hder hpos
  have he : (∫ v in j (-r)..j r, (eta (logPhaseMorse v) : ℂ) * W (p * (1 + v)) *
      Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ))) =
        ∫ w : ℝ, B (p, w) * quadPhase (-lam) w := by
    rw [← hsub]
    have hpoint : (∫ w in (-r)..r, (deriv j w) •
        ((eta (logPhaseMorse (j w)) : ℂ) * W (p * (1 + j w)) *
          Complex.exp (Complex.I * ((lam * logPhaseProfile (j w) : ℝ) : ℂ)))) =
        ∫ w in (-r)..r, B (p, w) * quadPhase (-lam) w := by
      apply intervalIntegral.integral_congr
      intro w hw
      have hm := hj w (hu ▸ hw)
      simp only [hm.2.2.2.1, hm.2.2.2.2, B, quadPhase, Complex.real_smul]
      have hex : Complex.I * ((lam * (-(w ^ 2) / 2) : ℝ) : ℂ) =
          (((-lam * w ^ 2 / 2 : ℝ) : ℂ) * I) := by push_cast; ring
      rw [hex]
      ring
    simp only [Function.comp_apply]
    rw [hpoint, intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    have hb : r ≤ |w| := by
      by_contra hh
      have ha := abs_lt.mp (lt_of_not_ge hh)
      exact hw ⟨ha.1, ha.2.le⟩
    rw [hBs p hp w hb, zero_mul]
  rw [he, ← hB0]
  exact hbound p hp lam hlam

/-- A fixed physical height window, positive on its central interval and supported in [1,2]. -/
def bagPhysicalHeightWindow : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The physical height cutoff and every regularity input are supplied by the source.
The stationary constant is common to all saddle positions in the full ratio interval. -/
theorem exists_logPhaseMorse_source_height_window :
    ∃ (r C : ℝ) (j : ℝ → ℝ) (eta : ContDiffBump (0 : ℝ)),
      0 < r ∧ 0 < C ∧ eta.rOut < r ∧ j 0 = 0 ∧ deriv j 0 = 1 ∧
      (∀ w ∈ Icc (-r) r, AnalyticAt ℝ j w ∧ 0 < deriv j w ∧ -1 < j w ∧
        logPhaseMorse (j w) = w ∧ logPhaseProfile (j w) = -(w ^ 2) / 2) ∧
      ∀ p ∈ Icc (1 / 2 : ℝ) 4, ∀ lam : ℝ, 0 < lam →
        ‖(∫ v in j (-r)..j r, (eta (logPhaseMorse v) : ℂ) *
            (bagPhysicalHeightWindow (p * (1 + v)) : ℂ) *
            Complex.exp (Complex.I * ((lam * logPhaseProfile v : ℝ) : ℂ))) -
          (bagPhysicalHeightWindow p : ℂ) * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
            Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)‖ ≤
              C / (lam * Real.sqrt lam) := by
  obtain ⟨r, j, eta, hr, he, hj0, hjd, hj, hfamily⟩ :=
    exists_logPhaseMorse_physical_window_family
  obtain ⟨C, hC, hb⟩ := hfamily (fun x => (bagPhysicalHeightWindow x : ℂ))
    (Complex.ofRealCLM.contDiff.comp bagPhysicalHeightWindow.contDiff)
    (Icc (1 / 2 : ℝ) 4) isCompact_Icc
  exact ⟨r, C, j, eta, hr, hC, he, hj0, hjd, hj, hb⟩

end GaloisForLFunctions.RHTower
