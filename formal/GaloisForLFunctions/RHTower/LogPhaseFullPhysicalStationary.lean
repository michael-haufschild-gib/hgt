import GaloisForLFunctions.RHTower.LogPhaseNonstationaryFamily

/-!
# Complete physical-window logarithmic stationary formula

The source-defined physical height window has its full Fresnel main uniformly
across saddle positions. Exact interval support and Morse monotonicity identify
the localized term; the entire complementary integral is retained and charged.
No saddle-dependent cutoff replaces the fixed physical window in the capstone.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff
namespace GaloisForLFunctions.RHTower

private theorem full_interval_eq {f : ℝ → ℂ}
    (hf : ∀ v : ℝ, v ∉ Icc (-(3 / 4 : ℝ)) 3 → f v = 0) :
    (∫ v in (-(7 / 8 : ℝ))..(25 / 8 : ℝ), f v) = ∫ v : ℝ, f v := by
  rw [intervalIntegral.integral_of_le (by norm_num : -(7 / 8 : ℝ) ≤ 25 / 8)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  apply hf v
  intro hm
  apply hv
  constructor <;> linarith [hm.1, hm.2]

private theorem physical_window_integral_split (eta : ContDiffBump (0 : ℝ))
    {p : ℝ} (hp : p ∈ Icc (1 / 2 : ℝ) 4) (lam : ℝ) :
    (∫ v : ℝ, (bagPhysicalHeightWindow (p * (1 + v)) : ℂ) *
      Complex.exp (I * ((lam * logPhaseProfile v : ℝ) : ℂ))) =
      (∫ v : ℝ, (eta (logPhaseMorse v) : ℂ) *
        (bagPhysicalHeightWindow (p * (1 + v)) : ℂ) *
        Complex.exp (I * ((lam * logPhaseProfile v : ℝ) : ℂ))) +
      ∫ v : ℝ, (1 - (eta (logPhaseMorse v) : ℂ)) *
        (bagPhysicalHeightWindow (p * (1 + v)) : ℂ) *
        Complex.exp (I * ((lam * logPhaseProfile v : ℝ) : ℂ)) := by
  let W : ℝ → ℂ := fun v => (bagPhysicalHeightWindow (p * (1 + v)) : ℂ)
  let E : ℝ → ℂ := fun v => Complex.exp (I * ((lam * logPhaseProfile v : ℝ) : ℂ))
  let H : ℝ → ℂ := fun v => (eta (logPhaseMorse v) : ℂ)
  have hW : Continuous W := Complex.continuous_ofReal.comp
    (bagPhysicalHeightWindow.continuous.comp
      (continuous_const.mul (continuous_const.add continuous_id)))
  have hpsi : ContinuousOn logPhaseProfile (Icc (-(7 / 8 : ℝ)) (25 / 8)) :=
    fun v hv => (hasDerivAt_logPhaseProfile (by linarith [hv.1])).continuousAt.continuousWithinAt
  have hE : ContinuousOn E (Icc (-(7 / 8 : ℝ)) (25 / 8)) :=
    Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hpsi)))
  have hH : ContinuousOn H (Icc (-(7 / 8 : ℝ)) (25 / 8)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (eta.continuous.comp_continuousOn (fun v hv =>
        (contDiffAt_logPhaseMorse (by linarith [hv.1])).continuousAt.continuousWithinAt))
  have hloc : IntervalIntegrable (fun v => H v * W v * E v) volume (-(7 / 8 : ℝ)) (25 / 8) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : -(7 / 8 : ℝ) ≤ 25 / 8)]
    exact (hH.mul hW.continuousOn).mul hE
  have hrem : IntervalIntegrable (fun v => (1 - H v) * W v * E v) volume
      (-(7 / 8 : ℝ)) (25 / 8) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : -(7 / 8 : ℝ) ≤ 25 / 8)]
    exact ((continuousOn_const.sub hH).mul hW.continuousOn).mul hE
  have hzero (v : ℝ) (hv : v ∉ Icc (-(3 / 4 : ℝ)) 3) : W v = 0 := by
    simp only [W, bagPhysicalHeightWindow_scaled_eq_zero hp hv, Complex.ofReal_zero]
  have hf := full_interval_eq (f := fun v => W v * E v) (fun v hv => by rw [hzero v hv, zero_mul])
  have hl := full_interval_eq (f := fun v => H v * W v * E v)
    (fun v hv => by rw [hzero v hv, mul_zero, zero_mul])
  have hr := full_interval_eq (f := fun v => (1 - H v) * W v * E v)
    (fun v hv => by rw [hzero v hv, mul_zero, zero_mul])
  have hi := intervalIntegral.integral_add hloc hrem
  have heq : (fun v => H v * W v * E v + (1 - H v) * W v * E v) =
      fun v => W v * E v := by funext v; ring
  rw [heq, hf, hl, hr] at hi
  exact hi

private theorem physical_window_local_integral {r : ℝ} (hr : 0 < r)
    {j : ℝ → ℝ} {eta : ContDiffBump (0 : ℝ)} (heta : eta.rOut < r)
    (hdomL : -1 < j (-r)) (hdomR : -1 < j r)
    (hwL : logPhaseMorse (j (-r)) = -r) (hwR : logPhaseMorse (j r) = r)
    {p : ℝ} (hp : p ∈ Icc (1 / 2 : ℝ) 4) (lam : ℝ) :
    (∫ v in j (-r)..j r, (eta (logPhaseMorse v) : ℂ) *
        (bagPhysicalHeightWindow (p * (1 + v)) : ℂ) *
        Complex.exp (I * ((lam * logPhaseProfile v : ℝ) : ℂ))) =
      ∫ v : ℝ, (eta (logPhaseMorse v) : ℂ) *
        (bagPhysicalHeightWindow (p * (1 + v)) : ℂ) *
        Complex.exp (I * ((lam * logPhaseProfile v : ℝ) : ℂ)) := by
  have horder : j (-r) ≤ j r := by
    by_contra hh
    have hm := strictMonoOn_logPhaseMorse hdomR hdomL (lt_of_not_ge hh)
    rw [hwR, hwL] at hm
    linarith
  rw [intervalIntegral.integral_of_le horder]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  by_cases hvdom : -1 < v
  · have he : eta (logPhaseMorse v) = 0 := by
      apply eta.zero_of_le_dist
      rw [Real.dist_eq, sub_zero]
      by_cases hvL : v ≤ j (-r)
      · have hh := strictMonoOn_logPhaseMorse.monotoneOn hvdom hdomL hvL
        rw [hwL] at hh
        linarith [neg_le_abs (logPhaseMorse v)]
      · have hvR : j r < v := by
          by_contra hh
          exact hv ⟨lt_of_not_ge hvL, le_of_not_gt hh⟩
        have hh := strictMonoOn_logPhaseMorse.monotoneOn hdomR hvdom hvR.le
        rw [hwR] at hh
        linarith [le_abs_self (logPhaseMorse v)]
    simp only [he, Complex.ofReal_zero, zero_mul]
  · have hz := bagPhysicalHeightWindow_scaled_eq_zero hp (show v ∉ Icc (-(3 / 4 : ℝ)) 3 by
      intro hh
      linarith [le_of_not_gt hvdom, hh.1])
    simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul]

/-- The complete source physical window has a uniform oriented Fresnel main.
The local saddle, both physical cutoff transitions, and the entire complement remain present. -/
theorem exists_full_physical_logPhase_stationary :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Icc (1 / 2 : ℝ) 4, ∀ lam : ℝ, 1 ≤ lam →
      ‖(∫ v : ℝ, (bagPhysicalHeightWindow (p * (1 + v)) : ℂ) *
          Complex.exp (I * ((lam * logPhaseProfile v : ℝ) : ℂ))) -
        (bagPhysicalHeightWindow p : ℂ) * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
          Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)‖ ≤
            C / (lam * Real.sqrt lam) := by
  obtain ⟨r, Cj, j, eta, hr, hCj, heta, hj0, hjd, hj, hlocal⟩ :=
    exists_logPhaseMorse_source_height_window
  obtain ⟨Cc, hCc, hcomp⟩ := exists_logPhaseMorse_source_window_complement eta
  refine ⟨Cj + Cc, by positivity, ?_⟩
  intro p hp lam hlam
  have hlam0 : 0 < lam := by linarith
  have hleft := hj (-r) ⟨le_rfl, by linarith⟩
  have hright := hj r ⟨by linarith, le_rfl⟩
  have hl := physical_window_local_integral hr heta hleft.2.2.1 hright.2.2.1
    hleft.2.2.2.1 hright.2.2.2.1 hp lam
  have hb := hlocal p hp lam hlam0
  rw [hl] at hb
  rw [physical_window_integral_split eta hp lam]
  have htriangle : ∀ z w main : ℂ, ‖z + w - main‖ ≤ ‖z - main‖ + ‖w‖ := by
    intro z w main
    calc
      _ = ‖(z - main) + w‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  apply (htriangle _ _ _).trans
  apply (add_le_add hb (hcomp p hp lam hlam0)).trans
  have hsqrt : Real.sqrt lam ≤ lam := Real.sqrt_le_self_iff.mpr (Or.inr hlam)
  have hden : lam * Real.sqrt lam ≤ lam ^ 2 := by nlinarith
  calc
    Cj / (lam * Real.sqrt lam) + Cc / lam ^ 2 ≤
        Cj / (lam * Real.sqrt lam) + Cc / (lam * Real.sqrt lam) :=
      add_le_add le_rfl (div_le_div_of_nonneg_left hCc.le (by positivity) hden)
    _ = _ := by ring

end GaloisForLFunctions.RHTower
