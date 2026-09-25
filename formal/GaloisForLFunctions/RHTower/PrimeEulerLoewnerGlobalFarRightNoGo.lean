import GaloisForLFunctions.RHTower.EulerNormalizedTraceHankelFarRight
import GaloisForLFunctions.RHTower.PrimeEulerLoewnerLocalNoGo
import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg

/-!
# Far-right indefiniteness of the actual prime-only source cup

The von Mangoldt L-series on the absolute-Euler ray defines a real divided-difference
kernel. Its removable diagonal is the first logarithmic von Mangoldt moment, proved here
by differentiating that same L-series. The existing first-prime asymptotic shows that the
adjacent two-node determinant, scaled by `4^x`, tends to a strictly negative constant.
Thus the **infinite** prime source itself is not a positive Gram kernel on every far-right
ray packet. This rules out a prime-only positivity producer; it says nothing negative about
the completed prime--polar--Gamma kernel, whose missing cancellation remains RH-bearing.
-/

open Filter Topology LSeries

namespace RHTower

noncomputable section

/-- The confluence value is the derivative of the same source series used off diagonal. -/
theorem hasDerivAt_vonMangoldtLogMoment_zero {x : ℝ} (hx : 1 < x) :
    HasDerivAt (vonMangoldtLogMoment 0) (-vonMangoldtLogMoment 1 x) x := by
  have habs : abscissaOfAbsConv (vonMangoldtLogCoeff 0) < (x : ℂ).re := by
    simpa [vonMangoldtLogCoeff] using
      (lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hx))
  have hc : HasDerivAt (LSeries (vonMangoldtLogCoeff 0))
      (-LSeries (vonMangoldtLogCoeff 1) (x : ℂ)) (x : ℂ) := by
    simpa [vonMangoldtLogCoeff, Function.iterate_succ_apply'] using
      (LSeries_hasDerivAt habs)
  have hpath : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have hr : HasDerivAt
      (fun r : ℝ => (LSeries (vonMangoldtLogCoeff 0) (r : ℂ)).re)
      (-(LSeries (vonMangoldtLogCoeff 1) (x : ℂ)).re) x := by
    simpa only [Function.comp_def, Complex.reCLM_apply, mul_one, Complex.neg_re] using
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hc.comp x hpath))
  exact hr

private theorem tendsto_scaled_vonMangoldtLogMoment_shift (m : ℕ) :
    Tendsto (fun x : ℝ => (2 : ℝ) ^ x * vonMangoldtLogMoment m (x + 1))
      atTop (nhds ((Real.log 2) ^ (m + 1) / 2)) := by
  have hshift : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have h := (tendsto_scaled_vonMangoldtLogMoment m).comp hshift |>.div_const 2
  convert h using 1
  · funext x
    simp only [Function.comp_apply]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
    ring

/-- Adjacent two-node determinant of the prime-only divided-difference kernel. -/
def vonMangoldtPrimeAdjacentLoewnerDet (x : ℝ) : ℝ :=
  vonMangoldtLogMoment 1 x * vonMangoldtLogMoment 1 (x + 1) -
    (vonMangoldtLogMoment 0 x - vonMangoldtLogMoment 0 (x + 1)) ^ (2 : ℕ)

/-- Real source cup from the actual infinite von Mangoldt L-series, with removable diagonal. -/
noncomputable def vonMangoldtPrimeRayLoewnerKernel (x y : ℝ) : ℝ :=
  if x = y then vonMangoldtLogMoment 1 x
  else (vonMangoldtLogMoment 0 y - vonMangoldtLogMoment 0 x) / (x - y)

theorem vonMangoldtPrimeRayLoewnerKernel_diagonal_eq_neg_deriv
    {x : ℝ} (hx : 1 < x) :
    vonMangoldtPrimeRayLoewnerKernel x x =
      -deriv (vonMangoldtLogMoment 0) x := by
  simp only [vonMangoldtPrimeRayLoewnerKernel, ite_true]
  rw [(hasDerivAt_vonMangoldtLogMoment_zero hx).deriv]
  ring

theorem vonMangoldtPrimeRayLoewnerKernel_adjacent_det (x : ℝ) :
    vonMangoldtPrimeRayLoewnerKernel x x *
        vonMangoldtPrimeRayLoewnerKernel (x + 1) (x + 1) -
      vonMangoldtPrimeRayLoewnerKernel x (x + 1) *
        vonMangoldtPrimeRayLoewnerKernel (x + 1) x =
      vonMangoldtPrimeAdjacentLoewnerDet x := by
  have hne : x ≠ x + 1 := by linarith
  have hne' : x + 1 ≠ x := Ne.symm hne
  simp only [vonMangoldtPrimeRayLoewnerKernel, if_neg hne, if_neg hne', ite_true]
  unfold vonMangoldtPrimeAdjacentLoewnerDet
  ring

/-- The first prime controls the projective far-right determinant limit. -/
theorem tendsto_scaled_vonMangoldtPrimeAdjacentLoewnerDet :
    Tendsto
      (fun x : ℝ => ((2 : ℝ) ^ x) ^ (2 : ℕ) *
        vonMangoldtPrimeAdjacentLoewnerDet x)
      atTop
      (nhds (((Real.log 2) ^ (2 : ℕ)) * ((Real.log 2) ^ (2 : ℕ) / 2) -
        ((Real.log 2) - (Real.log 2) / 2) ^ (2 : ℕ))) := by
  have h0 := tendsto_scaled_vonMangoldtLogMoment 0
  have h0s := tendsto_scaled_vonMangoldtLogMoment_shift 0
  have h1 := tendsto_scaled_vonMangoldtLogMoment 1
  have h1s := tendsto_scaled_vonMangoldtLogMoment_shift 1
  have h := h1.mul h1s |>.sub ((h0.sub h0s).pow 2)
  convert h using 1
  · funext x
    rw [vonMangoldtPrimeAdjacentLoewnerDet]
    ring
  · ring

private theorem two_mul_log_two_sq_lt_one :
    2 * (Real.log 2) ^ (2 : ℕ) < 1 := by
  have ht : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := exp_gap_sq_gt (Real.log 2) 0 1 ht (by norm_num)
  norm_num [Real.exp_log] at h
  nlinarith

/-- The actual prime-only determinant is eventually strictly negative. -/
theorem vonMangoldtPrimeAdjacentLoewnerDet_eventually_neg :
    ∀ᶠ x : ℝ in atTop, vonMangoldtPrimeAdjacentLoewnerDet x < 0 := by
  have ht : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlimneg :
      (Real.log 2) ^ (2 : ℕ) * ((Real.log 2) ^ (2 : ℕ) / 2) -
        ((Real.log 2) - (Real.log 2) / 2) ^ (2 : ℕ) < 0 := by
    have hfactor :
        (Real.log 2) ^ (2 : ℕ) * ((Real.log 2) ^ (2 : ℕ) / 2) -
          ((Real.log 2) - (Real.log 2) / 2) ^ (2 : ℕ) =
        ((Real.log 2) ^ (2 : ℕ) / 4) *
          (2 * (Real.log 2) ^ (2 : ℕ) - 1) := by ring
    rw [hfactor]
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith [two_mul_log_two_sq_lt_one])
  have hev := tendsto_scaled_vonMangoldtPrimeAdjacentLoewnerDet.eventually
    (Iio_mem_nhds hlimneg)
  filter_upwards [hev] with x hx
  have hscale : 0 < ((2 : ℝ) ^ x) ^ (2 : ℕ) := by positivity
  nlinarith

/-- The literal infinite prime-only source kernel fails the two-node Gram sign far right. -/
theorem vonMangoldtPrimeRayLoewnerKernel_adjacent_eventually_negative_determinant :
    ∀ᶠ x : ℝ in atTop,
      vonMangoldtPrimeRayLoewnerKernel x x *
          vonMangoldtPrimeRayLoewnerKernel (x + 1) (x + 1) <
        vonMangoldtPrimeRayLoewnerKernel x (x + 1) *
          vonMangoldtPrimeRayLoewnerKernel (x + 1) x := by
  filter_upwards [vonMangoldtPrimeAdjacentLoewnerDet_eventually_neg] with x hx
  rw [← vonMangoldtPrimeRayLoewnerKernel_adjacent_det] at hx
  linarith

end

end RHTower
