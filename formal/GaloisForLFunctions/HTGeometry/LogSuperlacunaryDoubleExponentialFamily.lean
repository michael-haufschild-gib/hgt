import GaloisForLFunctions.HTGeometry.LogSuperlacunaryMagnitudeHypertranscendence
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The phase-uniform double-exponential family

This module realizes the explicit family

`F θ z = ∑ n, exp (-2^(2^n)) * exp (i * θ n) * z^n`

as an entire function and applies the log-superlacunary magnitude theorem.  It also records that
the zero-phase Taylor coefficients all belong to the one-generator field `ℚ(exp(-1))`.
-/

open Filter PowerSeries
open scoped Topology ENNReal

namespace GaloisForLFunctions

noncomputable section

/-- The logarithmic magnitude scale `2^(2^n)`. -/
def doubleExponentialScale (n : ℕ) : ℝ := (2 : ℝ) ^ (2 ^ n)

theorem doubleExponentialScale_succ (n : ℕ) :
    doubleExponentialScale (n + 1) = doubleExponentialScale n ^ 2 := by
  rw [doubleExponentialScale, doubleExponentialScale, Nat.two_pow_succ, pow_add, pow_two]

theorem doubleExponentialScale_pos (n : ℕ) : 0 < doubleExponentialScale n := by
  exact pow_pos (by norm_num) _

theorem doubleExponentialScale_ge_two (n : ℕ) : 2 ≤ doubleExponentialScale n := by
  unfold doubleExponentialScale
  calc
    (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
    _ ≤ (2 : ℝ) ^ (2 ^ n) :=
      pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) Nat.one_le_two_pow

theorem doubleExponentialScale_tendsto :
    Tendsto doubleExponentialScale atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))

theorem doubleExponentialScale_ratio_tendsto :
    Tendsto (fun n => doubleExponentialScale (n + 1) / doubleExponentialScale n)
      atTop atTop := by
  convert doubleExponentialScale_tendsto using 1
  funext n
  rw [doubleExponentialScale_succ, pow_two]
  exact mul_div_cancel_left₀ (doubleExponentialScale n)
    (ne_of_gt (doubleExponentialScale_pos n))

theorem doubleExponentialScale_diff_tendsto :
    Tendsto (fun n => doubleExponentialScale (n + 1) - doubleExponentialScale n)
      atTop atTop := by
  refine Filter.tendsto_atTop_mono' atTop (Eventually.of_forall fun n => ?_)
    doubleExponentialScale_tendsto
  change doubleExponentialScale n ≤
    doubleExponentialScale (n + 1) - doubleExponentialScale n
  rw [doubleExponentialScale_succ]
  nlinarith [doubleExponentialScale_ge_two n]

/-- The `n`-th coefficient with arbitrary real phase. -/
def doubleExponentialPhaseCoeff (θ : ℕ → ℝ) (n : ℕ) : ℂ :=
  (Real.exp (-doubleExponentialScale n) : ℂ) *
    Complex.exp (Complex.I * (θ n : ℂ))

theorem norm_doubleExponentialPhaseCoeff (θ : ℕ → ℝ) (n : ℕ) :
    ‖doubleExponentialPhaseCoeff θ n‖ = Real.exp (-doubleExponentialScale n) := by
  simp [doubleExponentialPhaseCoeff, Complex.norm_exp]

theorem doubleExponentialPhaseCoeff_ne_zero (θ : ℕ → ℝ) (n : ℕ) :
    doubleExponentialPhaseCoeff θ n ≠ 0 := by
  simp [doubleExponentialPhaseCoeff, Complex.exp_ne_zero]

theorem doubleExponentialPhaseCoeff_ratio_tendsto (θ : ℕ → ℝ) :
    Tendsto (fun n => ‖doubleExponentialPhaseCoeff θ n.succ‖ /
      ‖doubleExponentialPhaseCoeff θ n‖) atTop (𝓝 0) := by
  have harg : Tendsto
      (fun n => -(doubleExponentialScale (n + 1) - doubleExponentialScale n))
      atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp doubleExponentialScale_diff_tendsto
  have hexp := Real.tendsto_exp_atBot.comp harg
  convert hexp using 1
  funext n
  rw [norm_doubleExponentialPhaseCoeff, norm_doubleExponentialPhaseCoeff,
    ← Real.exp_sub]
  congr 1
  ring

/-- A scalar power series of infinite radius is recovered exactly by the Taylor map. -/
theorem taylorPS_ofScalarsSum_of_radius_eq_top (c : ℕ → ℂ)
    (hr : (FormalMultilinearSeries.ofScalars ℂ c).radius = ⊤) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (FormalMultilinearSeries.ofScalarsSum c)) = c n := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have hiter := hp.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin n => (1 : ℂ))
  have hiter' : iteratedDeriv n p.sum 0 = (n.factorial : ℂ) * c n := by
    rw [iteratedDeriv_eq_iteratedFDeriv, hiter]
    simp [p, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  change PowerSeries.coeff n (taylorPS p.sum) = c n
  rw [coeff_taylorPS, hiter']
  exact mul_div_cancel_left₀ (c n) (by exact_mod_cast Nat.factorial_ne_zero n)

/-- The entire function with double-exponential magnitudes and phase sequence `θ`. -/
def doubleExponentialPhaseFunction (θ : ℕ → ℝ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (doubleExponentialPhaseCoeff θ)

theorem doubleExponentialPhaseFunction_eq_tsum (θ : ℕ → ℝ) (z : ℂ) :
    doubleExponentialPhaseFunction θ z =
      ∑' n, doubleExponentialPhaseCoeff θ n * z ^ n := by
  simpa [doubleExponentialPhaseFunction, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (doubleExponentialPhaseCoeff θ) z)

theorem doubleExponentialPhaseSeries_radius_eq_top (θ : ℕ → ℝ) :
    (FormalMultilinearSeries.ofScalars ℂ (doubleExponentialPhaseCoeff θ)).radius = ⊤ := by
  exact FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℂ
    (doubleExponentialPhaseCoeff θ)
    (Eventually.of_forall (doubleExponentialPhaseCoeff_ne_zero θ))
    (doubleExponentialPhaseCoeff_ratio_tendsto θ)

/-- Every member of the phase family is entire. -/
theorem contDiff_doubleExponentialPhaseFunction (θ : ℕ → ℝ) :
    ContDiff ℂ (⊤ : ℕ∞) (doubleExponentialPhaseFunction θ) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (doubleExponentialPhaseCoeff θ)
  have hr : p.radius = ⊤ := doubleExponentialPhaseSeries_radius_eq_top θ
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have ha : AnalyticOnNhd ℂ p.sum Set.univ := by
    simpa [hr] using hp.analyticOnNhd
  exact ha.contDiff

theorem taylorPS_doubleExponentialPhaseFunction (θ : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (doubleExponentialPhaseFunction θ)) =
      doubleExponentialPhaseCoeff θ n := by
  exact taylorPS_ofScalarsSum_of_radius_eq_top (doubleExponentialPhaseCoeff θ)
    (doubleExponentialPhaseSeries_radius_eq_top θ) n

theorem taylorPS_doubleExponentialPhaseFunction_coeff_ne_zero
    (θ : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (doubleExponentialPhaseFunction θ)) ≠ 0 := by
  rw [taylorPS_doubleExponentialPhaseFunction]
  exact doubleExponentialPhaseCoeff_ne_zero θ n

/-- Every arbitrary-phase double-exponential series is hypertranscendental. -/
theorem hypertranscendental_doubleExponentialPhaseFunction (θ : ℕ → ℝ) :
    Hypertranscendental (doubleExponentialPhaseFunction θ) := by
  apply hypertranscendental_of_eventually_logSuperlacunary
    (contDiff_doubleExponentialPhaseFunction θ) (b := doubleExponentialScale)
  · exact Eventually.of_forall fun n => by
      rw [taylorPS_doubleExponentialPhaseFunction, norm_doubleExponentialPhaseCoeff]
  · exact Eventually.of_forall doubleExponentialScale_pos
  · exact doubleExponentialScale_ratio_tendsto

/-- The coefficient field `ℚ(exp(-1))` inside `ℂ`. -/
def expMinusOneCoefficientField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({(Real.exp (-1) : ℂ)} : Set ℂ)

theorem exp_neg_doubleExponentialScale_eq_pow (n : ℕ) :
    Real.exp (-doubleExponentialScale n) =
      Real.exp (-1) ^ (2 ^ (2 ^ n)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  simp [doubleExponentialScale]

theorem doubleExponentialPhaseCoeff_zero_mem_expMinusOneCoefficientField (n : ℕ) :
    doubleExponentialPhaseCoeff (fun _ => 0) n ∈ expMinusOneCoefficientField := by
  have hbase : (Real.exp (-1) : ℂ) ∈ expMinusOneCoefficientField := by
    exact (IntermediateField.subset_adjoin ℚ ({(Real.exp (-1) : ℂ)} : Set ℂ))
      (Set.mem_singleton _)
  have hpow := (expMinusOneCoefficientField.toSubfield.pow_mem hbase (2 ^ (2 ^ n)))
  simpa [doubleExponentialPhaseCoeff, exp_neg_doubleExponentialScale_eq_pow] using hpow

/-- Every Taylor coefficient of the positive member lies in `ℚ(exp(-1))`. -/
theorem taylorPS_doubleExponentialPhaseFunction_zero_mem_expMinusOneCoefficientField (n : ℕ) :
    PowerSeries.coeff n (taylorPS (doubleExponentialPhaseFunction (fun _ => 0))) ∈
      expMinusOneCoefficientField := by
  rw [taylorPS_doubleExponentialPhaseFunction]
  exact doubleExponentialPhaseCoeff_zero_mem_expMinusOneCoefficientField n

end


end GaloisForLFunctions
