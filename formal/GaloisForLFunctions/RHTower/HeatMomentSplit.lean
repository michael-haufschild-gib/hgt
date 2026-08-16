import GaloisForLFunctions.RHTower.HeatFullWindowMoment

/-!
# Two-sided moments of the heat multiplier

The Jonquière expansion has different leading coefficients on the two sides of the phase origin.
Because the heat multiplier is even and nonnegative, a two-sided power test averages the two
coefficients.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

/-- The heat multiplier as a nonnegative real number. -/
noncomputable def heatMultiplierValue (x θ : ℝ) : ℝ :=
  x ^ (-(1 : ℝ) / 2) * ∑' n : ℤ, heatGauss x n θ

theorem heatMultiplier_eq_value {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    heatMultiplier x θ = ((heatMultiplierValue x θ : ℝ) : ℂ) :=
  heatMultiplier_eq_ofReal hx θ

theorem heatMultiplierValue_nonneg {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    0 ≤ heatMultiplierValue x θ := by
  rw [heatMultiplierValue]
  refine mul_nonneg (Real.rpow_nonneg hx.le _) ?_
  exact tsum_nonneg fun n => (heatGauss_pos x n θ).le

theorem norm_heatMultiplier {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    ‖heatMultiplier x θ‖ = heatMultiplierValue x θ := by
  rw [heatMultiplier_eq_value hx, Complex.norm_real,
    Real.norm_of_nonneg (heatMultiplierValue_nonneg hx θ)]

/-- The two-sided power test is integrable on the window. -/
theorem integrableOn_halfSplit {x : ℝ} (hx : 0 < x) {lam : ℂ} (hlam : -1 < lam.re) (cp cm : ℂ) :
    IntegrableOn
      (fun θ : ℝ => ((if 0 < θ then cp else cm) * ((|θ| : ℝ) : ℂ) ^ lam) * heatMultiplier x θ)
      (Ioc (-Real.pi) Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hneg : IntegrableOn
      (fun θ : ℝ => ((if 0 < θ then cp else cm) * ((|θ| : ℝ) : ℂ) ^ lam) * heatMultiplier x θ)
      (Ioc (-Real.pi) 0) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (Integrable.const_mul (integrableOn_abs_cpow_mul_heatMultiplier_neg hlam hx) cm)
      (fun θ hθ => ?_) measurableSet_Ioc
    have hnot : ¬ (0 < θ) := by
      have := hθ.2
      linarith
    rw [if_neg hnot]
    ring
  have hpos : IntegrableOn
      (fun θ : ℝ => ((if 0 < θ then cp else cm) * ((|θ| : ℝ) : ℂ) ^ lam) * heatMultiplier x θ)
      (Ioc (0 : ℝ) Real.pi) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (Integrable.const_mul (integrableOn_cpow_mul_heatMultiplier hlam hx) cp)
      (fun θ hθ => ?_) measurableSet_Ioc
    have hθ0 : (0 : ℝ) < θ := hθ.1
    rw [if_pos hθ0, abs_of_pos hθ0]
    ring
  have hunion : Ioc (-Real.pi) 0 ∪ Ioc (0 : ℝ) Real.pi = Ioc (-Real.pi) Real.pi :=
    Set.Ioc_union_Ioc_eq_Ioc (by linarith) hpi.le
  rw [← hunion]
  exact hneg.union hpos

/-- **A two-sided power test averages the two coefficients.** -/
theorem heatMoment_halfSplit {x : ℝ} (hx : 0 < x) {lam : ℂ} (hlam : -1 < lam.re) (cp cm : ℂ) :
    (1 / (2 * (Real.pi : ℂ)))
      * (∫ θ in Ioc (-Real.pi) Real.pi,
          ((if 0 < θ then cp else cm) * ((|θ| : ℝ) : ℂ) ^ lam) * heatMultiplier x θ)
      = ((cp + cm) / 2) * heatMoment x lam := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hneg : IntegrableOn
      (fun θ : ℝ => ((if 0 < θ then cp else cm) * ((|θ| : ℝ) : ℂ) ^ lam) * heatMultiplier x θ)
      (Ioc (-Real.pi) 0) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (Integrable.const_mul (integrableOn_abs_cpow_mul_heatMultiplier_neg hlam hx) cm)
      (fun θ hθ => ?_) measurableSet_Ioc
    have hnot : ¬ (0 < θ) := by
      have := hθ.2
      linarith
    rw [if_neg hnot]
    ring
  have hpos : IntegrableOn
      (fun θ : ℝ => ((if 0 < θ then cp else cm) * ((|θ| : ℝ) : ℂ) ^ lam) * heatMultiplier x θ)
      (Ioc (0 : ℝ) Real.pi) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (Integrable.const_mul (integrableOn_cpow_mul_heatMultiplier hlam hx) cp)
      (fun θ hθ => ?_) measurableSet_Ioc
    have hθ0 : (0 : ℝ) < θ := hθ.1
    rw [if_pos hθ0, abs_of_pos hθ0]
    ring
  have hdisj : Disjoint (Ioc (-Real.pi) 0) (Ioc (0 : ℝ) Real.pi) := by
    rw [Set.disjoint_left]
    intro a ha ha'
    exact absurd ha'.1 (by simpa using ha.2)
  have hsplit := MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hneg hpos
  rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) hpi.le] at hsplit
  have hleft : (∫ θ in Ioc (-Real.pi) 0,
      ((if 0 < θ then cp else cm) * ((|θ| : ℝ) : ℂ) ^ lam) * heatMultiplier x θ)
      = cm * ∫ θ in Ioc (0 : ℝ) Real.pi, ((θ : ℝ) : ℂ) ^ lam * heatMultiplier x θ := by
    rw [← setIntegral_reflect_window (x := x) (lam := lam), ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
    have hnot : ¬ (0 < θ) := by
      have := hθ.2
      linarith
    rw [if_neg hnot]
    ring
  have hright : (∫ θ in Ioc (0 : ℝ) Real.pi,
      ((if 0 < θ then cp else cm) * ((|θ| : ℝ) : ℂ) ^ lam) * heatMultiplier x θ)
      = cp * ∫ θ in Ioc (0 : ℝ) Real.pi, ((θ : ℝ) : ℂ) ^ lam * heatMultiplier x θ := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
    have hθ0 : (0 : ℝ) < θ := hθ.1
    rw [if_pos hθ0, abs_of_pos hθ0]
    ring
  rw [hsplit, hleft, hright, heatMoment, integral_abs_cpow_mul_heatMultiplier_window hlam hx]
  have hpine : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
  field_simp
  ring

end RHTower
