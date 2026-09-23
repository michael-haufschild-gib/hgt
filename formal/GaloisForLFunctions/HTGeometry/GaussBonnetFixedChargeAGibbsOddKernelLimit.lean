import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddDecomposition

/-!
# The first odd correction to the full Gibbs force

The exact decomposition has a quartic polynomial limit. Its coefficient
is negative and is tied exactly to the independently proved displacement
of the intermediate maximum.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAGibbsOddCoefficient (w φ : ℝ) : ℝ :=
  egbFixedChargeACriticalRadius w φ * egbFixedChargeAMeanGibbsForceCoefficient φ

def egbFixedChargeAGibbsOddLimitKernel (w φ t : ℝ) : ℝ :=
  egbFixedChargeAGibbsOddCoefficient w φ * (t ^ (2 : ℕ) - 1) * (5 * t ^ (2 : ℕ) - 1)

theorem egbFixedChargeAGibbsOddCoefficient_neg (w φ : ℝ) : egbFixedChargeAGibbsOddCoefficient w φ < 0 :=
  mul_neg_of_pos_of_neg (egbFixedChargeACriticalRadius_pos w φ) (egbFixedChargeAMeanGibbsForceCoefficient_neg φ)

theorem egbFixedChargeAGibbsOddCoefficient_peak_displacement (w φ : ℝ) :
    egbFixedChargeAGibbsOddCoefficient w φ / (4 * egbFixedChargeAGibbsBarrierCoefficient w φ) = egbFixedChargeAMiddleMeanCorrection φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  unfold egbFixedChargeAGibbsOddCoefficient egbFixedChargeAMeanGibbsForceCoefficient
    egbFixedChargeAGibbsBarrierCoefficient egbFixedChargeAMiddleMeanCorrection
  field_simp <;> ring

theorem egbFixedChargeAGibbsOddKernel_critical_limit (w φ t : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsOddKernel w φ τ t) atBot (𝓝 (egbFixedChargeAGibbsOddLimitKernel w φ t)) := by
  have he := egbFixedChargeAGibbsReciprocal_critical_limit t
  have ht : Tendsto (fun _ : ℝ => t) atBot (𝓝 t) := tendsto_const_nhds
  have hA : Tendsto (fun _ : ℝ => egbFixedChargeAGibbsCriticalPrefactor w φ) atBot (𝓝 (egbFixedChargeAGibbsCriticalPrefactor w φ)) := tendsto_const_nhds
  have h1 := (((egbFixedChargeAGibbsPrefactor_linear_limit w φ).mul he).mul (egbFixedChargeAGibbsLinear_critical_limit φ)).mul ht
  have h2 := ((hA.mul (egbFixedChargeAGibbsLinear_linear_limit φ)).mul he).mul ht
  have h3 := (tendsto_const_nhds (x := egbFixedChargeAGibbsCriticalPrefactor w φ *
    (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) * t)).mul (egbFixedChargeAGibbsReciprocal_linear_limit t)
  have h4 := ((egbFixedChargeAGibbsPrefactor_critical_limit w φ).mul he).mul
    (((egbFixedChargeAMeanPressureNumerator_critical_limit φ).mul (tendsto_const_nhds (x := t ^ (2 : ℕ)))).add
      (egbFixedChargeAGibbsResidual_critical_limit φ))
  have h := (tendsto_const_nhds (x := t ^ (2 : ℕ) - 1)).mul (((h1.add h2).add h3).add h4)
  simp only [mul_zero, zero_mul, zero_add, mul_one] at h
  have hlimit : (t ^ (2 : ℕ) - 1) * (egbFixedChargeAGibbsCriticalPrefactor w φ *
      (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) * t * (-2 * t) +
      egbFixedChargeAGibbsCriticalPrefactor w φ * ((3 - 2 * egbFixedChargeACriticalCouplingWeight φ) * t ^ (2 : ℕ) +
        (1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5))) = egbFixedChargeAGibbsOddLimitKernel w φ t := by
    calc
      _ = (egbFixedChargeAGibbsCriticalPrefactor w φ * (1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5)) *
        (t ^ (2 : ℕ) - 1) * (1 - 5 * t ^ (2 : ℕ)) := by ring
      _ = _ := by
        rw [egbFixedChargeAGibbsCriticalPrefactor_residual_product]
        unfold egbFixedChargeAGibbsOddLimitKernel egbFixedChargeAGibbsOddCoefficient
        ring
  rw [hlimit] at h
  simp only [egbFixedChargeAGibbsOddKernel_decomposition]
  exact h

theorem egbFixedChargeAGibbsOddKernel_measurable (w φ τ : ℝ) : Measurable (egbFixedChargeAGibbsOddKernel w φ τ) := by
  unfold egbFixedChargeAGibbsOddKernel egbFixedChargeAGibbsKernel egbFixedChargeAGibbsLeadingKernel egbFixedChargeABarrierPolynomial
  fun_prop

theorem egbFixedChargeAGibbsOddKernel_continuousOn (w φ τ : ℝ) :
    ContinuousOn (egbFixedChargeAGibbsOddKernel w φ τ) (Icc (-1 : ℝ) 1) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAGibbsOddKernel
  apply ContinuousOn.div
  · apply ContinuousOn.sub (egbFixedChargeAGibbsKernel_continuousOn w φ τ)
    unfold egbFixedChargeAGibbsLeadingKernel
    fun_prop
  · exact continuousOn_const
  · intro t ht
    exact hd.ne'

end GaloisForLFunctions.HTGeometry
