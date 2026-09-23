import GaloisForLFunctions.HTGeometry.FokasLenellsRawReverseCubic

/-!
# A second nonsingular phase remainder

One further compact-interval average factors the difference between the
first phase average and one. The identity is exact at every frequency,
including zero, and its bound requires no division by the frequency.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawSecondPhaseAverage (r x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (t : ℂ)*rawPhaseAverage r (t*x)

theorem continuous_rawSecondPhaseAverage_parameters :
    Continuous (fun p : ℝ × ℝ => rawSecondPhaseAverage p.1 p.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hp : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1,p.2*p.1.2)) := by fun_prop
  have hh := continuous_rawPhaseAverage_parameters.comp hp
  change Continuous (fun p : (ℝ × ℝ) × ℝ => (p.2 : ℂ)*rawPhaseAverage p.1.1 (p.2*p.1.2))
  exact (Complex.continuous_ofReal.comp continuous_snd).mul hh

theorem rawSecondPhaseAverage_bound (r x : ℝ) : ‖rawSecondPhaseAverage r x‖ ≤ 1 := by
  have hb (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
      ‖(t : ℂ)*rawPhaseAverage r (t*x)‖ ≤ 1 := by
    have ht' : 0 < t ∧ t ≤ 1 := by simpa only [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num),Set.mem_Ioc] using ht
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (rawPhaseAverage_bound r (t*x)) (abs_nonneg t)).trans
      (by simpa only [mul_one,abs_of_nonneg ht'.1.le] using ht'.2)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := 1) hb
  simpa only [rawSecondPhaseAverage,sub_zero,abs_one,mul_one] using hh

/-- Exact second divided difference of the original oscillatory phase. -/
theorem rawPhaseAverage_sub_one_factor (r x : ℝ) :
    rawPhaseAverage r x-1 = (-I*(r : ℂ)*(x : ℂ))*rawSecondPhaseAverage r x := by
  have hc : Continuous (fun t : ℝ => FDNLS.staggerPhase r (t*x)) := by
    unfold FDNLS.staggerPhase
    fun_prop
  have he : (fun t : ℝ => FDNLS.staggerPhase r (t*x)-1) =
      fun t : ℝ => (-I*(r : ℂ)*(x : ℂ))*((t : ℂ)*rawPhaseAverage r (t*x)) := by
    funext t
    rw [staggerPhase_sub_one_factor]
    push_cast
    ring
  have hi := intervalIntegral.integral_sub (μ := volume) (hc.intervalIntegrable 0 1)
    (intervalIntegrable_const (μ := volume) (a := (0 : ℝ)) (b := 1) (c := (1 : ℂ)))
  rw [he,intervalIntegral.integral_const_mul] at hi
  simpa only [rawPhaseAverage,rawSecondPhaseAverage,intervalIntegral.integral_const,
    sub_zero,one_smul] using hi.symm

theorem rawPhaseAverage_square_sub_one_factor (k x : ℝ) :
    rawPhaseAverage (2*k^(2 : ℕ)) x-1 =
      (k : ℂ)^(2 : ℕ)*(-2*I*(x : ℂ))*rawSecondPhaseAverage (2*k^(2 : ℕ)) x := by
  rw [rawPhaseAverage_sub_one_factor]
  push_cast
  ring

theorem rawPhaseAverage_neg_square_sub_one_factor (k x : ℝ) :
    rawPhaseAverage (-(2*k^(2 : ℕ))) x-1 =
      (k : ℂ)^(2 : ℕ)*(2*I*(x : ℂ))*rawSecondPhaseAverage (-(2*k^(2 : ℕ))) x := by
  rw [rawPhaseAverage_sub_one_factor]
  push_cast
  ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
