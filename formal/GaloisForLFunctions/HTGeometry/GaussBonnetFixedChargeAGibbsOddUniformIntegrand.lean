import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddUniformKernel

/-!
# Uniform odd correction along every physical integration path

Uniformity of the force correction controls all angle parameters and
all points of their fixed integration paths simultaneously.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAGibbsOddLimitIntegrand_continuous (w φ ψ : ℝ) :
    Continuous (egbFixedChargeAGibbsOddLimitIntegrand w φ ψ) := by
  unfold egbFixedChargeAGibbsOddLimitIntegrand egbFixedChargeAGibbsOddLimitKernel egbFixedChargeAInteriorPathCoordinate
  fun_prop

theorem egbFixedChargeAGibbsOddIntegrand_uniform_critical_limit (w φ : ℝ) :
    TendstoUniformlyOn (fun τ (p : ℝ × ℝ) => egbFixedChargeAGibbsOddIntegrand w φ τ p.1 p.2)
      (fun p => egbFixedChargeAGibbsOddLimitIntegrand w φ p.1 p.2) atBot (univ ×ˢ Icc (0 : ℝ) 1) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have h := (Metric.tendstoUniformlyOn_iff.mp (egbFixedChargeAGibbsOddKernel_uniform_critical_limit w φ))
    (ε / 3) (by positivity)
  filter_upwards [h] with τ hτ
  intro p hp
  have hk := hτ (egbFixedChargeAInteriorPathCoordinate p.1 p.2)
    (egbFixedChargeAInteriorPathCoordinate_mapsTo p.1 hp.2)
  rw [Real.dist_eq] at hk ⊢
  have hs : |sin p.1 - 1| ≤ 2 := abs_le.mpr ⟨by linarith [neg_one_le_sin p.1], by linarith [sin_le_one p.1]⟩
  have he : egbFixedChargeAGibbsOddLimitIntegrand w φ p.1 p.2 - egbFixedChargeAGibbsOddIntegrand w φ τ p.1 p.2 =
      (sin p.1 - 1) * (egbFixedChargeAGibbsOddLimitKernel w φ (egbFixedChargeAInteriorPathCoordinate p.1 p.2) -
        egbFixedChargeAGibbsOddKernel w φ τ (egbFixedChargeAInteriorPathCoordinate p.1 p.2)) := by
    unfold egbFixedChargeAGibbsOddLimitIntegrand egbFixedChargeAGibbsOddIntegrand
    ring
  rw [he, abs_mul]
  calc
    _ ≤ 2 * (ε / 3) := mul_le_mul hs hk.le (abs_nonneg _) (by norm_num)
    _ < ε := by linarith

end GaloisForLFunctions.HTGeometry
