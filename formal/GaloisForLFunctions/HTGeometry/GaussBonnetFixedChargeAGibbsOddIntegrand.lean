import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddDomination
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsIntegrand

/-!
# Integrands for the first asymmetric energy correction

The fixed positive paths from the large phase preserve the uniform force
bound. Their divided integrand differences converge to the derivative of
an odd quintic polynomial in the scaled radius coordinate.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAGibbsOddIntegrand (w φ τ ψ u : ℝ) : ℝ :=
  (sin ψ - 1) * egbFixedChargeAGibbsOddKernel w φ τ (egbFixedChargeAInteriorPathCoordinate ψ u)
def egbFixedChargeAGibbsOddLimitIntegrand (w φ ψ u : ℝ) : ℝ :=
  (sin ψ - 1) * egbFixedChargeAGibbsOddLimitKernel w φ (egbFixedChargeAInteriorPathCoordinate ψ u)

theorem egbFixedChargeAGibbsOddIntegrand_critical_limit (w φ ψ u : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsOddIntegrand w φ τ ψ u) atBot
      (𝓝 (egbFixedChargeAGibbsOddLimitIntegrand w φ ψ u)) := by
  exact (tendsto_const_nhds (x := sin ψ - 1)).mul
    (egbFixedChargeAGibbsOddKernel_critical_limit w φ (egbFixedChargeAInteriorPathCoordinate ψ u))

theorem egbFixedChargeAGibbsOddIntegrand_measurable (w φ τ ψ : ℝ) : Measurable (egbFixedChargeAGibbsOddIntegrand w φ τ ψ) := by
  unfold egbFixedChargeAGibbsOddIntegrand egbFixedChargeAGibbsOddKernel egbFixedChargeAGibbsKernel
    egbFixedChargeAGibbsLeadingKernel egbFixedChargeABarrierPolynomial egbFixedChargeAInteriorPathCoordinate
  fun_prop

theorem egbFixedChargeAGibbsOddIntegrand_continuousOn (w φ τ ψ : ℝ) :
    ContinuousOn (egbFixedChargeAGibbsOddIntegrand w φ τ ψ) (Icc (0 : ℝ) 1) := by
  unfold egbFixedChargeAGibbsOddIntegrand
  apply ContinuousOn.mul continuousOn_const
  apply (egbFixedChargeAGibbsOddKernel_continuousOn w φ τ).comp
  · unfold egbFixedChargeAInteriorPathCoordinate
    fun_prop
  · exact egbFixedChargeAInteriorPathCoordinate_mapsTo ψ

theorem egbFixedChargeAGibbsOddIntegrand_intervalIntegrable (w φ τ ψ : ℝ) :
    IntervalIntegrable (egbFixedChargeAGibbsOddIntegrand w φ τ ψ) volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (egbFixedChargeAGibbsOddIntegrand_continuousOn w φ τ ψ)

theorem egbFixedChargeAGibbsOddIntegrand_dominated (w φ : ℝ) :
    ∀ᶠ τ in atBot, ∀ ψ : ℝ, ∀ u ∈ Icc (0 : ℝ) 1,
      |egbFixedChargeAGibbsOddIntegrand w φ τ ψ u| ≤ 160 * (egbFixedChargeAGibbsCriticalPrefactor w φ + 1) := by
  filter_upwards [egbFixedChargeAGibbsOddKernel_dominated w φ] with τ hτ
  intro ψ u hu
  have hk := hτ (egbFixedChargeAInteriorPathCoordinate ψ u) (egbFixedChargeAInteriorPathCoordinate_mapsTo ψ hu)
  have hs : |sin ψ - 1| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith [neg_one_le_sin ψ, sin_le_one ψ]
  unfold egbFixedChargeAGibbsOddIntegrand
  rw [abs_mul]
  calc
    _ ≤ 2 * (80 * (egbFixedChargeAGibbsCriticalPrefactor w φ + 1)) := mul_le_mul hs hk (abs_nonneg _) (by norm_num)
    _ = _ := by ring

theorem egbFixedChargeAGibbsOddIntegrand_difference (w φ τ ψ u : ℝ) :
    egbFixedChargeAGibbsOddIntegrand w φ τ ψ u =
      (egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ u - egbFixedChargeAInteriorGibbsLimitIntegrand w φ ψ u) /
        egbCoexistenceASymmetricRatio τ := by
  unfold egbFixedChargeAGibbsOddIntegrand egbFixedChargeAGibbsOddKernel egbFixedChargeAGibbsLeadingKernel
    egbFixedChargeAInteriorGibbsIntegrand egbFixedChargeAInteriorGibbsLimitIntegrand
  ring

end GaloisForLFunctions.HTGeometry
