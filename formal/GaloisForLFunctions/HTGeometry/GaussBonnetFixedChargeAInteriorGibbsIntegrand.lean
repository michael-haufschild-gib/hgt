import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsPath
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsKernelDomination

/-!
# Integrands for the entire interior Gibbs profile

The full force bound supplies one dominating constant for all sine
endpoints simultaneously. No endpoint-dependent estimate is assumed.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAInteriorGibbsIntegrand (w φ τ ψ u : ℝ) : ℝ :=
  (sin ψ - 1) * egbFixedChargeAGibbsKernel w φ τ (egbFixedChargeAInteriorPathCoordinate ψ u)

def egbFixedChargeAInteriorGibbsLimitIntegrand (w φ ψ u : ℝ) : ℝ :=
  (sin ψ - 1) * (4 * egbFixedChargeAGibbsBarrierCoefficient w φ *
    (egbFixedChargeAInteriorPathCoordinate ψ u ^ 2 - 1) * egbFixedChargeAInteriorPathCoordinate ψ u)

theorem egbFixedChargeAInteriorGibbsIntegrand_critical_limit (w φ ψ u : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ u) atBot
      (𝓝 (egbFixedChargeAInteriorGibbsLimitIntegrand w φ ψ u)) := by
  exact (tendsto_const_nhds (x := sin ψ - 1)).mul
    (egbFixedChargeAGibbsKernel_critical_limit w φ (egbFixedChargeAInteriorPathCoordinate ψ u))

theorem egbFixedChargeAInteriorGibbsIntegrand_measurable (w φ τ ψ : ℝ) :
    Measurable (egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ) := by
  unfold egbFixedChargeAInteriorGibbsIntegrand egbFixedChargeAGibbsKernel
    egbFixedChargeABarrierPolynomial egbFixedChargeAInteriorPathCoordinate
  fun_prop

theorem egbFixedChargeAInteriorGibbsIntegrand_continuousOn (w φ τ ψ : ℝ) :
    ContinuousOn (egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ) (Icc (0 : ℝ) 1) := by
  unfold egbFixedChargeAInteriorGibbsIntegrand
  apply ContinuousOn.mul continuousOn_const
  apply (egbFixedChargeAGibbsKernel_continuousOn w φ τ).comp
  · unfold egbFixedChargeAInteriorPathCoordinate
    fun_prop
  · exact egbFixedChargeAInteriorPathCoordinate_mapsTo ψ

theorem egbFixedChargeAInteriorGibbsIntegrand_intervalIntegrable (w φ τ ψ : ℝ) :
    IntervalIntegrable (egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ) volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (egbFixedChargeAInteriorGibbsIntegrand_continuousOn w φ τ ψ)

theorem egbFixedChargeAInteriorGibbsIntegrand_dominated (w φ : ℝ) :
    ∀ᶠ τ in atBot, ∀ ψ : ℝ, ∀ u ∈ Icc (0 : ℝ) 1,
      |egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ u| ≤ 20 * (egbFixedChargeACriticalRadius w φ + 1) := by
  filter_upwards [egbFixedChargeAGibbsKernel_dominated w φ] with τ hτ
  intro ψ u hu
  have hkernel := hτ (egbFixedChargeAInteriorPathCoordinate ψ u) (egbFixedChargeAInteriorPathCoordinate_mapsTo ψ hu)
  have hs : |sin ψ - 1| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith [neg_one_le_sin ψ, sin_le_one ψ]
  unfold egbFixedChargeAInteriorGibbsIntegrand
  rw [abs_mul]
  calc
    _ ≤ 2 * (10 * (egbFixedChargeACriticalRadius w φ + 1)) :=
      mul_le_mul hs hkernel (abs_nonneg _) (by norm_num)
    _ = _ := by ring

end GaloisForLFunctions.HTGeometry
