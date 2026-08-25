import GaloisForLFunctions.HTGeometry.SmirnovBoundaryQuotient
import GaloisForLFunctions.Bottcher.AnalyticDomain

open Complex MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A nonzero element of the Smirnov Toeplitz kernel with real-line boundary symbol `U`.
Both analytic sides are represented by exact Smirnov quotients, and the defining reflected
boundary identity is imposed almost everywhere. -/
structure SmirnovToeplitzKernelElement (U : ℝ → ℂ) where
  forward : DiskSmirnovBoundary
  reflected : DiskSmirnovBoundary
  boundary_relation : reflected.boundary =ᵐ[volume] fun x =>
    (starRingEnd ℂ) (U x) * (starRingEnd ℂ) (forward.boundary x)
  forward_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, forward.numerator.fn z ≠ 0

/-- Pointwise product of two Toeplitz symbols. -/
def smirnovToeplitzSymbolMul (U V : ℝ → ℂ) (x : ℝ) : ℂ := U x * V x

/-- Toeplitz kernels multiply inside the Smirnov boundary algebra. -/
def SmirnovToeplitzKernelElement.mul {U V : ℝ → ℂ}
    (F : SmirnovToeplitzKernelElement U) (G : SmirnovToeplitzKernelElement V) :
    SmirnovToeplitzKernelElement (smirnovToeplitzSymbolMul U V) where
  forward := F.forward.mul G.forward
  reflected := F.reflected.mul G.reflected
  boundary_relation := by
    filter_upwards [F.reflected.boundary_mul_ae G.reflected,
      F.forward.boundary_mul_ae G.forward,
      F.boundary_relation, G.boundary_relation] with x href hfwd hF hG
    rw [href, hF, hG, hfwd]
    simp only [smirnovToeplitzSymbolMul, map_mul]
    ring
  forward_nonzero := by
    have hFne : ¬ Set.EqOn F.forward.numerator.fn 0 (Metric.ball (0 : ℂ) 1) := by
      rintro hzero
      obtain ⟨z, hz, hne⟩ := F.forward_nonzero
      exact hne (hzero hz)
    have hGne : ¬ Set.EqOn G.forward.numerator.fn 0 (Metric.ball (0 : ℂ) 1) := by
      rintro hzero
      obtain ⟨z, hz, hne⟩ := G.forward_nonzero
      exact hne (hzero hz)
    have hprod := Bottcher.analyticOnNhd_mul_ne_zero
      (F.forward.numerator.diff.analyticOnNhd Metric.isOpen_ball)
      (G.forward.numerator.diff.analyticOnNhd Metric.isOpen_ball)
      Metric.isPreconnected_ball Metric.isOpen_ball hFne hGne
    by_contra hex
    push Not at hex
    apply hprod
    intro z hz
    have hz0 := hex z hz
    change F.forward.numerator.fn z * G.forward.numerator.fn z = 0 at hz0
    exact hz0

/-- A Smirnov Toeplitz-kernel element depends only on the almost-everywhere class of its
boundary symbol. -/
def SmirnovToeplitzKernelElement.congr {U V : ℝ → ℂ}
    (F : SmirnovToeplitzKernelElement U) (hUV : U =ᵐ[volume] V) :
    SmirnovToeplitzKernelElement V where
  forward := F.forward
  reflected := F.reflected
  boundary_relation := by
    filter_upwards [F.boundary_relation, hUV] with x hF hx
    rw [hF, hx]
  forward_nonzero := F.forward_nonzero

/-- Exact boundary phase-reflection symbol of a bounded analytic multiplier. -/
def diskMultiplierPhaseReflectionSymbol (φ : DiskMultiplier) (x : ℝ) : ℂ :=
  if diskMultiplierLineBoundary φ x = 0 then 1
  else (starRingEnd ℂ) (diskMultiplierLineBoundary φ x) /
    diskMultiplierLineBoundary φ x

theorem measurable_diskMultiplierPhaseReflectionSymbol (φ : DiskMultiplier) :
    Measurable (diskMultiplierPhaseReflectionSymbol φ) := by
  apply Measurable.ite
  · change MeasurableSet (diskMultiplierLineBoundary φ ⁻¹' ({0} : Set ℂ))
    exact measurable_diskMultiplierLineBoundary φ (measurableSet_singleton 0)
  · exact measurable_const
  · exact ((Complex.continuous_conj.measurable.comp
      (measurable_diskMultiplierLineBoundary φ)).div
        (measurable_diskMultiplierLineBoundary φ))

theorem norm_diskMultiplierPhaseReflectionSymbol (φ : DiskMultiplier) (x : ℝ) :
    ‖diskMultiplierPhaseReflectionSymbol φ x‖ = 1 := by
  rw [diskMultiplierPhaseReflectionSymbol]
  split_ifs with hx
  · simp
  · rw [norm_div]
    change ‖(starRingEnd ℂ) (diskMultiplierLineBoundary φ x)‖ /
      ‖diskMultiplierLineBoundary φ x‖ = 1
    simp [hx]

/-- Every nonzero bounded analytic multiplier is a nonzero element of the Toeplitz kernel of its
literal phase-reflection symbol. No measurable phase lift is chosen. -/
def diskMultiplierSmirnovToeplitzElement
    (φ : DiskMultiplier) (hφ : ∃ z ∈ Metric.ball (0 : ℂ) 1, φ.fn z ≠ 0) :
    SmirnovToeplitzKernelElement (diskMultiplierPhaseReflectionSymbol φ) where
  forward := DiskSmirnovBoundary.ofMultiplier φ
  reflected := DiskSmirnovBoundary.ofMultiplier φ
  boundary_relation := by
    filter_upwards [DiskSmirnovBoundary.boundary_ofMultiplier_ae φ,
      DiskSmirnovBoundary.boundary_ofMultiplier_ae φ,
      diskMultiplierLineBoundary_ne_zero_ae φ hφ] with x href hfwd hx
    simp only [href, diskMultiplierPhaseReflectionSymbol, if_neg hx,
      map_div₀, starRingEnd_self_apply]
    exact (div_mul_cancel₀ _ ((map_ne_zero (starRingEnd ℂ)).2 hx)).symm
  forward_nonzero := hφ

end

end GaloisForLFunctions.HTGeometry
