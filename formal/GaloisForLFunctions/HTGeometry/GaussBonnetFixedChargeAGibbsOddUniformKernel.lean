import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddRationalFamily
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform convergence of the odd Gibbs force correction

The finite rational family is jointly continuous near its critical
coefficient vector on the compact physical interval. Heine–Cantor
upgrades the scalar coefficient limits to a uniform force correction.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAGibbsOddRationalFamily_continuousOn (w φ : ℝ) :
    ContinuousOn (fun p : EGBGibbsOddState × Icc (-1 : ℝ) 1 =>
      egbFixedChargeAGibbsOddRationalFamily w φ p.1 p.2)
      ({s : EGBGibbsOddState | |s.1| < 1 / 2} ×ˢ univ) := by
  dsimp [egbFixedChargeAGibbsOddRationalFamily]
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro p hp
    have hd : |p.1.1| < 1 / 2 := hp.1
    have ht : |(p.2 : ℝ)| ≤ 1 := abs_le.mpr p.2.property
    have hm : |p.1.1 * (p.2 : ℝ)| < 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left ht (abs_nonneg _)).trans_lt (by simpa only [mul_one] using hd)
    have hpos : 0 < 1 + p.1.1 * (p.2 : ℝ) := by
      linarith [(abs_lt.mp hm).1]
    positivity

theorem egbFixedChargeAGibbsOddRationalFamily_uniform_critical_limit (w φ : ℝ) :
    TendstoUniformly (fun s (t : Icc (-1 : ℝ) 1) => egbFixedChargeAGibbsOddRationalFamily w φ s t)
      (fun t => egbFixedChargeAGibbsOddRationalFamily w φ (egbFixedChargeAGibbsOddCriticalState w φ) t)
      (𝓝 (egbFixedChargeAGibbsOddCriticalState w φ)) := by
  have hU : {s : EGBGibbsOddState | |s.1| < 1 / 2} ∈ 𝓝 (egbFixedChargeAGibbsOddCriticalState w φ) := by
    apply (isOpen_lt (continuous_fst.abs) continuous_const).mem_nhds
    norm_num [egbFixedChargeAGibbsOddCriticalState]
  exact (egbFixedChargeAGibbsOddRationalFamily_continuousOn w φ).tendstoUniformly hU

theorem egbFixedChargeAGibbsOddKernel_uniform_critical_limit (w φ : ℝ) :
    TendstoUniformlyOn (egbFixedChargeAGibbsOddKernel w φ)
      (egbFixedChargeAGibbsOddLimitKernel w φ) atBot (Icc (-1 : ℝ) 1) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAGibbsOddRationalFamily_uniform_critical_limit w φ)) ε hε
  filter_upwards [(egbFixedChargeAGibbsOddState_critical_limit w φ).eventually h] with τ hτ
  intro t ht
  have he := egbFixedChargeAGibbsOddKernel_rational_family w φ τ ht
  rw [he, ← egbFixedChargeAGibbsOddRationalFamily_critical w φ t]
  exact hτ ⟨t, ht⟩

end GaloisForLFunctions.HTGeometry
