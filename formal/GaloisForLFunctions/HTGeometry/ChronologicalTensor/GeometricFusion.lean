import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicJoin
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FusionDivisor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Zeta zeros from the geometric fusion trace

The discrete trace uses actual finite faces of repeated cubic joins, weighted
by logarithms of the already proved capacity suprema. The continuous reference
is an actual improper integral of the linear interpolation of these levels.
Their difference has a convergent Mellin integral in the open strip and exactly
the zeta zero locus there, including multiplicities. No zeta value or zero is
used in the definition of either trace or of the resulting kernel.
-/

open Complex Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section


def fusionContinuousHeat (t : ℝ) : ℝ :=
  -(∫ x : ℝ in Ioi 0, Real.exp (-(fusionSpacing*t)*x))

theorem fusionContinuousHeat_integrable :
    ∀ t ∈ Ioi (0 : ℝ),
      IntegrableOn (fun x : ℝ => Real.exp (-(fusionSpacing*t)*x)) (Ioi 0) := by
  intro t ht
  exact integrableOn_exp_mul_Ioi (neg_neg_of_pos (mul_pos fusionSpacing_pos ht)) 0

theorem fusionContinuousHeat_eq :
    Set.EqOn fusionContinuousHeat (fun t => -(1/(fusionSpacing*t))) (Ioi 0) := by
  intro t ht
  unfold fusionContinuousHeat
  rw [integral_exp_mul_Ioi (neg_neg_of_pos (mul_pos fusionSpacing_pos ht))]
  simp

def geometricFusionKernel (t : ℝ) : ℂ :=
  if 0<t then ((cubicEulerHeat (Real.log t)-fusionContinuousHeat t : ℝ) : ℂ) else 0

theorem geometricFusionKernel_eq : geometricFusionKernel=fusionRegularizedKernel := by
  funext t
  by_cases ht : 0<t
  · have hcont := fusionContinuousHeat_eq ht
    have hheat := cubicEulerHeat_kernel (Real.log t)
    rw [Real.exp_log ht] at hheat
    rw [geometricFusionKernel,if_pos ht,hcont]
    rw [hheat]
    push_cast
    ring
  · have hprod : ¬0<fusionSpacing*t := by
      exact not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos fusionSpacing_pos.le (not_lt.mp ht))
    simp only [geometricFusionKernel,if_neg ht,fusionRegularizedKernel,
      fusionBoseDefect,if_neg hprod,Complex.ofReal_zero]

theorem geometricFusionKernel_converges :
    ∀ s ∈ fusionMellinStrip, MellinConvergent geometricFusionKernel s := by
  rw [geometricFusionKernel_eq]
  exact fusionRegularizedKernel_converges

theorem geometricFusionKernel_mellin :
    Set.EqOn (mellin geometricFusionKernel)
      (fun s => -(fusionSpacing : ℂ)^(-s)*Complex.Gamma s*riemannZeta s)
      fusionMellinStrip := by
  rw [geometricFusionKernel_eq]
  exact fusionRegularizedKernel_mellin

theorem geometricFusionKernel_zeroLocus :
    {s ∈ fusionMellinStrip | mellin geometricFusionKernel s=0}=
      {s ∈ fusionMellinStrip | riemannZeta s=0} := by
  rw [geometricFusionKernel_eq]
  exact fusionRegularizedKernel_zeroLocus

theorem geometricFusionKernel_zeroMultiplicity :
    Set.EqOn (analyticOrderAt (mellin geometricFusionKernel))
      (analyticOrderAt riemannZeta) fusionMellinStrip := by
  rw [geometricFusionKernel_eq]
  exact fusionRegularizedKernel_zeroMultiplicity

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
