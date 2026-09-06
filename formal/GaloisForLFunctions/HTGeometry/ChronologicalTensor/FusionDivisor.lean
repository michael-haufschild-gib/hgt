import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FusionMellin
import Mathlib.Analysis.Analytic.Order

/-!
# The fusion response preserves zeta multiplicities

The Mellin identity holds as an equality of analytic germs throughout the
open strip. Its prefactor is analytic and nonvanishing there, so the order
of every zero agrees with the corresponding order of zeta.
-/

open Complex Set Filter MeasureTheory Asymptotics
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section


theorem fusionMellinStrip_isOpen : IsOpen fusionMellinStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

def fusionMellinFactor (s : ℂ) : ℂ :=
  -(fusionSpacing : ℂ)^(-s)*Complex.Gamma s

theorem fusionMellinFactor_nonzero :
    ∀ s ∈ fusionMellinStrip, fusionMellinFactor s ≠ 0 := by
  intro s hs
  have hpow : (fusionSpacing : ℂ)^(-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (ne_of_gt fusionSpacing_pos)))
  exact mul_ne_zero (neg_ne_zero.mpr hpow) (Complex.Gamma_ne_zero_of_re_pos hs.1)

theorem fusionMellinFactor_analytic :
    AnalyticOnNhd ℂ fusionMellinFactor fusionMellinStrip := by
  intro s hs
  have hd : Differentiable ℂ (fun z : ℂ => (fusionSpacing : ℂ)^(-z)) :=
    differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr
      (ne_of_gt fusionSpacing_pos)))
  exact (hd.analyticAt s).neg.mul (_root_.HTGeometry.analyticAt_Gamma_of_re_pos hs.1)

theorem fusionRegularizedKernel_mellin_germ :
    ∀ s ∈ fusionMellinStrip,
      mellin fusionRegularizedKernel =ᶠ[𝓝 s] fusionMellinFactor*riemannZeta := by
  intro s hs
  filter_upwards [fusionMellinStrip_isOpen.mem_nhds hs] with z hz
  exact fusionRegularizedKernel_mellin hz

theorem fusionRegularizedKernel_mellin_analytic :
    AnalyticOnNhd ℂ (mellin fusionRegularizedKernel) fusionMellinStrip := by
  intro s hs
  have hs1 : s ≠ 1 := by
    intro h
    have hh := hs.2
    rw [h,Complex.one_re] at hh
    exact lt_irrefl _ hh
  have hz := analyticOn_riemannZeta s (by simpa only [mem_compl_iff,mem_singleton_iff] using hs1)
  exact ((fusionMellinFactor_analytic s hs).mul hz).congr
    (fusionRegularizedKernel_mellin_germ s hs).symm

theorem fusionRegularizedKernel_zeroMultiplicity :
    Set.EqOn (analyticOrderAt (mellin fusionRegularizedKernel))
      (analyticOrderAt riemannZeta) fusionMellinStrip := by
  intro s hs
  have hs1 : s ≠ 1 := by
    intro h
    have hh := hs.2
    rw [h,Complex.one_re] at hh
    exact lt_irrefl _ hh
  have hz := analyticOn_riemannZeta s (by simpa only [mem_compl_iff,mem_singleton_iff] using hs1)
  rw [analyticOrderAt_congr (fusionRegularizedKernel_mellin_germ s hs),
    analyticOrderAt_mul (fusionMellinFactor_analytic s hs) hz,
    (fusionMellinFactor_analytic s hs).analyticOrderAt_eq_zero.mpr
      (fusionMellinFactor_nonzero s hs),zero_add]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
