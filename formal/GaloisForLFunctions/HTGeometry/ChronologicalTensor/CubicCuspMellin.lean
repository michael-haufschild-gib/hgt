import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspHeat
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FusionDivisor

/-!
# Zeta zeros in the normalization-defect response

The actual quotient-flow diagonal heat, subtracted from an actual continuous
reference integral, has a convergent Mellin transform on the open unit strip.
Its transform is -Gamma times zeta. The nonvanishing analytic Gamma factor
preserves the full zero locus and every zero multiplicity on that strip.
-/

open Complex Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section


theorem cubicCuspKernel_bose : cubicCuspKernel=fusionBoseKernel := by
  ext t
  exact cubicCuspKernel_eq t

theorem cubicCuspKernel_converges :
    ∀ s ∈ fusionMellinStrip, MellinConvergent cubicCuspKernel s := by
  rw [cubicCuspKernel_bose]
  exact fusionBoseKernel_converges

theorem cubicCuspKernel_mellin :
    EqOn (mellin cubicCuspKernel) (fun s => -Complex.Gamma s*riemannZeta s) fusionMellinStrip := by
  rw [cubicCuspKernel_bose]
  exact fusionBoseKernel_mellin

theorem cubicCuspKernel_zeroLocus :
    {s ∈ fusionMellinStrip | mellin cubicCuspKernel s=0}=
      {s ∈ fusionMellinStrip | riemannZeta s=0} := by
  ext s
  constructor
  · rintro ⟨hs,h⟩
    refine ⟨hs,?_⟩
    rw [cubicCuspKernel_mellin hs] at h
    exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr (Complex.Gamma_ne_zero_of_re_pos hs.1))
  · rintro ⟨hs,h⟩
    refine ⟨hs,?_⟩
    rw [cubicCuspKernel_mellin hs]
    dsimp only
    rw [h,mul_zero]

def cubicCuspMellinFactor (s : ℂ) : ℂ := -Complex.Gamma s

theorem cubicCuspMellinFactor_nonzero :
    ∀ s ∈ fusionMellinStrip, cubicCuspMellinFactor s ≠ 0 := by
  intro s hs
  exact neg_ne_zero.mpr (Complex.Gamma_ne_zero_of_re_pos hs.1)

theorem cubicCuspMellinFactor_analytic :
    AnalyticOnNhd ℂ cubicCuspMellinFactor fusionMellinStrip := by
  intro s hs
  exact (_root_.HTGeometry.analyticAt_Gamma_of_re_pos hs.1).neg

theorem cubicCuspKernel_mellin_germ :
    ∀ s ∈ fusionMellinStrip,
      mellin cubicCuspKernel =ᶠ[𝓝 s] cubicCuspMellinFactor*riemannZeta := by
  intro s hs
  filter_upwards [fusionMellinStrip_isOpen.mem_nhds hs] with z hz
  exact cubicCuspKernel_mellin hz

theorem cubicCuspKernel_mellin_analytic :
    AnalyticOnNhd ℂ (mellin cubicCuspKernel) fusionMellinStrip := by
  intro s hs
  have hs1 : s ≠ 1 := by
    intro h
    have hh := hs.2
    rw [h,Complex.one_re] at hh
    exact lt_irrefl _ hh
  have hz := analyticOn_riemannZeta s (by simpa only [mem_compl_iff,mem_singleton_iff] using hs1)
  exact ((cubicCuspMellinFactor_analytic s hs).mul hz).congr
    (cubicCuspKernel_mellin_germ s hs).symm

theorem cubicCuspKernel_zeroMultiplicity :
    EqOn (analyticOrderAt (mellin cubicCuspKernel))
      (analyticOrderAt riemannZeta) fusionMellinStrip := by
  intro s hs
  have hs1 : s ≠ 1 := by
    intro h
    have hh := hs.2
    rw [h,Complex.one_re] at hh
    exact lt_irrefl _ hh
  have hz := analyticOn_riemannZeta s (by simpa only [mem_compl_iff,mem_singleton_iff] using hs1)
  rw [analyticOrderAt_congr (cubicCuspKernel_mellin_germ s hs),
    analyticOrderAt_mul (cubicCuspMellinFactor_analytic s hs) hz,
    (cubicCuspMellinFactor_analytic s hs).analyticOrderAt_eq_zero.mpr
      (cubicCuspMellinFactor_nonzero s hs),zero_add]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
