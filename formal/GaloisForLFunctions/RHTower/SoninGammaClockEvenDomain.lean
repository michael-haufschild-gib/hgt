import GaloisForLFunctions.RHTower.SoninGammaClockSpectralDomain
import GaloisForLFunctions.RHTower.SoninGammaRemainderOperator
import GaloisForLFunctions.HTGeometry.LinearPMapBoundedUnitaryTransport

/-!
# Literal physical Gamma cutoffs and their maximal even domain

The finite positive clock kernel and its reflection retain both dilation
directions and the exact zero-clock counterterm. Their strong action and
Mellin symbol are proved before transporting the maximal-domain criterion.
The full physical carrier additionally requires its odd sector.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology LinearPMap
namespace RHTower

private theorem density_continuous (ε R : ℝ) (hε : 0 < ε) :
    ContinuousOn (fun u => ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ)) (Icc ε R) := by
  apply Complex.continuous_ofReal.comp_continuousOn
  intro u hu
  have hu0 : 0 < u := hε.trans_le hu.1
  have hd : Real.exp u-Real.exp (-u) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))
  unfold ccmPublishedArchimedeanDensity
  apply ContinuousAt.continuousWithinAt
  exact ((by fun_prop : ContinuousAt (fun t : ℝ => Real.exp (t/2)) u).div
    (by fun_prop) hd).div continuousAt_id hu0.ne'

private theorem positive_integrable (ε R : ℝ) (hε : 0 < ε) :
    Integrable ((Icc ε R).indicator (fun u => ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ))) volume :=
  (integrable_indicator_iff measurableSet_Icc).mpr (density_continuous ε R hε).integrableOn_Icc

/-- The literal finite positive-clock Gamma density as an intrinsic L1 kernel. -/
def gammaPositiveClockKernel (ε R : ℝ) (hε : 0 < ε) : CCMLogKernel :=
  (positive_integrable ε R hε).toL1 _

private theorem positiveKernel_ae (ε R : ℝ) (hε : 0 < ε) :
    (gammaPositiveClockKernel ε R hε : ℝ → ℂ) =ᵐ[volume]
      (Icc ε R).indicator (fun u => ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ)) :=
  (positive_integrable ε R hε).coeFn_toL1

/-- Both original Gamma clock directions, with their unchanged coefficients. -/
def gammaSymmetricClockKernel (ε R : ℝ) (hε : 0 < ε) : CCMLogKernel :=
  gammaPositiveClockKernel ε R hε + ccmLogKernelReflect (gammaPositiveClockKernel ε R hε)

private theorem positiveKernel_integral (ε R : ℝ) (hε : 0 < ε) :
    (∫ u : ℝ, gammaPositiveClockKernel ε R hε u) =
      ((∫ u in Icc ε R, ccmPublishedArchimedeanDensity u/u : ℝ):ℂ) := by
  rw [integral_congr_ae (positiveKernel_ae ε R hε), integral_indicator measurableSet_Icc,
    integral_complex_ofReal]

private theorem positiveKernel_smul_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (ε R : ℝ) (hε : 0 < ε) (f : ℝ → E) :
    (∫ u : ℝ, gammaPositiveClockKernel ε R hε u • f u) =
      ∫ u in Icc ε R, ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) • f u := by
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [positiveKernel_ae ε R hε] with u hu
  rw [hu]
  by_cases hmem : u ∈ Icc ε R
  · simp only [indicator_of_mem hmem]
  · simp only [indicator_of_notMem hmem, zero_smul]

private theorem reflect_smul_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (g : CCMLogKernel) (f : ℝ → E) :
    (∫ u : ℝ, ccmLogKernelReflect g u • f u) = ∫ u : ℝ, g u • f (-u) := by
  calc
    _ = ∫ u : ℝ, g (-u) • f u := by
      apply integral_congr_ae
      filter_upwards [ccmLogKernelReflect_ae g] with u hu
      rw [hu]
    _ = ∫ u : ℝ, g (-(-u)) • f (-u) := by
      symm
      exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding (fun u => g (-u) • f u)
    _ = _ := by simp only [neg_neg]

private def clockChar (ξ u : ℝ) : ℂ := MellinL2.mellinCharacter (Real.exp (-u)) ξ

private theorem clockChar_continuous (ξ : ℝ) : Continuous (clockChar ξ) := by
  unfold clockChar MellinL2.mellinCharacter
  simp only [Real.log_exp]
  fun_prop

private theorem clockChar_norm (ξ u : ℝ) : ‖clockChar ξ u‖ = 1 :=
  MellinL2.norm_mellinCharacter _ _

private theorem kernel_character_integrable (g : CCMLogKernel) (ξ : ℝ) :
    Integrable (fun u => g u*clockChar ξ u) volume := by
  apply (L1.integrable_coeFn g).norm.mono'
    ((Lp.aestronglyMeasurable g).mul (clockChar_continuous ξ).aestronglyMeasurable)
  filter_upwards [] with u
  simp only [Pi.mul_apply]
  rw [norm_mul, clockChar_norm, mul_one]

private theorem kernel_character_reverse_integrable (g : CCMLogKernel) (ξ : ℝ) :
    Integrable (fun u => g u*clockChar ξ (-u)) volume := by
  apply (L1.integrable_coeFn g).norm.mono'
    ((Lp.aestronglyMeasurable g).mul ((clockChar_continuous ξ).comp continuous_neg).aestronglyMeasurable)
  filter_upwards [] with u
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [norm_mul, clockChar_norm, mul_one]

private theorem symbol_symmetric (g : CCMLogKernel) (ξ : ℝ) :
    ccmLogKernelMellinSymbol (g+ccmLogKernelReflect g) ξ =
      (∫ u : ℝ, g u*clockChar ξ u)+(∫ u : ℝ, g u*clockChar ξ (-u)) := by
  rw [ccmLogKernelMellinSymbol_eq_integral]
  calc
    _ = ∫ u : ℝ, g u*clockChar ξ u+ccmLogKernelReflect g u*clockChar ξ u := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add g (ccmLogKernelReflect g)] with u hu
      rw [hu, Pi.add_apply, add_mul]
      rfl
    _ = (∫ u : ℝ, g u*clockChar ξ u)+(∫ u : ℝ, ccmLogKernelReflect g u*clockChar ξ u) :=
      integral_add (kernel_character_integrable g ξ) (kernel_character_integrable (ccmLogKernelReflect g) ξ)
    _ = _ := by
      congr 1
      exact reflect_smul_integral g (clockChar ξ)

private theorem clockChar_second_difference (ξ u : ℝ) :
    clockChar ξ u+clockChar ξ (-u)-2 = ((2*(Real.cos (ξ*u)-1):ℝ):ℂ) := by
  unfold clockChar MellinL2.mellinCharacter
  simp only [Real.log_exp, neg_neg]
  push_cast
  rw [mul_comm (ξ:ℂ) (u:ℂ), Complex.cos]
  simp only [neg_mul]
  ring

/-- Literal clock-zero mass subtracted by the symmetric Gamma source. -/
def gammaClockCutoffMass (ε R : ℝ) : ℝ := 2*∫ u in Icc ε R, ccmPublishedArchimedeanDensity u/u

/-- Exact finite-kernel Mellin symbol, with the full original zero-clock subtraction. -/
theorem gammaSymmetricClockKernel_symbol (ε R : ℝ) (hε : 0 < ε) (ξ : ℝ) :
    ccmLogKernelMellinSymbol (gammaSymmetricClockKernel ε R hε) ξ-
      (gammaClockCutoffMass ε R:ℂ) = (gammaClockCutoffSymbol ε R ξ:ℂ) := by
  let g := gammaPositiveClockKernel ε R hε
  have hmass : (gammaClockCutoffMass ε R:ℂ) = ∫ u : ℝ, g u*(2:ℂ) := by
    rw [integral_mul_const, positiveKernel_integral]
    unfold gammaClockCutoffMass
    push_cast
    ring
  have hs : Integrable (fun u => g u*clockChar ξ u+g u*clockChar ξ (-u)) volume :=
    (kernel_character_integrable g ξ).add (kernel_character_reverse_integrable g ξ)
  rw [gammaSymmetricClockKernel, symbol_symmetric, hmass,
    ← integral_add (kernel_character_integrable g ξ) (kernel_character_reverse_integrable g ξ),
    ← integral_sub hs ((L1.integrable_coeFn g).mul_const 2)]
  calc
    _ = ∫ u : ℝ, g u • ((2*(Real.cos (ξ*u)-1):ℝ):ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [← mul_add, ← mul_sub, clockChar_second_difference]
      rfl
    _ = ∫ u in Icc ε R, ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) •
        ((2*(Real.cos (ξ*u)-1):ℝ):ℂ) := positiveKernel_smul_integral ε R hε _
    _ = (gammaClockCutoffSymbol ε R ξ:ℂ) := by
      rw [gammaClockCutoffSymbol, ← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [] with u
      change ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) * ((2*(Real.cos (ξ*u)-1):ℝ):ℂ) =
        ((2*(Real.cos (ξ*u)-1)*ccmPublishedArchimedeanDensity u/u:ℝ):ℂ)
      push_cast
      ring

/-- Actual finite Gamma operator on the physical even carrier. -/
def gammaClockCutoffEvenOperator (ε R : ℝ) (hε : 0 < ε) : evenSubspace →L[ℂ] evenSubspace :=
  ccmIntegratedScaling (gammaSymmetricClockKernel ε R hε)-
    (gammaClockCutoffMass ε R:ℂ) • (1:evenSubspace →L[ℂ] evenSubspace)


private theorem cutoffSpectral_ae (ε R : ℝ) (hε : 0 < ε) (f : SpectralL2) :
    (gammaClockCutoffSpectralOperator ε R hε f : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (gammaClockCutoffSymbol ε R ξ:ℂ)*f ξ := by
  unfold gammaClockCutoffSpectralOperator
  exact lpBoundedMulCLM_coeFn _ _ _ f

/-- Exact finite Mellin identification of the original physical Gamma kernel. -/
theorem archimedeanMellinUnitary_gammaClockCutoff (ε R : ℝ) (hε : 0 < ε) (f : evenSubspace) :
    archimedeanMellinUnitary (gammaClockCutoffEvenOperator ε R hε f) =
      gammaClockCutoffSpectralOperator ε R hε (archimedeanMellinUnitary f) := by
  change archimedeanMellinUnitary (ccmIntegratedScaling (gammaSymmetricClockKernel ε R hε) f-
    (gammaClockCutoffMass ε R:ℂ) • f) = _
  rw [map_sub, map_smul, archimedeanMellinUnitary_ccmIntegratedScaling]
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub
      (ccmLogKernelMellinMultiplier (gammaSymmetricClockKernel ε R hε) (archimedeanMellinUnitary f))
      ((gammaClockCutoffMass ε R:ℂ) • archimedeanMellinUnitary f),
    Lp.coeFn_smul (gammaClockCutoffMass ε R:ℂ) (archimedeanMellinUnitary f),
    ccmLogKernelMellinMultiplier_ae (gammaSymmetricClockKernel ε R hε) (archimedeanMellinUnitary f),
    cutoffSpectral_ae ε R hε (archimedeanMellinUnitary f)] with ξ hsub hsmul hleft hright
  rw [hsub, Pi.sub_apply, hleft, hsmul, hright]
  change _ - (gammaClockCutoffMass ε R:ℂ)*_ = _
  rw [← sub_mul, gammaSymmetricClockKernel_symbol]

private theorem kernel_reverse_orbit_integrable (g : CCMLogKernel) (f : evenSubspace) :
    Integrable (fun u => g u • ccmLogDilationOrbit f (-u)) volume := by
  apply ((L1.integrable_coeFn g).norm.mul_const ‖f‖).mono'
    ((Lp.aestronglyMeasurable g).smul ((continuous_ccmLogDilationOrbit f).comp continuous_neg).aestronglyMeasurable)
  filter_upwards [] with u
  change ‖g u • ccmLogDilationOrbit f (-u)‖ ≤ ‖g u‖*‖f‖
  rw [norm_smul, norm_ccmLogDilationOrbit]

private theorem mass_eq_positiveIntegral (ε R : ℝ) (hε : 0 < ε) :
    (gammaClockCutoffMass ε R:ℂ) = ∫ u : ℝ, gammaPositiveClockKernel ε R hε u*(2:ℂ) := by
  rw [integral_mul_const, positiveKernel_integral]
  unfold gammaClockCutoffMass
  push_cast
  ring

private theorem even_apply (ε R : ℝ) (hε : 0 < ε) (f : evenSubspace) :
    gammaClockCutoffEvenOperator ε R hε f =
      ∫ u in Icc ε R, ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) •
        (ccmLogDilationOrbit f u+ccmLogDilationOrbit f (-u)-(2:ℂ) • f) := by
  let g := gammaPositiveClockKernel ε R hε
  change ccmIntegratedScaling (g+ccmLogKernelReflect g) f-(gammaClockCutoffMass ε R:ℂ) • f = _
  have hr : (∫ u : ℝ, ccmLogKernelReflect g u • ccmLogDilationOrbit f u) =
      ∫ u : ℝ, g u • ccmLogDilationOrbit f (-u) := by
    simpa using! reflect_smul_integral g (ccmLogDilationOrbit f)
  rw [ccmIntegratedScaling_add, add_apply, ccmIntegratedScaling_apply,
    ccmIntegratedScaling_apply, hr, mass_eq_positiveIntegral ε R hε,
    ← integral_smul_const]
  have hs : Integrable (fun u => g u • ccmLogDilationOrbit f u+g u • ccmLogDilationOrbit f (-u)) volume :=
    (integrable_ccmLogKernel_smul_orbit g f).add (kernel_reverse_orbit_integrable g f)
  rw [← integral_add (integrable_ccmLogKernel_smul_orbit g f) (kernel_reverse_orbit_integrable g f)]
  change (∫ u : ℝ, g u • ccmLogDilationOrbit f u+g u • ccmLogDilationOrbit f (-u)) -
    (∫ u : ℝ, (g u*2) • f) = _
  rw [← integral_sub hs (((L1.integrable_coeFn g).mul_const 2).smul_const f)]
  calc
    _ = ∫ u : ℝ, g u • (ccmLogDilationOrbit f u+ccmLogDilationOrbit f (-u)-(2:ℂ) • f) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [smul_add, smul_sub, smul_smul]
    _ = _ := positiveKernel_smul_integral ε R hε _

/-- The finite physical operator is exactly the original strong Gamma integral,
with both dilation directions and the full clock-zero counterterm retained. -/
theorem gammaClockCutoffEvenOperator_apply (ε R : ℝ) (hε : 0 < ε) (f : evenSubspace) :
    (gammaClockCutoffEvenOperator ε R hε f : SoninL2) =
      ∫ u in Icc ε R, ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) •
        gammaClockDifferenceOperator u (f:SoninL2) := by
  have hc : Continuous (fun u => ccmLogDilationOrbit f u+ccmLogDilationOrbit f (-u)-(2:ℂ) • f) :=
    ((continuous_ccmLogDilationOrbit f).add ((continuous_ccmLogDilationOrbit f).comp continuous_neg)).sub continuous_const
  have hi : Integrable (fun u => ((ccmPublishedArchimedeanDensity u/u:ℝ):ℂ) •
      (ccmLogDilationOrbit f u+ccmLogDilationOrbit f (-u)-(2:ℂ) • f))
      (volume.restrict (Icc ε R)) :=
    ((density_continuous ε R hε).smul hc.continuousOn).integrableOn_Icc
  rw [even_apply]
  change evenSubspace.subtypeL (∫ u in Icc ε R, _) = _
  rw [← evenSubspace.subtypeL.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [map_smul]
  congr 1
  simp only [map_sub, map_add, map_smul, ccmLogDilationOrbit,
    gammaClockDifferenceOperator, sub_apply, add_apply, smul_apply,
    one_apply_eq_self, dilationCLM_apply, neg_neg]
  change dilation (Real.exp (-u)) (Real.exp_pos (-u)) (f:SoninL2) +
    dilation (Real.exp u) (Real.exp_pos u) (f:SoninL2) - (2:ℂ) • (f:SoninL2) =
    dilation (Real.exp u) (Real.exp_pos u) (f:SoninL2) +
    dilation (Real.exp (-u)) (Real.exp_pos (-u)) (f:SoninL2) - (2:ℂ) • (f:SoninL2)
  abel


open GaloisForLFunctions.HTGeometry

/-- The full Gamma clock operator on its maximal physical even domain. -/
def gammaClockEvenOperator : evenSubspace →ₗ.[ℂ] evenSubspace :=
  unitaryConjugateLinearPMap archimedeanMellinUnitary gammaClockSpectralOperator

/-- The exact physical even Gamma operator is self-adjoint on its maximal domain. -/
theorem gammaClockEvenOperator_isSelfAdjoint : IsSelfAdjoint gammaClockEvenOperator :=
  IsSelfAdjoint.unitaryConjugate archimedeanMellinUnitary gammaClockSpectralOperator_isSelfAdjoint

/-- The original physical Gamma cutoff family converges exactly on the maximal even domain. -/
theorem gammaClockCutoffEvenOperator_limit_iff
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [NeBot l]
    (ε R : ι → ℝ) (hpos : ∀ i, 0 < ε i)
    (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (f g : evenSubspace) :
    Tendsto (fun i => gammaClockCutoffEvenOperator (ε i) (R i) (hpos i) f) l (𝓝 g) ↔
      ∃ hf : f ∈ gammaClockEvenOperator.domain, gammaClockEvenOperator ⟨f,hf⟩ = g := by
  constructor
  · intro ht
    have h := archimedeanMellinUnitary.continuous.continuousAt.tendsto.comp ht
    have hspec := h.congr (fun i => archimedeanMellinUnitary_gammaClockCutoff (ε i) (R i) (hpos i) f)
    obtain ⟨hf,heq⟩ := (gammaClockCutoffSpectralOperator_limit_iff ε R hpos hε hR
      (archimedeanMellinUnitary f) (archimedeanMellinUnitary g)).mp hspec
    refine ⟨hf, ?_⟩
    change archimedeanMellinUnitary.symm
      (gammaClockSpectralOperator ⟨archimedeanMellinUnitary f,hf⟩) = g
    rw [heq, archimedeanMellinUnitary.symm_apply_apply]
  · rintro ⟨hf,heq⟩
    let fU : gammaClockSpectralOperator.domain := ⟨archimedeanMellinUnitary f,hf⟩
    have h := archimedeanMellinUnitary.symm.continuous.continuousAt.tendsto.comp
      (gammaClockCutoffSpectralOperator_tendsto ε R hpos hε hR fU)
    have heqg : archimedeanMellinUnitary.symm (gammaClockSpectralOperator fU) = g := heq
    rw [heqg] at h
    apply h.congr
    intro i
    apply archimedeanMellinUnitary.injective
    simp only [Function.comp_apply, archimedeanMellinUnitary.apply_symm_apply,
      archimedeanMellinUnitary_gammaClockCutoff]
    rfl

end RHTower
