/-
# Exact Mellin transport of the CCM archimedean scaling representation

This module proves the missing operator identification used in Connes--Consani's
archimedean trace formula. Every intrinsic `L¹` logarithmic kernel acts by integrated
even dilation on the physical side and by its exactly normalized Fourier--Mellin symbol
on the spectral side. For Schwartz kernels this identifies the literal geometric
product with the previously constructed phase-log differential and proves it trace class.
No regularity, trace-class, or transform-intertwining premise is assumed.
-/

import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanConvolutionRepresentation
import GaloisForLFunctions.RHTower.HardyTitchmarshEulerConcrete
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseOperatorProduct
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import Mathlib.Analysis.Fourier.Convolution

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- Exact spectral multiplier symbol of an intrinsic logarithmic `L¹` kernel. -/
def ccmLogKernelMellinSymbol (g : CCMLogKernel) (t : ℝ) : ℂ :=
  Real.Lp.fourierTransform g (t / (2 * Real.pi))

theorem ccmLogKernelMellinSymbol_continuous (g : CCMLogKernel) : Continuous (ccmLogKernelMellinSymbol g) := by
  exact (Real.Lp.fourierTransform g).continuous.comp
    (continuous_id.div_const (2 * Real.pi))

theorem norm_ccmLogKernelMellinSymbol_le (g : CCMLogKernel) (t : ℝ) :
    ‖ccmLogKernelMellinSymbol g t‖ ≤ ‖g‖ := by
  rw [ccmLogKernelMellinSymbol, Real.Lp.fourierTransform_apply]
  calc
    ‖𝓕 (g : ℝ → ℂ) (t / (2 * Real.pi))‖ ≤ ∫ u : ℝ, ‖g u‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ ℝ) (g : ℝ → ℂ) _
    _ = ‖g‖ := (L1.norm_eq_integral_norm g).symm

theorem ccmLogKernelMellinSymbol_eq_integral (g : CCMLogKernel) (t : ℝ) :
    ccmLogKernelMellinSymbol g t =
      ∫ u : ℝ, g u * MellinL2.mellinCharacter (Real.exp (-u)) t := by
  rw [ccmLogKernelMellinSymbol, Real.Lp.fourierTransform_apply,
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  unfold MellinL2.mellinCharacter
  rw [Real.log_exp]
  change Complex.exp (↑(-2 * Real.pi * u * (t / (2 * Real.pi))) * I) * g u =
    g u * Complex.exp (↑(-u * t) * I)
  have hphase :
      (↑(-2 * Real.pi * u * (t / (2 * Real.pi))) : ℂ) * I =
        (↑(-u * t) : ℂ) * I := by
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hphase]
  ring

def ccmLogKernelMellinMultiplier (g : CCMLogKernel) : SpectralL2 →L[ℂ] SpectralL2 :=
  lpBoundedMulCLM (ccmLogKernelMellinSymbol_continuous g).measurable (norm_nonneg g)
    (norm_ccmLogKernelMellinSymbol_le g)

theorem ccmLogKernelMellinMultiplier_ae (g : CCMLogKernel) (F : SpectralL2) :
    ccmLogKernelMellinMultiplier g F =ᵐ[volume] fun t => ccmLogKernelMellinSymbol g t * F t :=
  lpBoundedMulCLM_coeFn (ccmLogKernelMellinSymbol_continuous g).measurable
    (norm_nonneg g) (norm_ccmLogKernelMellinSymbol_le g) F

theorem integrable_ccmMellinSpectralOrbit
    (g : CCMLogKernel) (f : evenSubspace) :
    Integrable (fun u : ℝ => g u •
      MellinL2.mellinCharacterMulUnitary (Real.exp (-u))
        (archimedeanMellinUnitary f)) volume := by
  have hmap :=
    archimedeanMellinUnitary.toLinearIsometry.toContinuousLinearMap.integrable_comp
      (integrable_ccmLogKernel_smul_orbit g f)
  refine hmap.congr (Filter.Eventually.of_forall fun u => ?_)
  change archimedeanMellinUnitary.toLinearIsometry.toContinuousLinearMap
      (g u • ccmLogDilationOrbit f u) =
    g u • MellinL2.mellinCharacterMulUnitary (Real.exp (-u))
      (archimedeanMellinUnitary f)
  rw [map_smul]
  congr 1
  unfold ccmLogDilationOrbit
  exact archimedeanMellinUnitary_evenDilation _ _ f

theorem integrable_ccmMellinJointProduct (g : CCMLogKernel) (G F : SpectralL2) :
    Integrable (fun p : ℝ × ℝ =>
      (g p.1 * MellinL2.mellinCharacter (Real.exp (-p.1)) p.2) *
        (starRingEnd ℂ (G p.2) * F p.2)) (volume.prod volume) := by
  let phi : ℝ → ℂ := fun t => starRingEnd ℂ (G t) * F t
  have hphi : Integrable phi volume := by
    simpa [phi, RCLike.inner_apply, mul_comm] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) G F)
  have hbase : Integrable (fun p : ℝ × ℝ => g p.1 * phi p.2)
      (volume.prod volume) :=
    Integrable.op_fst_snd continuous_mul ⟨1, fun x y : ℂ => by simp⟩
      (L1.integrable_coeFn g) hphi
  have hcharfun : (fun p : ℝ × ℝ =>
      MellinL2.mellinCharacter (Real.exp (-p.1)) p.2) =
        fun p => Complex.exp (((-p.1 * p.2 : ℝ) : ℂ) * I) := by
    funext p
    simp [MellinL2.mellinCharacter]
  have hchar : Continuous (fun p : ℝ × ℝ =>
      MellinL2.mellinCharacter (Real.exp (-p.1)) p.2) := by
    rw [hcharfun]
    fun_prop
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (g p.1 * MellinL2.mellinCharacter (Real.exp (-p.1)) p.2) *
        phi p.2) (volume.prod volume) :=
    (((L1.aestronglyMeasurable_coeFn g).comp_fst.mul
      hchar.aestronglyMeasurable).mul hphi.aestronglyMeasurable.comp_snd)
  refine hbase.norm.mono' hmeas ?_
  filter_upwards with p
  simp only [norm_mul, MellinL2.norm_mellinCharacter, mul_one, phi]
  rfl

theorem archimedeanMellinUnitary_ccmIntegratedScaling_eq_integral (g : CCMLogKernel) (f : evenSubspace) :
    archimedeanMellinUnitary (ccmIntegratedScaling g f) =
      ∫ u : ℝ, g u • MellinL2.mellinCharacterMulUnitary
        (Real.exp (-u)) (archimedeanMellinUnitary f) := by
  rw [ccmIntegratedScaling_apply]
  change archimedeanMellinUnitary.toLinearIsometry.toContinuousLinearMap
    (∫ u : ℝ, g u • ccmLogDilationOrbit f u) = _
  rw [← archimedeanMellinUnitary.toLinearIsometry.toContinuousLinearMap.integral_comp_comm
    (integrable_ccmLogKernel_smul_orbit g f)]
  apply integral_congr_ae
  filter_upwards with u
  rw [map_smul]
  congr 1
  unfold ccmLogDilationOrbit
  exact archimedeanMellinUnitary_evenDilation _ _ f

theorem inner_archimedeanMellinUnitary_ccmIntegratedScaling (g : CCMLogKernel) (G : SpectralL2) (f : evenSubspace) :
    inner ℂ G (archimedeanMellinUnitary (ccmIntegratedScaling g f)) =
      inner ℂ G (ccmLogKernelMellinMultiplier g (archimedeanMellinUnitary f)) := by
  let F : SpectralL2 := archimedeanMellinUnitary f
  let phi : ℝ → ℂ := fun t => starRingEnd ℂ (G t) * F t
  rw [archimedeanMellinUnitary_ccmIntegratedScaling_eq_integral]
  have hinner := (innerSL ℂ G).integral_comp_comm
    (integrable_ccmMellinSpectralOrbit g f)
  simp only [coe_innerSL_apply] at hinner
  rw [← hinner]
  have hslice : ∀ u : ℝ,
      inner ℂ G (g u • MellinL2.mellinCharacterMulUnitary
        (Real.exp (-u)) F) =
        ∫ t : ℝ,
          (g u * MellinL2.mellinCharacter (Real.exp (-u)) t) * phi t := by
    intro u
    rw [inner_smul_right, MeasureTheory.L2.inner_def, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [MellinL2.mellinCharacterMulUnitary_ae
      (Real.exp (-u)) F] with t ht
    rw [ht]
    simp only [phi, RCLike.inner_apply]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hslice)]
  rw [integral_integral_swap (integrable_ccmMellinJointProduct g G F)]
  have ht : ∀ t : ℝ,
      (∫ u : ℝ,
        (g u * MellinL2.mellinCharacter (Real.exp (-u)) t) * phi t) =
          ccmLogKernelMellinSymbol g t * phi t := by
    intro t
    rw [integral_mul_const, ccmLogKernelMellinSymbol_eq_integral]
  rw [integral_congr_ae (Filter.Eventually.of_forall ht)]
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmLogKernelMellinMultiplier_ae g F] with t hF
  rw [hF]
  simp only [phi, RCLike.inner_apply]
  ring

/-- Exact Mellin intertwining of integrated logarithmic scaling with multiplication. -/
theorem archimedeanMellinUnitary_ccmIntegratedScaling (g : CCMLogKernel) (f : evenSubspace) :
    archimedeanMellinUnitary (ccmIntegratedScaling g f) =
      ccmLogKernelMellinMultiplier g (archimedeanMellinUnitary f) := by
  apply ext_inner_left ℂ
  intro G
  exact inner_archimedeanMellinUnitary_ccmIntegratedScaling g G f

def ccmMellinSpectralScale : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 ((2 * Real.pi)⁻¹)
      (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))

@[simp] theorem ccmMellinSpectralScale_apply (t : ℝ) :
    ccmMellinSpectralScale t = t / (2 * Real.pi) := by
  change (2 * Real.pi)⁻¹ * t = t / (2 * Real.pi)
  ring

def ccmSchwartzLogKernel (g : 𝓢(ℝ, ℂ)) : CCMLogKernel :=
  g.toLp 1 volume

theorem ccmSchwartzLogKernel_ae (g : 𝓢(ℝ, ℂ)) :
    (ccmSchwartzLogKernel g : ℝ → ℂ) =ᵐ[volume] g :=
  g.coeFn_toLp 1 volume

def ccmSchwartzMellinSymbol (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ccmMellinSpectralScale
    ((SchwartzMap.fourierTransformCLM ℂ) g)

@[simp] theorem ccmSchwartzMellinSymbol_apply (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ccmSchwartzMellinSymbol g t =
      (𝓕 (g : ℝ → ℂ)) (t / (2 * Real.pi)) := by
  change ((SchwartzMap.fourierTransformCLM ℂ) g) (ccmMellinSpectralScale t) = _
  rw [ccmMellinSpectralScale_apply]
  exact congrFun (SchwartzMap.fourier_coe g) _

theorem ccmLogKernelMellinSymbol_schwartz_eq (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ccmLogKernelMellinSymbol (ccmSchwartzLogKernel g) t = ccmSchwartzMellinSymbol g t := by
  rw [ccmLogKernelMellinSymbol, Real.Lp.fourierTransform_apply,
    ccmSchwartzMellinSymbol_apply, Real.fourier_eq, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [ccmSchwartzLogKernel_ae g] with u hu
  rw [hu]

theorem ccmLogKernelMellinMultiplier_schwartz_eq (g : 𝓢(ℝ, ℂ)) :
    ccmLogKernelMellinMultiplier (ccmSchwartzLogKernel g) =
      ccmSchwartzMultiplier (ccmSchwartzMellinSymbol g) := by
  apply ContinuousLinearMap.ext
  intro F
  apply Lp.ext
  filter_upwards [ccmLogKernelMellinMultiplier_ae (ccmSchwartzLogKernel g) F,
    ccmSchwartzMultiplier_coeFn (ccmSchwartzMellinSymbol g) F] with t hleft hright
  rw [hleft, hright, ccmLogKernelMellinSymbol_schwartz_eq]

theorem archimedeanMellinUnitary_ccmIntegratedScaling_schwartz (g : 𝓢(ℝ, ℂ)) (f : evenSubspace) :
    archimedeanMellinUnitary
        (ccmIntegratedScaling (ccmSchwartzLogKernel g) f) =
      ccmSchwartzMultiplier (ccmSchwartzMellinSymbol g)
        (archimedeanMellinUnitary f) := by
  rw [archimedeanMellinUnitary_ccmIntegratedScaling, ccmLogKernelMellinMultiplier_schwartz_eq]

def ccmArchimedeanMellinCLM : evenSubspace →L[ℂ] SpectralL2 :=
  archimedeanMellinUnitary.toLinearIsometry.toContinuousLinearMap

def ccmArchimedeanMellinInvCLM : SpectralL2 →L[ℂ] evenSubspace :=
  archimedeanMellinUnitary.symm.toLinearIsometry.toContinuousLinearMap

theorem ccmArchimedeanMellinCLM_comp_inv : ccmArchimedeanMellinCLM ∘L ccmArchimedeanMellinInvCLM = 1 := by
  apply ContinuousLinearMap.ext
  intro F
  exact archimedeanMellinUnitary.apply_symm_apply F

theorem ccmArchimedeanMellinInvCLM_comp : ccmArchimedeanMellinInvCLM ∘L ccmArchimedeanMellinCLM = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact archimedeanMellinUnitary.symm_apply_apply f

theorem ccmIntegratedScaling_schwartz_eq_mellinConjugate (g : 𝓢(ℝ, ℂ)) :
    ccmIntegratedScaling (ccmSchwartzLogKernel g) =
      ccmArchimedeanMellinInvCLM ∘L
        (ccmSchwartzMultiplier (ccmSchwartzMellinSymbol g) ∘L ccmArchimedeanMellinCLM) := by
  apply ContinuousLinearMap.ext
  intro f
  change ccmIntegratedScaling (ccmSchwartzLogKernel g) f =
    archimedeanMellinUnitary.symm
      (ccmSchwartzMultiplier (ccmSchwartzMellinSymbol g)
        (archimedeanMellinUnitary f))
  apply archimedeanMellinUnitary.injective
  rw [archimedeanMellinUnitary.apply_symm_apply]
  exact archimedeanMellinUnitary_ccmIntegratedScaling_schwartz g f

/-- Physical-even-space conjugate of the spectral CCM scattering logarithmic differential. -/
def ccmArchimedeanGeometricScatteringLogDifferential : evenSubspace →L[ℂ] evenSubspace :=
  ccmArchimedeanMellinInvCLM ∘L
    (ccmArchimedeanScatteringLogDifferential ∘L ccmArchimedeanMellinCLM)

theorem ccmIntegratedScaling_mul_geometricScatteringLogDifferential_eq_mellinConjugate (g : 𝓢(ℝ, ℂ)) :
    ccmIntegratedScaling (ccmSchwartzLogKernel g) ∘L ccmArchimedeanGeometricScatteringLogDifferential =
      ccmArchimedeanMellinInvCLM ∘L
        ((ccmSchwartzMultiplier (ccmSchwartzMellinSymbol g) *
          ccmArchimedeanScatteringLogDifferential) ∘L ccmArchimedeanMellinCLM) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply, ccmIntegratedScaling_schwartz_eq_mellinConjugate]
  change archimedeanMellinUnitary.symm
      (ccmSchwartzMultiplier (ccmSchwartzMellinSymbol g)
        (archimedeanMellinUnitary
          (archimedeanMellinUnitary.symm
            (ccmArchimedeanScatteringLogDifferential
              (archimedeanMellinUnitary f))))) =
    archimedeanMellinUnitary.symm
      (ccmSchwartzMultiplier (ccmSchwartzMellinSymbol g)
        (ccmArchimedeanScatteringLogDifferential
          (archimedeanMellinUnitary f)))
  rw [archimedeanMellinUnitary.apply_symm_apply]

theorem ccmIsTraceClass_unitaryConjugate
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (U : H ≃ₗᵢ[ℂ] K) (T : K →L[ℂ] K)
    (hT : T.IsTraceClass) :
    (U.symm.toLinearIsometry.toContinuousLinearMap ∘L
      (T ∘L U.toLinearIsometry.toContinuousLinearMap)).IsTraceClass := by
  rcases hT with ⟨S, V, hS, hV, hfactor⟩
  let S' : H →L[ℂ] H :=
    U.symm.toLinearIsometry.toContinuousLinearMap ∘L
      (S ∘L U.toLinearIsometry.toContinuousLinearMap)
  let V' : H →L[ℂ] H :=
    U.symm.toLinearIsometry.toContinuousLinearMap ∘L
      (V ∘L U.toLinearIsometry.toContinuousLinearMap)
  have hS' : S'.IsHilbertSchmidt :=
    (hS.comp_left U.symm.toLinearIsometry.toContinuousLinearMap).comp_right
      U.toLinearIsometry.toContinuousLinearMap
  have hV' : V'.IsHilbertSchmidt :=
    (hV.comp_left U.symm.toLinearIsometry.toContinuousLinearMap).comp_right
      U.toLinearIsometry.toContinuousLinearMap
  refine ⟨S', V', hS', hV', ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  simp only [hfactor, S', V', ContinuousLinearMap.comp_apply]
  change U.symm (S (V (U x))) =
    U.symm (S (U (U.symm (V (U x)))))
  rw [U.apply_symm_apply]

/-- The literal geometric CCM product is trace class for every Schwartz log kernel. -/
theorem ccmIntegratedScaling_mul_geometricScatteringLogDifferential_isTraceClass (g : 𝓢(ℝ, ℂ)) :
    (ccmIntegratedScaling (ccmSchwartzLogKernel g) ∘L
      ccmArchimedeanGeometricScatteringLogDifferential).IsTraceClass := by
  rw [ccmIntegratedScaling_mul_geometricScatteringLogDifferential_eq_mellinConjugate]
  exact ccmIsTraceClass_unitaryConjugate archimedeanMellinUnitary _
    (ccmSchwartzMultiplier_mul_scatteringLogDifferential_isTraceClass
      (ccmSchwartzMellinSymbol g))

end RHTower
