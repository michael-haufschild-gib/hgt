import GaloisForLFunctions.RHTower.SuzukiTaDeficiencyIndices
import GaloisForLFunctions.HTGeometry.HermiteFourierEigen

/-!
# Suzuki's energy-space derivative is symmetric

This closes Suzuki v2, Lemma 6.1 on the literal space `H(T_a)`.  The proof stays in the
completed prime--polar--Gamma source: on compact smooth data, `i d/dx` is the real Fourier
multiplier `-2 pi xi`.  Consequently it moves between the two slots without disturbing either
the exact Weil distribution or the physical `L²` correction in Suzuki's energy inner product.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform SchwartzMap
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem suzukiTaSmoothCoreToSource_toSchwartz_IDeriv
    (a : SuzukiPositiveAperture) (u : SuzukiTaSmoothCore a) :
    (suzukiTaSmoothCoreToSource a (suzukiTaSmoothCoreIDeriv a u)).toSchwartz =
      I • derivSCLM (suzukiTaSmoothCoreToSource a u).toSchwartz := by
  apply SchwartzMap.ext
  intro x
  simp only [CCMComplexSmoothInteriorSource.toSchwartz_apply, _root_.smul_apply,
    derivSCLM_apply, suzukiTaSmoothCoreToSource_apply,
    suzukiTaSmoothCoreIDeriv_apply, smul_eq_mul]
  change I * deriv u x = I * deriv u x
  rfl

/-- The literal Suzuki derivative has real Fourier symbol `-2 pi xi`. -/
theorem fourierSCLM_suzukiTaSmoothCoreIDeriv
    (a : SuzukiPositiveAperture) (u : SuzukiTaSmoothCore a) :
    fourierSCLM
        (suzukiTaSmoothCoreToSource a (suzukiTaSmoothCoreIDeriv a u)).toSchwartz =
      (-2 * (Real.pi : ℂ)) • mulXCLM
        (fourierSCLM (suzukiTaSmoothCoreToSource a u).toSchwartz) := by
  rw [suzukiTaSmoothCoreToSource_toSchwartz_IDeriv, map_smul,
    fourierSCLM_derivSCLM, smul_smul]
  congr 1
  calc
    I * (2 * (Real.pi : ℂ) * I) = 2 * (Real.pi : ℂ) * I ^ 2 := by ring
    _ = -2 * (Real.pi : ℂ) := by rw [Complex.I_sq]; ring

/-- The Hermitian source correlation is unchanged when `i d/dx` moves between slots. -/
theorem ccmComplexSmoothCrossCorrelation_suzukiTaSmoothCoreIDeriv
    (a : SuzukiPositiveAperture) (u v : SuzukiTaSmoothCore a) :
    ccmComplexSmoothCrossCorrelation
        (suzukiTaSmoothCoreToSource a (suzukiTaSmoothCoreIDeriv a u))
        (suzukiTaSmoothCoreToSource a v) =
      ccmComplexSmoothCrossCorrelation
        (suzukiTaSmoothCoreToSource a u)
        (suzukiTaSmoothCoreToSource a (suzukiTaSmoothCoreIDeriv a v)) := by
  apply (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)).injective
  rw [FourierTransform.fourierCLE_apply, FourierTransform.fourierCLE_apply]
  apply SchwartzMap.ext
  intro xi
  change 𝓕 (ccmComplexSmoothCrossCorrelation
        (suzukiTaSmoothCoreToSource a (suzukiTaSmoothCoreIDeriv a u))
        (suzukiTaSmoothCoreToSource a v) : ℝ → ℂ) xi =
    𝓕 (ccmComplexSmoothCrossCorrelation
        (suzukiTaSmoothCoreToSource a u)
        (suzukiTaSmoothCoreToSource a (suzukiTaSmoothCoreIDeriv a v)) : ℝ → ℂ) xi
  rw [fourier_ccmComplexSmoothCrossCorrelation,
    fourier_ccmComplexSmoothCrossCorrelation]
  have hu := congrArg (fun f : SchwartzMap ℝ ℂ => f xi)
    (fourierSCLM_suzukiTaSmoothCoreIDeriv a u)
  have hv := congrArg (fun f : SchwartzMap ℝ ℂ => f xi)
    (fourierSCLM_suzukiTaSmoothCoreIDeriv a v)
  simp only [fourierSCLM_apply, _root_.smul_apply, mulXCLM_apply,
    smul_eq_mul] at hu hv
  rw [hu, hv]
  simp only [map_mul, map_neg, map_ofNat, Complex.star_def,
    Complex.conj_ofReal]
  ring

/-- Suzuki's Hermitian convolution is the CCM Hermitian cross-correlation in source coordinates. -/
theorem ccmComplexSmoothCrossCorrelation_eq_suzukiHermitianConvolution
    {a : SuzukiPositiveAperture} (u v : CCMComplexSmoothInteriorSource a) :
    (ccmComplexSmoothCrossCorrelation u v : ℝ → ℂ) =
      suzukiHermitianConvolution
        v.toSuzukiSmoothCompactTest u.toSuzukiSmoothCompactTest := by
  funext x
  rw [ccmComplexSmoothCrossCorrelation,
    SchwartzMap.crossCorrelationSchwartz, SchwartzMap.convolution_apply,
    suzukiHermitianConvolution, MeasureTheory.convolution_def]
  rfl

/-- The exact completed Weil form is symmetric under moving the Suzuki derivative between slots. -/
theorem ccmRestrictedWeilForm_suzukiTaSmoothCoreIDeriv
    (a : SuzukiPositiveAperture) (u v : SuzukiTaSmoothCore a) :
    ccmRestrictedWeilForm a
        (suzukiTaSmoothCoreToSource a (suzukiTaSmoothCoreIDeriv a u)).toCCMFormVector
        (suzukiTaSmoothCoreToSource a v).toCCMFormVector =
      ccmRestrictedWeilForm a
        (suzukiTaSmoothCoreToSource a u).toCCMFormVector
        (suzukiTaSmoothCoreToSource a (suzukiTaSmoothCoreIDeriv a v)).toCCMFormVector := by
  rw [ccmRestrictedWeilForm_complexSmooth_eq_suzukiWeilDistribution,
    ccmRestrictedWeilForm_complexSmooth_eq_suzukiWeilDistribution]
  congr 1
  rw [← ccmComplexSmoothCrossCorrelation_eq_suzukiHermitianConvolution,
    ← ccmComplexSmoothCrossCorrelation_eq_suzukiHermitianConvolution,
    ccmComplexSmoothCrossCorrelation_suzukiTaSmoothCoreIDeriv]

theorem inner_suzukiTaPhysicalEmbedding_smoothCore
    (a : SuzukiPositiveAperture) (u v : SuzukiTaSmoothCore a) :
    inner ℂ
        (suzukiTaPhysicalEmbedding a (suzukiTaSmoothCoreToHilbert a u))
        (suzukiTaPhysicalEmbedding a (suzukiTaSmoothCoreToHilbert a v)) =
      ∫ x : ℝ, star (u x) * v x := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : SuzukiApertureInterval a.1,
        inner ℂ
          ((suzukiTaPhysicalEmbedding a
            (suzukiTaSmoothCoreToHilbert a u) :
              SuzukiApertureInterval a.1 → ℂ) x)
          ((suzukiTaPhysicalEmbedding a
            (suzukiTaSmoothCoreToHilbert a v) :
              SuzukiApertureInterval a.1 → ℂ) x)) =
        ∫ x : SuzukiApertureInterval a.1,
          star (u (x : ℝ)) * v (x : ℝ) := by
      apply integral_congr_ae
      filter_upwards [suzukiTaPhysicalEmbedding_smoothCore_ae a u,
        suzukiTaPhysicalEmbedding_smoothCore_ae a v] with x hu hv
      rw [hu, hv]
      simp [RCLike.inner_apply]
      ring
    _ = ∫ x in Icc (-a.1) a.1, star (u x) * v x := by
      simpa only [SuzukiApertureInterval] using
        (MeasureTheory.integral_subtype measurableSet_Icc
          (fun x : ℝ => star (u x) * v x))
    _ = ∫ x : ℝ, star (u x) * v x := by
      apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hxt : x ∉ tsupport (u : ℝ → ℂ) := by
        intro hmem
        exact hx (Ioo_subset_Icc_self (u.tsupport_subset hmem))
      rw [image_eq_zero_of_notMem_tsupport hxt]
      simp

theorem ccmComplexSmoothCrossCorrelation_zero_eq_inner_physical
    (a : SuzukiPositiveAperture) (u v : SuzukiTaSmoothCore a) :
    ccmComplexSmoothCrossCorrelation
        (suzukiTaSmoothCoreToSource a u)
        (suzukiTaSmoothCoreToSource a v) 0 =
      inner ℂ
        (suzukiTaPhysicalEmbedding a (suzukiTaSmoothCoreToHilbert a u))
        (suzukiTaPhysicalEmbedding a (suzukiTaSmoothCoreToHilbert a v)) := by
  rw [inner_suzukiTaPhysicalEmbedding_smoothCore]
  rw [ccmComplexSmoothCrossCorrelation_eq_suzukiHermitianConvolution,
    suzukiHermitianConvolution]
  apply integral_congr_ae
  filter_upwards with x
  simp only [CCMComplexSmoothInteriorSource.toSuzukiSmoothCompactTest_apply,
    suzukiTaSmoothCoreToSource_apply, suzukiHermitianReflection]
  simp
  ring

theorem inner_suzukiTaPhysicalEmbedding_suzukiTaSmoothCoreIDeriv
    (a : SuzukiPositiveAperture) (u v : SuzukiTaSmoothCore a) :
    inner ℂ
        (suzukiTaPhysicalEmbedding a
          (suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreIDeriv a u)))
        (suzukiTaPhysicalEmbedding a (suzukiTaSmoothCoreToHilbert a v)) =
      inner ℂ
        (suzukiTaPhysicalEmbedding a (suzukiTaSmoothCoreToHilbert a u))
        (suzukiTaPhysicalEmbedding a
          (suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreIDeriv a v))) := by
  rw [← ccmComplexSmoothCrossCorrelation_zero_eq_inner_physical,
    ← ccmComplexSmoothCrossCorrelation_zero_eq_inner_physical]
  exact congrArg (fun f : SchwartzMap ℝ ℂ => f 0)
    (ccmComplexSmoothCrossCorrelation_suzukiTaSmoothCoreIDeriv a u v)

/-- Suzuki v2, Lemma 6.1: `i d/dx` is symmetric on the literal dense core
`C_c^infty(-a,a)` in `H(T_a)`. -/
theorem suzukiTaSmoothCoreIDeriv_symmetric
    (a : SuzukiPositiveAperture) (u v : SuzukiTaSmoothCore a) :
    inner ℂ
        (suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreIDeriv a u))
        (suzukiTaSmoothCoreToHilbert a v) =
      inner ℂ
        (suzukiTaSmoothCoreToHilbert a u)
        (suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreIDeriv a v)) := by
  rw [inner_suzukiTa_eq, inner_suzukiTa_eq]
  change
    suzukiWeilIntervalForm a
        (suzukiTaSmoothCoreToSource a (suzukiTaSmoothCoreIDeriv a u)).toCCMFormVector
        (suzukiTaSmoothCoreToSource a v).toCCMFormVector + _ =
      suzukiWeilIntervalForm a
        (suzukiTaSmoothCoreToSource a u).toCCMFormVector
        (suzukiTaSmoothCoreToSource a (suzukiTaSmoothCoreIDeriv a v)).toCCMFormVector + _
  rw [suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm,
    suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm,
    ccmRestrictedWeilForm_suzukiTaSmoothCoreIDeriv,
    inner_suzukiTaPhysicalEmbedding_suzukiTaSmoothCoreIDeriv]

end RHTower

