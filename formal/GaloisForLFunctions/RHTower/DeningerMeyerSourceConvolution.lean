import GaloisForLFunctions.RHTower.DeningerMeyerNonlinearMellin
import GaloisForLFunctions.RHTower.DeningerMeyerGlobalXiSynthesis
import Mathlib.Analysis.Fourier.Convolution

/-! # Actual convolution and the Poisson ideal

Inverse Mellin reconstruction admits the product of any two original source
transforms. Fourier injectivity identifies this source with the literal
convolution integral. Global Xi division makes the actual Poisson range an
ideal, so the product descends to original Meyer middle cohomology.
-/

open Complex MeasureTheory
open scoped FourierTransform

namespace RHTower
noncomputable section

@[simp] theorem deningerMeyerStrongLogMellin_add
    (g h : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (g+h) s =
      deningerMeyerStrongLogMellin g s + deningerMeyerStrongLogMellin h s :=
  (deningerMeyerStrongLogMellinLM s).map_add g h

@[simp] theorem deningerMeyerStrongLogMellin_sub
    (g h : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (g-h) s =
      deningerMeyerStrongLogMellin g s - deningerMeyerStrongLogMellin h s :=
  (deningerMeyerStrongLogMellinLM s).map_sub g h

@[simp] theorem deningerMeyerStrongLogMellin_smul
    (c : ℂ) (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (c • g) s =
      c * deningerMeyerStrongLogMellin g s :=
  (deningerMeyerStrongLogMellinLM s).map_smul c g

@[simp] theorem deningerMeyerStrongLogMellin_zero (s : ℂ) :
    deningerMeyerStrongLogMellin (0 : ℝ → ℂ) s = 0 :=
  (deningerMeyerStrongLogMellinLM s).map_zero

/-- Admitted convolution of arbitrary original all-weight sources. -/
def deningerMeyerSourceConvolution (g h : DeningerMeyerStrongLogTarget) :
    DeningerMeyerStrongLogTarget :=
  deningerMeyerInverseMellinSource
    (fun s => deningerMeyerStrongLogMellin g s * deningerMeyerStrongLogMellin h s)
    ((deningerMeyerStrongLogMellin_entireRegular g).mul
      (deningerMeyerStrongLogMellin_entireRegular h))

@[simp] theorem deningerMeyerSourceConvolution_mellin
    (g h : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g h) s =
      deningerMeyerStrongLogMellin g s * deningerMeyerStrongLogMellin h s :=
  deningerMeyerInverseMellinSource_mellin _ _

private def sourceSchwartz (g : DeningerMeyerStrongLogTarget) : SchwartzMap ℝ ℂ :=
  (DeningerMeyerSource.toSource (deningerMeyerStrongLogSourceEquiv g)).val

private theorem sourceSchwartz_coe (g : DeningerMeyerStrongLogTarget) :
    (sourceSchwartz g : ℝ → ℂ) = g.val := rfl

/-- The reconstructed product is the original logarithmic convolution integral. -/
theorem deningerMeyerSourceConvolution_apply
    (g h : DeningerMeyerStrongLogTarget) (x : ℝ) :
    (deningerMeyerSourceConvolution g h).val x = ∫ t : ℝ, g.val t * h.val (x-t) := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have hf : 𝓕 (sourceSchwartz (deningerMeyerSourceConvolution g h)) =
      𝓕 (SchwartzMap.convolution B (sourceSchwartz g) (sourceSchwartz h)) := by
    rw [SchwartzMap.fourier_convolution]
    ext w
    change 𝓕 ((deningerMeyerSourceConvolution g h).val) w = 𝓕 g.val w * 𝓕 h.val w
    rw [← deningerMeyerStrongLogMellin_eq_fourier,
      ← deningerMeyerStrongLogMellin_eq_fourier,
      ← deningerMeyerStrongLogMellin_eq_fourier, deningerMeyerSourceConvolution_mellin]
  have he : sourceSchwartz (deningerMeyerSourceConvolution g h) =
      SchwartzMap.convolution B (sourceSchwartz g) (sourceSchwartz h) := by
    simpa using congrArg (fun f : SchwartzMap ℝ ℂ => 𝓕⁻ f) hf
  have hx := congrArg (fun f : SchwartzMap ℝ ℂ => f x) he
  rw [SchwartzMap.convolution_apply] at hx
  exact hx

theorem deningerMeyerSourceConvolution_comm (g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerSourceConvolution g h = deningerMeyerSourceConvolution h g := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  simp [mul_comm]

theorem deningerMeyerSourceConvolution_assoc (f g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerSourceConvolution (deningerMeyerSourceConvolution f g) h =
      deningerMeyerSourceConvolution f (deningerMeyerSourceConvolution g h) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  simp [mul_assoc]

/-- The product is genuinely bilinear on original sources. -/
def deningerMeyerSourceConvolutionLM :
    DeningerMeyerStrongLogTarget →ₗ[ℂ]
      DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget where
  toFun g :=
    { toFun := deningerMeyerSourceConvolution g
      map_add' := fun h k => by
        apply deningerMeyerStrongLogMellin_injective
        funext s
        simp [mul_add]
      map_smul' := fun c h => by
        apply deningerMeyerStrongLogMellin_injective
        funext s
        simp [mul_left_comm] }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply deningerMeyerStrongLogMellin_injective
    funext s
    simp [add_mul]
  map_smul' c g := by
    apply LinearMap.ext
    intro h
    apply deningerMeyerStrongLogMellin_injective
    funext s
    simp [mul_assoc]

@[simp] theorem deningerMeyerSourceConvolutionLM_apply
    (g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerSourceConvolutionLM g h = deningerMeyerSourceConvolution g h := rfl

/-- Every original boundary has an entire Xi quotient, without a growth assumption. -/
theorem deningerMeyerBoundary_entireQuotient (f : DeningerMeyerCap) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ s,
      deningerMeyerStrongLogMellin (deningerMeyerStrongLogSumLM f) s = xi s * H s := by
  obtain ⟨F, hF⟩ := deningerMeyerCenteredMellin_boundary_mem_XiRange f
  refine ⟨fun s => F (-I*(s-1/2)), F.property.comp (by fun_prop), ?_⟩
  intro s
  have hc : 1/2+I*(-I*(s-1/2)) = s := by ring_nf; rw [I_sq]; ring
  have he := congrArg (fun A : DeningerCompactOpenEntire => A (-I*(s-1/2))) hF
  change XiC (-I*(s-1/2))*F (-I*(s-1/2)) =
    deningerMeyerStrongLogMellin (deningerMeyerStrongLogSumLM f)
      (1/2+I*(-I*(s-1/2))) at he
  rw [XiC, mul_comm (-I*(s-1/2)) I, hc] at he
  exact he.symm

/-- The actual Poisson boundary range is a convolution ideal. -/
theorem deningerMeyerSourceConvolution_boundary
    (g : DeningerMeyerStrongLogTarget) (f : DeningerMeyerCap) :
    ∃ k : DeningerMeyerCap, deningerMeyerStrongLogSumLM k =
      deningerMeyerSourceConvolution g (deningerMeyerStrongLogSumLM f) := by
  obtain ⟨H, hH, he⟩ := deningerMeyerBoundary_entireQuotient f
  apply deningerMeyerXiDivision_has_cap _
    ((deningerMeyerStrongLogMellin_entireRegular g).differentiable.mul hH)
  intro s
  rw [deningerMeyerSourceConvolution_mellin, he]
  simp only [Pi.mul_apply]
  ring

end
end RHTower
