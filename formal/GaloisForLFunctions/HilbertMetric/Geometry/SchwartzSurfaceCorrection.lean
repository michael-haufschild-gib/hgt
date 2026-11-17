import GaloisForLFunctions.HilbertMetric.Geometry.BonnetSurface
import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzInversion

/-!
# Schwartz displacement of a support surface

The support parametrization differs from the round sphere by a Schwartz
vector field. Its rational factor is a Bessel-potential multiplier.
Consequently the surface displacement, not only its support function,
extends smoothly and flatly through the missing stereographic pole.
-/

open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.SchwartzSurfaceCorrection
open GaloisForLFunctions.HTGeometry.GaussBonnet
open BonnetSupport BonnetSurface StereographicFrame SchwartzInversion
noncomputable section

private def dx (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap (ℝ × ℝ) ℝ :=
  SchwartzMap.evalCLM ℝ (ℝ × ℝ) ℝ (1, 0) (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) ℝ f)

private def dy (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap (ℝ × ℝ) ℝ :=
  SchwartzMap.evalCLM ℝ (ℝ × ℝ) ℝ (0, 1) (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) ℝ f)

private theorem fst_temperate : Function.HasTemperateGrowth (fun p : ℝ × ℝ => p.1) := by
  change Function.HasTemperateGrowth (ContinuousLinearMap.fst ℝ ℝ ℝ)
  fun_prop

private theorem snd_temperate : Function.HasTemperateGrowth (fun p : ℝ × ℝ => p.2) := by
  change Function.HasTemperateGrowth (ContinuousLinearMap.snd ℝ ℝ ℝ)
  fun_prop

/-- The inverse round denominator is a Bessel-potential multiplier in complex coordinates. -/
theorem inverseDenominator_temperate : Function.HasTemperateGrowth inverseDenominator := by
  have hw : Function.HasTemperateGrowth (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹) := by
    simpa only [Real.rpow_neg_one] using Function.hasTemperateGrowth_one_add_norm_sq_rpow ℂ (-1)
  have hc : Function.HasTemperateGrowth Complex.equivRealProdCLM.symm := by
    change Function.HasTemperateGrowth Complex.equivRealProdCLM.symm.toContinuousLinearMap
    fun_prop
  have he : inverseDenominator =
      (fun p : ℝ × ℝ => (1 + ‖Complex.equivRealProdCLM.symm p‖ ^ 2)⁻¹) := by
    funext p
    change (1 + p.1 ^ 2 + p.2 ^ 2)⁻¹ = (1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2)⁻¹
    rw [Complex.sq_norm, Complex.normSq_apply]
    congr 1
    ring
  rw [he]
  exact hw.comp hc

private def e₁ : Space := !₂[1, 0, 0]
private def e₂ : Space := !₂[0, 1, 0]
private def e₃ : Space := !₂[0, 0, 1]

private def position (p : ℝ × ℝ) : Space := p.1 • e₁ + p.2 • e₂ - e₃

private theorem position_temperate : Function.HasTemperateGrowth position := by
  have hf := fst_temperate
  have hs := snd_temperate
  unfold position
  fun_prop

private def scalarRemainder (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap (ℝ × ℝ) ℝ :=
  f - SchwartzMap.smulLeftCLM ℝ Prod.fst (dx f) - SchwartzMap.smulLeftCLM ℝ Prod.snd (dy f)

private def vectorScale (v : Space) (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap (ℝ × ℝ) Space :=
  SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space)
    (Function.HasTemperateGrowth.const v) f

/-- The exact vector displacement as an actual Schwartz map. -/
def displacement (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap (ℝ × ℝ) Space :=
  vectorScale e₁ ((1 / 2 : ℝ) • dx f) + vectorScale e₂ ((1 / 2 : ℝ) • dy f) +
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space)
      position_temperate (SchwartzMap.smulLeftCLM ℝ inverseDenominator (scalarRemainder f))

theorem displacement_apply (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) :
    displacement f p = correction f p := by
  have hx : dx f p = px f p := rfl
  have hy : dy f p = py f p := rfl
  simp only [displacement, add_apply, vectorScale, SchwartzMap.bilinLeftCLM_apply,
    ContinuousLinearMap.lsmul_apply, smul_apply, smul_eq_mul,
    SchwartzMap.smulLeftCLM_apply_apply inverseDenominator_temperate,
    scalarRemainder, sub_apply, SchwartzMap.smulLeftCLM_apply_apply fst_temperate,
    SchwartzMap.smulLeftCLM_apply_apply snd_temperate, hx, hy]
  ext i
  fin_cases i <;> simp [correction, position, e₁, e₂, e₃, inverseDenominator,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, div_eq_mul_inv] <;> ring

/-- The actual surface parametrization is the round sphere plus this Schwartz displacement. -/
theorem surface_displacement (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (p : ℝ × ℝ) :
    surface (support f ε) p = normal p + ε • displacement f p := by
  rw [displacement_apply]
  exact surface_eq_normal_add (f.smooth ⊤) ε p

/-- The displacement in complex plane coordinates. -/
def complexDisplacement (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap ℂ Space :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ Complex.equivRealProdCLM (displacement f)

theorem complexDisplacement_apply (f : SchwartzMap (ℝ × ℝ) ℝ) (z : ℂ) :
    complexDisplacement f z = displacement f (z.re, z.im) := rfl

/-- The vector displacement has a smooth extension through inversion. -/
theorem inverted_displacement_smooth (f : SchwartzMap (ℝ × ℝ) ℝ) :
    ContDiff ℝ ∞ (kelvin (complexDisplacement f)) := kelvin_contDiff _

/-- Every derivative of the extended surface displacement is zero at the missing pole. -/
theorem inverted_displacement_flat (f : SchwartzMap (ℝ × ℝ) ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (kelvin (complexDisplacement f)) 0 = 0 :=
  kelvin_iteratedFDeriv_zero n _

#print axioms inverseDenominator_temperate
#print axioms displacement_apply
#print axioms surface_displacement
#print axioms inverted_displacement_smooth
#print axioms inverted_displacement_flat
end
end GaloisForLFunctions.HilbertMetric.Geometry.SchwartzSurfaceCorrection
