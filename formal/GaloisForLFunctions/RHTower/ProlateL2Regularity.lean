import GaloisForLFunctions.RHTower.ProlateL2Family
import GaloisForLFunctions.RHTower.SlepianBandCommutation

/-!
# From `L²` eigenvectors to pointwise prolate eigenfunctions

An eigenvector of the band operator is an `L²` class, but the band operator smooths: since the kernel
is continuous and bounded, the function

```text
Phi(x) = nu⁻¹ ∫ sinc_c(x - y) psi(y) dy
```

is continuous on all of `ℝ`, agrees with `psi` almost everywhere on the band, and satisfies the
*pointwise* eigenrelation of the corpus's `bandTransform` everywhere:

```text
bandTransform c Phi x = nu · Phi x     for every real x.
```

That is the dictionary entry which carries a statement about the Hilbert-space operator over to the
classical prolate functions, on which the differential (Slepian) machinery acts.  The one analytic
input is the global bound `|sinc_c(u)| ≤ |c|/pi`, proved here from `|sin t| ≤ |t|`; it makes the
dominated-continuity argument uniform in `x` over all of `ℝ`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **The smoothed sinc profile is globally bounded** by `|c|/pi`. -/
theorem abs_sincSmooth_le (c u : ℝ) : |sincSmooth c u| ≤ |c| / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases eq_or_ne u 0 with hu | hu
  · subst hu
    rw [sincSmooth_zero, abs_div, abs_of_pos hpi]
  · rw [sincSmooth_eq_off hu, sincScalar, abs_div, abs_mul, abs_of_pos hpi]
    rw [div_le_div_iff₀ (by positivity) hpi]
    have hsin : |Real.sin (c * u)| ≤ |c * u| := Real.abs_sin_le_abs
    have habs : |c * u| = |c| * |u| := abs_mul c u
    have hu' : (0 : ℝ) < |u| := abs_pos.mpr hu
    nlinarith [hsin, hpi.le, abs_nonneg c]

/-- The continuous extension of an `L²` eigenvector by its own band integral. -/
def eigenExtension (c ν : ℝ) (ψ : RealIntervalL2 (-1 : ℝ) 1) : ℝ → ℝ :=
  fun x => ν⁻¹ * ∫ y : ClosedInterval (-1 : ℝ) 1, sincKernelSmooth c x (y : ℝ) * ψ y ∂volume

/-- **The extension is continuous on all of `ℝ`.**  Dominated continuity with the uniform bound
`|c|/pi · |psi|`. -/
theorem continuous_eigenExtension (c ν : ℝ) (ψ : RealIntervalL2 (-1 : ℝ) 1) :
    Continuous (eigenExtension c ν ψ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hψ : Integrable (ψ : ClosedInterval (-1 : ℝ) 1 → ℝ)
      (volume : Measure (ClosedInterval (-1 : ℝ) 1)) := integrable_of_realIntervalL2 ψ
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable
      (fun y : ClosedInterval (-1 : ℝ) 1 => sincKernelSmooth c x (y : ℝ) * (ψ y : ℝ))
      (volume : Measure (ClosedInterval (-1 : ℝ) 1)) := by
    intro x
    refine AEStronglyMeasurable.mul ?_ (Lp.aestronglyMeasurable ψ)
    refine Continuous.aestronglyMeasurable ?_
    have h : Continuous fun y : ClosedInterval (-1 : ℝ) 1 => x - (y : ℝ) := by fun_prop
    simpa [sincKernelSmooth, Function.comp_def] using (contDiff_sincSmooth c).continuous.comp h
  have hbound : ∀ x : ℝ, ∀ᵐ (y : ClosedInterval (-1 : ℝ) 1)
      ∂(volume : Measure (ClosedInterval (-1 : ℝ) 1)),
      ‖sincKernelSmooth c x (y : ℝ) * (ψ y : ℝ)‖ ≤ |c| / Real.pi * ‖(ψ y : ℝ)‖ := by
    intro x
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_sincSmooth_le c (x - (y : ℝ))) (abs_nonneg _)
  have hbint : Integrable (fun y : ClosedInterval (-1 : ℝ) 1 => |c| / Real.pi * ‖(ψ y : ℝ)‖)
      (volume : Measure (ClosedInterval (-1 : ℝ) 1)) := hψ.norm.const_mul _
  have hcont : ∀ᵐ (y : ClosedInterval (-1 : ℝ) 1)
      ∂(volume : Measure (ClosedInterval (-1 : ℝ) 1)),
      Continuous fun x : ℝ => sincKernelSmooth c x (y : ℝ) * (ψ y : ℝ) := by
    refine Filter.Eventually.of_forall fun y => ?_
    have h : Continuous fun x : ℝ => x - (y : ℝ) := by fun_prop
    have h2 : Continuous fun x : ℝ => sincSmooth c (x - (y : ℝ)) :=
      (contDiff_sincSmooth c).continuous.comp h
    have h3 : Continuous fun x : ℝ => sincSmooth c (x - (y : ℝ)) * (ψ y : ℝ) :=
      h2.mul continuous_const
    simpa [sincKernelSmooth] using h3
  exact continuous_const.mul (continuous_of_dominated hmeas hbound hbint hcont)

/-- **The extension represents the eigenvector.** -/
theorem eigenExtension_ae_eq {c ν : ℝ} (hν : ν ≠ 0) {ψ : RealIntervalL2 (-1 : ℝ) 1}
    (heig : bandOperatorL2 c ψ = ν • ψ) :
    (ψ : ClosedInterval (-1 : ℝ) 1 → ℝ) =ᵐ[volume]
      fun x => eigenExtension c ν ψ (x : ℝ) := by
  have hcoe : ((bandOperatorL2 c ψ : RealIntervalL2 (-1 : ℝ) 1) :
      ClosedInterval (-1 : ℝ) 1 → ℝ) =ᵐ[volume] fun x => ν * (ψ x : ℝ) := by
    rw [heig]
    filter_upwards [Lp.coeFn_smul ν ψ] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]
  filter_upwards [bandOperatorL2_coeFn c ψ, hcoe] with x h1 h2
  rw [h1] at h2
  rw [eigenExtension, h2]
  field_simp

/-- Integrals over the interval subtype are interval integrals. -/
theorem integral_subtype_unit (G : ℝ → ℝ) :
    (∫ y : ClosedInterval (-1 : ℝ) 1, G (y : ℝ) ∂volume) = ∫ y in (-1 : ℝ)..1, G y := by
  rw [integral_subtype measurableSet_Icc G,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- **The pointwise prolate eigenrelation.**  The continuous extension of an `L²` eigenvector of the
band operator satisfies the corpus's function-level band eigenrelation at every real point. -/
theorem bandTransform_eigenExtension {c ν : ℝ} (hν : ν ≠ 0) {ψ : RealIntervalL2 (-1 : ℝ) 1}
    (heig : bandOperatorL2 c ψ = ν • ψ) (x : ℝ) :
    bandTransform c (eigenExtension c ν ψ) x = ν * eigenExtension c ν ψ x := by
  have hcont := continuous_eigenExtension c ν ψ
  have hswap : (∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * eigenExtension c ν ψ y)
      = ∫ y : ClosedInterval (-1 : ℝ) 1,
          sincKernelSmooth c x (y : ℝ) * eigenExtension c ν ψ (y : ℝ) ∂volume :=
    (integral_subtype_unit (fun y => sincKernelSmooth c x y * eigenExtension c ν ψ y)).symm
  have hrepl : (∫ y : ClosedInterval (-1 : ℝ) 1,
        sincKernelSmooth c x (y : ℝ) * eigenExtension c ν ψ (y : ℝ) ∂volume)
      = ∫ y : ClosedInterval (-1 : ℝ) 1, sincKernelSmooth c x (y : ℝ) * (ψ y : ℝ) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [eigenExtension_ae_eq hν heig] with y hy
    rw [hy]
  rw [bandTransform, hswap, hrepl, eigenExtension]
  field_simp

end GaloisForLFunctions.RHTower

end
