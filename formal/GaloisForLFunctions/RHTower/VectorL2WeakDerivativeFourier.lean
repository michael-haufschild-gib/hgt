import GaloisForLFunctions.RHTower.VectorL2FourierIntegralBridge
import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# Vector-valued `L²` weak derivatives under Fourier transform

For Hilbert-valued `L²` functions, a distributional derivative is carried by the exact Fourier
multiplier `2πiξ`.  This module requires neither pointwise differentiability nor `L¹` hypotheses.
It also proves that dividing the derivative transform by `2πiξ` recovers the primitive transform
almost everywhere, with the origin removed by the null-singleton property.
-/

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap LineDeriv

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem locallyIntegrable_fourierFrequency_smul
    (f : Lp H 2 (volume : Measure ℝ)) :
    LocallyIntegrable
      (fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ) •
        ((𝓕 f : Lp H 2 (volume : Measure ℝ)) : ℝ → H) ξ) volume := by
  let Fhat : Lp H 2 (volume : Measure ℝ) := 𝓕 f
  have hF_loc : LocallyIntegrable (Fhat : ℝ → H) volume :=
    (Lp.memLp Fhat).locallyIntegrable (by norm_num)
  intro x
  let K : Set ℝ := Set.Icc (x - 1) (x + 1)
  have hK_nhds : K ∈ nhds x := by
    have hIoo : Set.Ioo (x - 1) (x + 1) ∈ nhds x :=
      Ioo_mem_nhds (by linarith) (by linarith)
    exact Filter.mem_of_superset hIoo Set.Ioo_subset_Icc_self
  refine ⟨K, hK_nhds, ?_⟩
  have hscalar : MemLp (fun y : ℝ => (2 * Real.pi * Complex.I) * y) ∞
      (volume.restrict K) := by
    refine memLp_top_of_bound
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_id))
        |>.aestronglyMeasurable.restrict)
      (‖2 * Real.pi * Complex.I‖ * (|x| + 1)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [norm_mul, Complex.norm_real]
    gcongr
    have : |y - x| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    calc
      |y| = |x + (y - x)| := by ring_nf
      _ ≤ |x| + |y - x| := abs_add_le _ _
      _ ≤ |x| + 1 := by linarith
  exact (hF_loc.integrableOn_isCompact isCompact_Icc).smul_of_top_right hscalar

/-- An `L²` distributional derivative is transformed by the exact Fourier multiplier
`2πiξ`, without pointwise differentiability or `L¹` hypotheses. -/
theorem l2_fourier_weakDerivative_ae
    (f g : Lp H 2 (volume : Measure ℝ))
    (hweak : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, H)) = (g : 𝓢'(ℝ, H))) :
    ((𝓕 g : Lp H 2 (volume : Measure ℝ)) : ℝ → H) =ᵐ[volume]
      fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ) •
        ((𝓕 f : Lp H 2 (volume : Measure ℝ)) : ℝ → H) ξ := by
  let Fhat : Lp H 2 (volume : Measure ℝ) := 𝓕 f
  let Ghat : Lp H 2 (volume : Measure ℝ) := 𝓕 g
  have hG_loc : LocallyIntegrable (Ghat : ℝ → H) volume :=
    (Lp.memLp Ghat).locallyIntegrable (by norm_num)
  have hmul_loc : LocallyIntegrable
      (fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ) • (Fhat : ℝ → H) ξ) volume := by
    simpa [Fhat] using locallyIntegrable_fourierFrequency_smul f
  apply ae_eq_of_integral_contDiff_smul_eq hG_loc hmul_loc
  intro φ hφ hsupp
  let φc : ℝ → ℂ := Complex.ofRealCLM ∘ φ
  have hφc_supp : HasCompactSupport φc := hsupp.comp_left rfl
  have hφc_diff : ContDiff ℝ (⊤ : ℕ∞) φc := Complex.ofRealCLM.contDiff.comp hφ
  let ψ : SchwartzMap ℝ ℂ := hφc_supp.toSchwartzMap hφc_diff
  have hdist :
      𝓕 (g : 𝓢'(ℝ, H)) =
        (2 * Real.pi * Complex.I) •
          TemperedDistribution.smulLeftCLM H (fun ξ : ℝ => inner ℝ ξ 1)
            (𝓕 (f : 𝓢'(ℝ, H))) := by
    rw [← hweak]
    exact TemperedDistribution.fourier_lineDerivOp_eq (f : 𝓢'(ℝ, H)) 1
  have happ := congrArg (fun T : 𝓢'(ℝ, H) => T ψ) hdist
  rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
      MeasureTheory.Lp.fourier_toTemperedDistribution_eq] at happ
  have hψ (x : ℝ) : ψ x = (φ x : ℂ) := rfl
  have hsmul (x : ℝ) :
      ((SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => (ξ : ℂ))) ψ) x =
        (x : ℂ) * φ x := by
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (by fun_prop : Function.HasTemperateGrowth (fun ξ : ℝ => (ξ : ℂ)))]
    rw [hψ]
    exact smul_eq_mul _ _
  have happ' :
      ∫ x : ℝ, φ x • (Ghat : ℝ → H) x =
        (2 * Real.pi * Complex.I) •
          ∫ x : ℝ, ((x : ℂ) * (φ x : ℂ)) • (Fhat : ℝ → H) x := by
    simpa [Ghat, Fhat, ψ, φc, MeasureTheory.Lp.toTemperedDistribution_apply,
      TemperedDistribution.smulLeftCLM_apply_apply,
      hψ, hsmul, smul_smul, mul_comm] using happ
  calc
    ∫ x : ℝ, φ x • (Ghat : ℝ → H) x =
        (2 * Real.pi * Complex.I) •
          ∫ x : ℝ, ((x : ℂ) * (φ x : ℂ)) • (Fhat : ℝ → H) x := happ'
    _ = ∫ x : ℝ, (2 * Real.pi * Complex.I) •
          (((x : ℂ) * (φ x : ℂ)) • (Fhat : ℝ → H) x) := by
      rw [MeasureTheory.integral_smul]
    _ = ∫ x : ℝ, φ x •
          ((2 * Real.pi * Complex.I * x) • (Fhat : ℝ → H) x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      module

/-- Dividing the Fourier transform of an `L²` weak derivative by `2πiξ` recovers the Fourier
transform of its primitive almost everywhere; the inverse-zero convention at `ξ = 0` is harmless. -/
theorem l2_roughPrimitiveForcing_eq_fourier_ae
    (f g : Lp H 2 (volume : Measure ℝ))
    (hweak : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, H)) = (g : 𝓢'(ℝ, H))) :
    (fun ξ : ℝ => (((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ξ : ℂ))⁻¹) •
        ((𝓕 g : Lp H 2 (volume : Measure ℝ)) : ℝ → H) ξ) =ᵐ[volume]
      ((𝓕 f : Lp H 2 (volume : Measure ℝ)) : ℝ → H) := by
  have hderiv := l2_fourier_weakDerivative_ae f g hweak
  filter_upwards [hderiv, (volume : Measure ℝ).ae_ne 0] with ξ hξ hξ0
  rw [hξ, smul_smul]
  have hm : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ξ : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero) ?_
    · exact_mod_cast Real.pi_ne_zero
    · exact_mod_cast hξ0
  rw [inv_mul_cancel₀ hm, one_smul]

end RHTower

end
