/-
BRIDGE (classical harmonic-analysis infrastructure).

The unitary Fourier transform on `L²(ℝ)` agrees almost everywhere with the classical Fourier
integral whenever the chosen `L²` representative is integrable.  The proof compares the two
tempered distributions and uses local uniqueness against compactly supported smooth tests.
-/
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section

open MeasureTheory
open FourierTransform
open scoped ENNReal BoundedContinuousFunction SchwartzMap

namespace RHTower

/-- If an `L²(ℝ)` representative is integrable, then mathlib's unitary `L²` Fourier transform is
almost everywhere equal to its classical `L¹` Fourier integral. -/
theorem l2_fourier_coeFn_eq_l1_fourier_of_integrable
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : Integrable (f : ℝ → ℂ)) :
    ((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hf).toLp f) : ℝ → ℂ) := by
  let f1 : Lp ℂ 1 (volume : Measure ℝ) :=
    (memLp_one_iff_integrable.mpr hf).toLp f
  let h : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 f
  let G : ℝ →ᵇ ℂ := Real.Lp.fourierTransform f1
  have hh_loc : LocallyIntegrable (h : ℝ → ℂ) volume :=
    (Lp.memLp h).locallyIntegrable (by norm_num)
  have hG_loc : LocallyIntegrable (G : ℝ → ℂ) volume :=
    G.continuous.locallyIntegrable
  apply ae_eq_of_integral_contDiff_smul_eq hh_loc hG_loc
  intro g hg hsupp
  let gc : ℝ → ℂ := Complex.ofRealCLM ∘ g
  have hgc_supp : HasCompactSupport gc := hsupp.comp_left rfl
  have hgc_diff := Complex.ofRealCLM.contDiff.comp hg
  let psi : SchwartzMap ℝ ℂ := hgc_supp.toSchwartzMap hgc_diff
  have hdist := Lp.fourier_toTemperedDistribution_eq f
  have hdist_apply := congrArg (fun T : 𝓢'(ℝ, ℂ) => T psi) hdist
  have hdistribution :
      ∫ x : ℝ, psi x * h x = ∫ x : ℝ, (𝓕 psi) x * f x := by
    simpa [h, mul_comm] using hdist_apply.symm
  have hclassical :
      ∫ x : ℝ, G x * psi x = ∫ x : ℝ, f x * (𝓕 psi) x := by
    have hf1_int : Integrable (f1 : ℝ → ℂ) := L1.integrable_coeFn f1
    have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (V := ℝ) (W := ℝ) (F := ℂ) (e := Real.fourierChar)
      (μ := volume) (ν := volume) (L := innerₗ ℝ)
      (f := (f1 : ℝ → ℂ)) (g := (psi : ℝ → ℂ))
      Real.continuous_fourierChar continuous_inner hf1_int psi.integrable
    have hswap' :
        ∫ x : ℝ, G x * psi x = ∫ x : ℝ, (f1 : ℝ → ℂ) x * (𝓕 psi) x := by
      simpa [G, Real.Lp.fourierTransform_apply, smul_eq_mul] using hswap
    calc
      _ = ∫ x : ℝ, (f1 : ℝ → ℂ) x * (𝓕 psi) x := hswap'
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf)] with x hx
        have hx' : (f1 : ℝ → ℂ) x = f x := by simpa [f1] using hx
        rw [hx']
  have hclassical' :
      ∫ x : ℝ, (𝓕 psi) x * f x = ∫ x : ℝ, G x * psi x := by
    simpa [mul_comm] using hclassical.symm
  simpa [psi, gc, h, G, mul_comm] using hdistribution.trans hclassical'

end RHTower
