import GaloisForLFunctions.RHTower.L2FourierIntegralBridge

/-!
# Vector-valued `L²` Fourier integral bridge

Mathlib's unitary Fourier transform on `L²(ℝ;H)` is identified almost everywhere with the
classical Bochner Fourier integral whenever the chosen representative is integrable.  This is the
Hilbert-valued extension of the scalar corpus bridge and is needed to identify physical source
derivatives with terminal frequency forcing.
-/

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal BoundedContinuousFunction SchwartzMap

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If an `L²(ℝ;H)` representative is Bochner integrable, its unitary `L²` Fourier transform is
almost everywhere its classical vector-valued Fourier integral. -/
theorem l2_vector_fourier_coeFn_eq_l1_fourier_of_integrable
    (f : Lp H 2 (volume : Measure ℝ)) (hf : Integrable (f : ℝ → H)) :
    ((𝓕 f : Lp H 2 (volume : Measure ℝ)) : ℝ → H) =ᵐ[volume]
      (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hf).toLp f) : ℝ → H) := by
  let f1 : Lp H 1 (volume : Measure ℝ) :=
    (memLp_one_iff_integrable.mpr hf).toLp f
  let h : Lp H 2 (volume : Measure ℝ) := 𝓕 f
  let G : ℝ →ᵇ H := Real.Lp.fourierTransform f1
  have hh_loc : LocallyIntegrable (h : ℝ → H) volume :=
    (Lp.memLp h).locallyIntegrable (by norm_num)
  have hG_loc : LocallyIntegrable (G : ℝ → H) volume :=
    G.continuous.locallyIntegrable
  apply ae_eq_of_integral_contDiff_smul_eq hh_loc hG_loc
  intro g hg hsupp
  let gc : ℝ → ℂ := Complex.ofRealCLM ∘ g
  have hgc_supp : HasCompactSupport gc := hsupp.comp_left rfl
  have hgc_diff := Complex.ofRealCLM.contDiff.comp hg
  let psi : SchwartzMap ℝ ℂ := hgc_supp.toSchwartzMap hgc_diff
  have hdist := Lp.fourier_toTemperedDistribution_eq f
  have hdist_apply := congrArg (fun T : 𝓢'(ℝ, H) => T psi) hdist
  have hdistribution :
      ∫ x : ℝ, psi x • h x = ∫ x : ℝ, (𝓕 psi) x • f x := by
    simpa [h, Lp.toTemperedDistribution_apply, TemperedDistribution.fourier_apply]
      using hdist_apply.symm
  have hclassical :
      ∫ x : ℝ, psi x • G x = ∫ x : ℝ, (𝓕 psi) x • f x := by
    have hf1_int : Integrable (f1 : ℝ → H) := L1.integrable_coeFn f1
    have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (V := ℝ) (W := ℝ) (F := H) (e := Real.fourierChar)
      (μ := volume) (ν := volume) (L := innerₗ ℝ)
      (f := (psi : ℝ → ℂ)) (g := (f1 : ℝ → H))
      Real.continuous_fourierChar continuous_inner psi.integrable hf1_int
    have hpsi_fourier (x : ℝ) :
        VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
            (psi : ℝ → ℂ) x =
          (𝓕 psi) x := by
      rw [SchwartzMap.fourier_coe, Real.fourier_eq]
      rfl
    have hf_fourier_flip (x : ℝ) :
        VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ).flip
            (f1 : ℝ → H) x =
          𝓕 (f1 : ℝ → H) x := by
      rw [flip_innerₗ, Real.fourier_eq]
      rfl
    have hswap' :
        ∫ x : ℝ, (𝓕 psi) x • (f1 : ℝ → H) x =
          ∫ x : ℝ, psi x • G x := by
      simpa only [G, Real.Lp.fourierTransform_apply, hpsi_fourier,
        hf_fourier_flip] using hswap
    have hae : (fun x : ℝ => (𝓕 psi) x • (f1 : ℝ → H) x) =ᵐ[volume]
        fun x : ℝ => (𝓕 psi) x • f x := by
      filter_upwards [MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf)] with x hx
      have hx' : (f1 : ℝ → H) x = f x := by simpa [f1] using hx
      exact congrArg (fun y : H => (𝓕 psi) x • y) hx'
    exact hswap'.symm.trans (integral_congr_ae hae)
  simpa [psi, gc, h, G] using hdistribution.trans hclassical.symm

end RHTower

end
