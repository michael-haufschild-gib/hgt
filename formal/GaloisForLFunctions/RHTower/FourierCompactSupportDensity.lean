import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Fourier transforms of test functions are dense in `L²(ℝ)`

If `G ∈ L²(ℝ)` satisfies `∫ 𝓕g · G = 0` for every smooth compactly supported `g`, then `G = 0` almost
everywhere: `conj 𝓕g = 𝓕(conj g(−·))`, so `G` is orthogonal to the Fourier transforms of all test
functions, hence `𝓕⁻G` is orthogonal to the dense set of test functions (Plancherel).
-/

open MeasureTheory Complex
open scoped FourierTransform ComplexConjugate ContDiff InnerProductSpace

namespace GaloisForLFunctions.RHTower.Kuznetsov

noncomputable section

/-- `conj (𝓕h ξ) = 𝓕(v ↦ conj (h(−v))) ξ`. -/
theorem conj_fourier_eq (h : ℝ → ℂ) (ξ : ℝ) :
    conj (𝓕 h ξ) = 𝓕 (fun v => conj (h (-v))) ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  rw [← integral_neg_eq_self (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * ξ) * I) •
    conj (h (-v)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, map_mul, neg_neg, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I]
  congr 2
  push_cast
  ring

/-- **Density of Fourier transforms of test functions.** -/
theorem ae_eq_zero_of_integral_fourier_mul_eq_zero {G : ℝ → ℂ} (hG : MemLp G 2)
    (h : ∀ g : ℝ → ℂ, HasCompactSupport g → ContDiff ℝ ∞ g → ∫ ξ, 𝓕 g ξ * G ξ = 0) :
    G =ᵐ[volume] 0 := by
  set Gl : Lp ℂ 2 (volume : Measure ℝ) := hG.toLp G
  have hdense := MeasureTheory.Lp.dense_hasCompactSupport_contDiff (F := ℂ) (E := ℝ)
    (μ := (volume : Measure ℝ)) (p := 2) ENNReal.ofNat_ne_top
  have horth : ∀ f ∈ {f : Lp ℂ 2 (volume : Measure ℝ) | ∃ g : ℝ → ℂ, (f : ℝ → ℂ) =ᵐ[volume] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ∞ g}, ⟪f, 𝓕⁻ Gl⟫_ℂ = 0 := by
    rintro f ⟨g, hfg, hgc, hgs⟩
    set gS := hgc.toSchwartzMap hgs
    have hf : f = gS.toLp 2 volume := by
      refine Lp.ext (hfg.trans ?_)
      exact (gS.coeFn_toLp 2 volume).symm
    rw [← Lp.inner_fourier_eq, FourierTransform.fourier_fourierInv_eq, hf, SchwartzMap.toLp_fourier_eq,
      L2.inner_def]
    have hcg : HasCompactSupport (fun v => conj (g (-v))) :=
      (hgc.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (map_zero (starRingEnd ℂ))
    have hsg : ContDiff ℝ ∞ (fun v => conj (g (-v))) :=
      (Complex.conjCLE.contDiff.comp (hgs.comp contDiff_neg))
    rw [← h _ hcg hsg]
    refine integral_congr_ae ?_
    filter_upwards [(𝓕 gS).coeFn_toLp 2 volume, hG.coeFn_toLp] with ξ h1 h2
    rw [h1, h2, RCLike.inner_apply, SchwartzMap.fourier_coe, ← conj_fourier_eq, mul_comm]
    rfl
  have hzero : 𝓕⁻ Gl = 0 := hdense.eq_zero_of_inner_right ℂ horth
  have hGl : Gl = 0 := by
    have := congrArg (fun X => 𝓕 X) hzero
    simpa [FourierTransform.fourier_fourierInv_eq] using this
  have hcoe := hG.coeFn_toLp
  rw [show hG.toLp G = Gl from rfl, hGl] at hcoe
  exact hcoe.symm.trans (Lp.coeFn_zero ℂ 2 volume)

end

end GaloisForLFunctions.RHTower.Kuznetsov
