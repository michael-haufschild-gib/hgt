import GaloisForLFunctions.HTGeometry.FiniteEvaluationPacket
import GaloisForLFunctions.RHTower.SmoothAFEGaussianKernel
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.LinearIndependent.Defs



open Filter Topology Finset Complex
noncomputable section
namespace RHTower

private theorem entire_zero_of_imaginary_axis {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hzero : ∀ t : ℝ, f ((t : ℂ) * I) = 0) : f = 0 := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ) * I) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · apply tendsto_nhdsWithin_of_tendsto_nhds
      simpa using (show ContinuousAt (fun t : ℝ => (t : ℂ) * I) 0 by fun_prop).tendsto
    · apply eventually_nhdsWithin_iff.mpr
      exact Eventually.of_forall fun t ht h => ht (by simpa using congrArg Complex.im h)
  have hz : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = (0 : ℂ → ℂ) z :=
    ht.frequently (Frequently.of_forall hzero)
  exact hf.eq_of_frequently_eq analyticOnNhd_const hz

/-- Distinct Gaussian Mellin translates have no nontrivial relation along the imaginary axis. -/
theorem gaussianCofactorMode_coefficients_eq_zero {J : ℕ} (s : Fin J → ℂ)
    (hs : ∀ j, 0 < (s j).re) (hinj : Function.Injective s) (c : Fin J → ℂ)
    (hzero : ∀ t : ℝ, ∑ j, c j * smoothAFEGaussianKernel (s j + (t : ℂ) * I) = 0) :
    ∀ j, c j = 0 := by
  classical
  let F : ℂ → ℂ := fun z => ∑ j, c j * Complex.exp ((s j + z) ^ 2) *
    ∏ k ∈ univ.erase j, (s k + z)
  have hF : AnalyticOnNhd ℂ F Set.univ := by
    apply analyticOnNhd_univ_iff_differentiable.mpr
    dsimp only [F]
    fun_prop
  have hline (t : ℝ) : F ((t : ℂ) * I) = 0 := by
    have hden (j : Fin J) : s j + (t : ℂ) * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      have hp := hs j
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
        Complex.zero_re] at hre
      linarith
    calc
      _ = ∑ j, (c j * smoothAFEGaussianKernel (s j + (t : ℂ) * I)) *
          ∏ k, (s k + (t : ℂ) * I) := by
        apply sum_congr rfl
        intro j _
        rw [← mul_prod_erase univ (fun k => s k + (t : ℂ) * I) (mem_univ j)]
        unfold smoothAFEGaussianKernel
        field_simp [hden j]
      _ = 0 := by rw [← sum_mul, hzero, zero_mul]
  have hident := entire_zero_of_imaginary_axis hF hline
  intro j
  have hvalue : F (-s j) = c j * ∏ k ∈ univ.erase j, (s k - s j) := by
    dsimp only [F]
    rw [sum_eq_single j]
    · simp only [add_neg_cancel, zero_pow (by norm_num : 2 ≠ 0), Complex.exp_zero, mul_one,
        sub_eq_add_neg]
    · intro k _ hkj
      have hz : (∏ i ∈ univ.erase k, (s i + -s j)) = 0 :=
        prod_eq_zero (by simp [hkj.symm] : j ∈ univ.erase k) (by simp)
      rw [hz, mul_zero]
    · simp
  have hprod : (∏ k ∈ univ.erase j, (s k - s j)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (fun h => (mem_erase.mp hk).1 (hinj h))
  have hz := congrFun hident (-s j)
  rw [hvalue] at hz
  exact (mul_eq_zero.mp hz).resolve_right hprod

/-- The Gaussian cofactor response functions at distinct right-half-plane nodes are linearly independent. -/
theorem linearIndependent_gaussianCofactorModes {J : ℕ} (s : Fin J → ℂ)
    (hs : ∀ j, 0 < (s j).re) (hinj : Function.Injective s) :
    LinearIndependent ℂ (fun j => fun t : ℝ => smoothAFEGaussianKernel (s j + (t : ℂ) * I)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  apply gaussianCofactorMode_coefficients_eq_zero s hs hinj c
  intro t
  have h := congrFun hc t
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h

/-- The full Gaussian response modes span the finite node space. -/
theorem span_gaussianCofactorModes_eq_top {J : ℕ} (s : Fin J → ℂ)
    (hs : ∀ j, 0 < (s j).re) (hinj : Function.Injective s) :
    Submodule.span ℂ (Set.range (fun t : ℝ =>
      fun j => smoothAFEGaussianKernel (s j + (t : ℂ) * I))) = ⊤ :=
  GaloisForLFunctions.HTGeometry.span_evaluationVectors_eq_top _
    (linearIndependent_gaussianCofactorModes s hs hinj)

/-- Finitely many coherent twists give a nonsingular Gaussian response matrix. -/
theorem exists_fullRank_gaussianCofactorModes {J : ℕ} (s : Fin J → ℂ)
    (hs : ∀ j, 0 < (s j).re) (hinj : Function.Injective s) :
    ∃ t : Fin J → ℝ,
      (Matrix.of (fun i j => smoothAFEGaussianKernel (s j + (t i : ℂ) * I))).det ≠ 0 := by
  obtain ⟨t, ht⟩ := GaloisForLFunctions.HTGeometry.exists_fullRank_evaluation_packet _
    (linearIndependent_gaussianCofactorModes s hs hinj)
  exact ⟨t, ((Matrix.isUnit_iff_isUnit_det _).mp ht).ne_zero⟩

end RHTower
