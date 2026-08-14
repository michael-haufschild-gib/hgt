import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Fourier uniqueness on `L¹`

An integrable function whose Fourier transform vanishes identically is almost everywhere zero.
Mathlib has the inversion formula only at continuity points, so the statement is obtained by
mollification: convolving with a normalized bump gives a continuous integrable function whose
Fourier transform is the product of the two transforms, hence zero, hence — by inversion — the
convolution itself is zero; and a normalized bump family converges to the identity almost
everywhere on locally integrable functions.

* `HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero`;
* `HTGeometry.ae_eq_of_fourierIntegral_eq`.
-/

open MeasureTheory Filter Convolution ContinuousLinearMap
open scoped FourierTransform Topology

namespace HTGeometry

/-- The mollifier family used for the uniqueness theorem. -/
noncomputable def uniqBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / (n + 2)
  rOut := 2 / (n + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [div_lt_div_iff_of_pos_right hn]
    norm_num

theorem tendsto_uniqBump_rOut : Tendsto (fun n : ℕ => (uniqBump n).rOut) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    exact Tendsto.const_div_atTop hcast 2
  exact h

theorem uniqBump_ratio (n : ℕ) : (uniqBump n).rOut ≤ 2 * (uniqBump n).rIn := by
  show 2 / ((n : ℝ) + 2) ≤ 2 * (1 / ((n : ℝ) + 2))
  rw [mul_one_div]

/-- **Fourier uniqueness on `L¹`.**  An integrable function with vanishing Fourier transform is
almost everywhere zero. -/
theorem ae_eq_zero_of_fourierIntegral_eq_zero {g : ℝ → ℂ} (hg : Integrable g)
    (h : ∀ x : ℝ, 𝓕 g x = 0) : g =ᵐ[volume] 0 := by
  classical
  have hloc : LocallyIntegrable g volume := hg.locallyIntegrable
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure ℝ)) (φ := uniqBump) (l := atTop) (K := 2)
    tendsto_uniqBump_rOut (Eventually.of_forall uniqBump_ratio) hloc
  have hzero : ∀ (n : ℕ) (x : ℝ),
      ((uniqBump n).normed (volume : Measure ℝ)
        ⋆[lsmul ℝ ℝ, (volume : Measure ℝ)] g) x = 0 := by
    intro n x
    set psi : ℝ → ℝ := (uniqBump n).normed (volume : Measure ℝ) with hpsi
    set psic : ℝ → ℂ := fun t => ((psi t : ℝ) : ℂ) with hpsic
    have hpsiInt : Integrable psi (volume : Measure ℝ) := by
      rw [hpsi]
      exact (uniqBump n).integrable_normed
    have hpsicInt : Integrable psic volume := hpsiInt.ofReal
    have hpsicCont : Continuous psic := by
      have hc : Continuous psi := by
        rw [hpsi]
        exact (uniqBump n).continuous_normed (μ := (volume : Measure ℝ))
      exact Complex.continuous_ofReal.comp hc
    have hpsicCS : HasCompactSupport psic := by
      have hcs : HasCompactSupport psi := by
        rw [hpsi]
        exact (uniqBump n).hasCompactSupport_normed (μ := (volume : Measure ℝ))
      exact hcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    have hEq : (psi ⋆[lsmul ℝ ℝ, (volume : Measure ℝ)] g) x
        = (psic ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] g) x := by
      rw [convolution, convolution]
      refine integral_congr_ae (.of_forall fun t => ?_)
      simp only [lsmul_apply, ContinuousLinearMap.mul_apply']
      rw [hpsic, Complex.real_smul]
    have hcont : Continuous (psic ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] g) :=
      hpsicCS.continuous_convolution_left _ hpsicCont hloc
    have hint : Integrable (psic ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] g) volume :=
      hpsicInt.integrable_convolution _ hg
    have hFzero : ∀ ξ : ℝ,
        𝓕 (psic ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] g) ξ = 0 := by
      intro ξ
      rw [Real.fourier_mul_convolution_eq hpsicInt hg ξ, h ξ, mul_zero]
    have hFint : Integrable (𝓕 (psic ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] g))
        volume := by
      have : (𝓕 (psic ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] g))
          = fun _ : ℝ => (0 : ℂ) := funext hFzero
      rw [this]
      exact integrable_zero _ _ _
    have hinv := hcont.fourierInv_fourier_eq hint hFint
    have hFfun : (𝓕 (psic ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] g))
        = fun _ : ℝ => (0 : ℂ) := funext hFzero
    rw [hFfun] at hinv
    have hzeroInv : (𝓕⁻ fun _ : ℝ => (0 : ℂ)) = fun _ : ℝ => (0 : ℂ) := by
      funext y
      rw [Real.fourierInv_eq]
      simp
    rw [hzeroInv] at hinv
    rw [hEq, ← hinv]
  filter_upwards [hae] with x hx
  have hconst : (fun n : ℕ => ((uniqBump n).normed (volume : Measure ℝ)
      ⋆[lsmul ℝ ℝ, (volume : Measure ℝ)] g) x) = fun _ : ℕ => (0 : ℂ) := funext fun n => hzero n x
  rw [hconst] at hx
  exact (tendsto_nhds_unique tendsto_const_nhds hx).symm

/-- Two integrable functions with the same Fourier transform agree almost everywhere. -/
theorem ae_eq_of_fourierIntegral_eq {g₁ g₂ : ℝ → ℂ} (hg₁ : Integrable g₁) (hg₂ : Integrable g₂)
    (h : ∀ x : ℝ, 𝓕 g₁ x = 𝓕 g₂ x) : g₁ =ᵐ[volume] g₂ := by
  have hF : ∀ x : ℝ, 𝓕 (g₁ - g₂) x = 0 := by
    intro x
    have hsplit : 𝓕 (g₁ - g₂) x = 𝓕 g₁ x - 𝓕 g₂ x := by
      rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
      simp only [Pi.sub_apply, smul_sub]
      exact integral_sub ((Real.fourierIntegral_convergent_iff x).2 hg₁)
        ((Real.fourierIntegral_convergent_iff x).2 hg₂)
    rw [hsplit, h x, sub_self]
  have hsub := ae_eq_zero_of_fourierIntegral_eq_zero (hg₁.sub hg₂) hF
  filter_upwards [hsub] with x hx
  have hval : g₁ x - g₂ x = 0 := hx
  exact sub_eq_zero.mp hval

end HTGeometry
