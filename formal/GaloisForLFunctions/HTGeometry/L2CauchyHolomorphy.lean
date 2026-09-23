import GaloisForLFunctions.HTGeometry.L2DominatedContinuity
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A locally square-integrably dominated analytic family is analytic in the actual L² quotient. -/
open MeasureTheory Filter Set Topology Metric
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [MeasurableSpace A]

/-- The actual L² class where it exists, with a fixed value elsewhere. -/
def l2Family (μ : Measure A) (F : ℂ → A → ℂ) (z : ℂ) : Lp ℂ 2 μ := by
  classical
  exact if h : MemLp (F z) 2 μ then h.toLp (F z) else 0

theorem l2Family_eq_toLp (μ : Measure A) (F : ℂ → A → ℂ) (z : ℂ) (h : MemLp (F z) 2 μ) :
    l2Family μ F z = h.toLp (F z) := by simp only [l2Family,dif_pos h]

/-- A common L² bound on pointwise holomorphic functions controls the genuine complex L² slope limit. -/
theorem differentiableAt_l2Family_of_cauchy_dominated (μ : Measure A) (F : ℂ → A → ℂ)
    (z : ℂ) (R : ℝ) (hR : 0 < R) (b : A → ℝ) (hb : MemLp b 2 μ)
    (hm : ∀ u ∈ ball z R, AEStronglyMeasurable (F u) μ)
    (hd : ∀ a, DifferentiableOn ℂ (fun u => F u a) (ball z R))
    (hbound : ∀ a, ∀ u ∈ ball z R, ‖F u a‖ ≤ b a) :
    DifferentiableAt ℂ (l2Family μ F) z := by
  have hz : z ∈ ball z R := mem_ball_self hR
  have hhalf : 0 < R/2 := by positivity
  have hsub : ball z (R/2) ⊆ ball z R := ball_subset_ball (by linarith)
  have hf (u : ℂ) (hu : u ∈ ball z R) : MemLp (F u) 2 μ :=
    MemLp.of_le hb (hm u hu) (Eventually.of_forall (fun a => (hbound a u hu).trans (le_abs_self _)))
  let d (a : A) := deriv (fun u => F u a) z
  let B (a : A) := (2/R)*b a
  have hB : MemLp B 2 μ := hb.const_mul (2/R)
  have hb0 (a : A) : 0 ≤ b a := (norm_nonneg _).trans (hbound a z hz)
  have hB0 (a : A) : 0 ≤ B a := mul_nonneg (by positivity) (hb0 a)
  have hdb (a : A) (u : ℂ) (hu : u ∈ ball z (R/2)) :
      ‖deriv (fun w => F w a) u‖ ≤ B a := by
    have h := Bottcher.norm_deriv_le_of_bounded_on_ball hR (hd a) (hbound a) u hu
    convert h using 1
    dsimp [B]
    ring
  have hdm : AEStronglyMeasurable d μ := aestronglyMeasurable_deriv_param_complex hR hm
    (fun a => (hd a).differentiableAt (isOpen_ball.mem_nhds hz))
  have hdf : MemLp d 2 μ := MemLp.of_le hB hdm
    (Eventually.of_forall (fun a => (hdb a z (mem_ball_self hhalf)).trans (le_abs_self _)))
  let D := hdf.toLp d
  let g (u : ℂ) (a : A) : ℂ := (u-z)⁻¹ • (F u a-F z a)
  have hg (u : ℂ) (hu : u ∈ ball z (R/2)) : MemLp (g u) 2 μ :=
    ((hf u (hsub hu)).sub (hf z hz)).const_smul (u-z)⁻¹
  have hgb (u : ℂ) (hu : u ∈ ball z (R/2)) (a : A) : ‖g u a‖ ≤ B a := by
    by_cases he : u = z
    · simpa [g,he] using hB0 a
    have hdiff (v : ℂ) (hv : v ∈ ball z (R/2)) :
        HasDerivAt (fun w => F w a) (deriv (fun w => F w a) v) v :=
      ((hd a).differentiableAt (isOpen_ball.mem_nhds (hsub hv))).hasDerivAt
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v hv => (hdiff v hv).hasDerivWithinAt) (hdb a) (convex_ball z (R/2))
      (mem_ball_self hhalf) hu
    dsimp [g]
    rw [norm_mul,norm_inv]
    calc
      _ ≤ ‖u-z‖⁻¹*(B a*‖u-z‖) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = B a := by rw [mul_left_comm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr he)),mul_one]
  have hi : Integrable (fun a => 4*(B a)^(2 : ℕ)) μ :=
    ((memLp_two_iff_integrable_sq hB.aestronglyMeasurable).mp hB).const_mul 4
  have hnhds0 : ∀ᶠ u in 𝓝 z, u ∈ ball z (R/2) := ball_mem_nhds z hhalf
  have hnhds : ∀ᶠ u in 𝓝[≠] z, u ∈ ball z (R/2) := hnhds0.filter_mono nhdsWithin_le_nhds
  have hlim : Tendsto (fun u => ∫ a, ‖g u a-d a‖^(2 : ℕ) ∂μ) (𝓝[≠] z) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[≠] z)
      (F := fun u a => ‖g u a-d a‖^(2 : ℕ)) (f := fun _ : A => (0:ℝ)) (fun a => 4*(B a)^(2 : ℕ))
      (hnhds.mono (fun u hu => ((hg u hu).aestronglyMeasurable.sub hdf.aestronglyMeasurable).norm.pow 2))
      (hnhds.mono (fun u hu => Eventually.of_forall (fun a => ?_))) hi ?_
    · simpa only [integral_zero] using h
    · rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have h := norm_sub_le (g u a) (d a)
      have h₁ := hgb u hu a
      have h₂ := hdb a z (mem_ball_self hhalf)
      change ‖d a‖ ≤ B a at h₂
      nlinarith [norm_nonneg (g u a-d a)]
    · exact Eventually.of_forall (fun a => by
        have h := (((hd a).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.tendsto_slope.sub
          (tendsto_const_nhds (x := d a))).norm.pow 2
        simpa only [slope_def_module,g,d,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using h)
  have he (u : ℂ) (hu : u ∈ ball z (R/2)) : (hg u hu).toLp (g u) =
      (u-z)⁻¹ • (l2Family μ F u-l2Family μ F z) := by
    rw [l2Family_eq_toLp μ F u (hf u (hsub hu)),l2Family_eq_toLp μ F z (hf z hz)]
    change (((hf u (hsub hu)).sub (hf z hz)).const_smul (u-z)⁻¹).toLp _ = _
    rw [MemLp.toLp_const_smul _ ((hf u (hsub hu)).sub (hf z hz)),MemLp.toLp_sub]
  have hn (u : ℂ) (hu : u ∈ ball z (R/2)) :
      ‖(u-z)⁻¹ • (l2Family μ F u-l2Family μ F z)-D‖^(2 : ℕ) = ∫ a, ‖g u a-d a‖^(2 : ℕ) ∂μ := by
    rw [← he u hu]
    dsimp [D]
    rw [← MemLp.toLp_sub,_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [((hg u hu).sub hdf).coeFn_toLp] with a ha
    rw [ha]
    rfl
  have hs : Tendsto (fun u => ‖(u-z)⁻¹ • (l2Family μ F u-l2Family μ F z)-D‖^(2 : ℕ)) (𝓝[≠] z) (𝓝 0) :=
    hlim.congr' (hnhds.mono (fun u hu => (hn u hu).symm))
  have hnorm := (Real.continuous_sqrt.tendsto 0).comp hs
  have hderiv : HasDerivAt (l2Family μ F) D z := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq (norm_nonneg _),slope_def_module] using hnorm
  exact hderiv.differentiableAt

end
end GaloisForLFunctions.HTGeometry
