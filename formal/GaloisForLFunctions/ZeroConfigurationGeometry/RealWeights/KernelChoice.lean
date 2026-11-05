import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.StripFourier
import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatedPointsAreSeenByTheLocalCamera
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Strip kernels with near-unit normalized mass

A small physical aperture makes the common strip envelope nearly preserve
Fourier energy. An expanding central interval captures every fixed fraction
of that energy, giving any prescribed normalized mass factor above one.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23

/-- An integrable kernel of positive mass captures every fraction below one
of its total mass in some symmetric interval. -/
theorem exists_central_kernel_mass_gt {K : ℝ → ℝ} (hKi : Integrable K)
    (hP : 0 < ∫ x, K x) {η : ℝ} (hη : η < 1) :
    ∃ R : ℝ, 1 ≤ R ∧ η * (∫ x, K x) < ∫ x in (-R)..R, K x := by
  have ht : Tendsto (fun R : ℝ => ∫ x in Icc (-R) R, K x) atTop (𝓝 (∫ x, K x)) :=
    (aecover_Icc (μ := volume) tendsto_neg_atTop_atBot tendsto_id).integral_tendsto_of_countably_generated hKi
  have hηP : η * (∫ x, K x) < ∫ x, K x := by nlinarith only [hη, hP]
  have he := (tendsto_order.mp ht).1 _ hηP
  obtain ⟨R, hR, hval⟩ := ((eventually_ge_atTop (1 : ℝ)).and he).exists
  refine ⟨R, hR, ?_⟩
  rw [intervalIntegral.integral_of_le (by linarith only [hR]), ← integral_Icc_eq_integral_Ioc]
  exact hval

/-- Every positive aperture admits a smooth Fourier kernel whose common strip envelope
costs less than any prescribed factor above one after central-mass normalization. -/
theorem exists_camera_kernel_with_strip_mass {a q : ℝ} (ha : 0 < a) (hq : 1 < q) :
    ∃ (ε R : ℝ) (b : ℝ → ℂ),
      0 < ε ∧ ε ≤ a ∧ 1 ≤ R ∧ ContDiff ℝ (⊤ : ℕ∞) b ∧
      tsupport b ⊆ Icc (-ε) ε ∧
      0 < (∫ x in (-R)..R, ‖paperFT b x‖ ^ 2) ∧
      (∫ x, cameraStripEnvelope b ε x) ≤
        q * (∫ x in (-R)..R, ‖paperFT b x‖ ^ 2) := by
  let p : ℝ := (1 + q) / 2
  have hp1 : 1 < p := by dsimp [p]; linarith only [hq]
  have hpq : p < q := by dsimp [p]; linarith only [hq]
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  let E : ℝ → ℝ := fun e => 1 + e + (e + e ^ 2) * Real.exp e
  have hEc : Continuous E := by dsimp [E]; fun_prop
  have hE0 : E 0 = 1 := by simp only [E, add_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
  have hE0p : E 0 < p := by rw [hE0]; exact hp1
  have hnear : ∀ᶠ e in 𝓝 (0 : ℝ), E e < p :=
    hEc.continuousAt.eventually (Iio_mem_nhds hE0p)
  obtain ⟨δ, hδ, hδE⟩ := Metric.eventually_nhds_iff.mp hnear
  let ε := min (a / 2) (δ / 2)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεa : ε ≤ a := (min_le_left _ _).trans (by linarith only [ha])
  have hεd : ε < δ := (min_le_right _ _).trans_lt (by linarith only [hδ])
  have hEp : E ε < p := hδE (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using hεd)
  obtain ⟨b, hb, hbs, hb1⟩ := exists_bump_one_le_norm_paperFT_I_mul hε
  have hbw : ApertureWindow ε b := ⟨hb.of_le (by norm_cast), hbs⟩
  let K : ℝ → ℝ := fun x => ‖paperFT b x‖ ^ 2
  have hKc : Continuous K := by
    have hd : Differentiable ℂ (paperFT b) :=
      fun z => (hasDerivAt_cameraFT_compact hb.continuous hbw.hasCompactSupport z).differentiableAt
    exact (hd.continuous.comp Complex.continuous_ofReal).norm.pow 2
  have hKi : Integrable K := _root_.RHTower.integrable_normSq_paperFT hbw.1 hbs
  have hK0 : 0 < K 0 := by
    have hh := hb1 0
    simp only [Complex.ofReal_zero, zero_mul] at hh
    dsimp [K]
    nlinarith only [hh]
  have hP : 0 < ∫ x, K x := by
    apply (integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _) hKi).mpr
    exact hKc.isOpen_support.measure_pos volume ⟨0, ne_of_gt hK0⟩
  have hpq1 : p / q < 1 := (div_lt_one hq0).mpr hpq
  obtain ⟨R, hR, hPR⟩ := exists_central_kernel_mass_gt hKi hP hpq1
  have hcentral : 0 < ∫ x in (-R)..R, K x :=
    (mul_pos (div_pos (by linarith only [hp1]) hq0) hP).trans hPR
  refine ⟨ε, R, b, hε, hεa, hR, hb, hbs, hcentral, ?_⟩
  have hmass := (cameraStripEnvelope_integrable_and_mass_le hbw.1 hbs hε).2
  have hratio : p * (∫ x, K x) < q * (∫ x in (-R)..R, K x) := by
    have hh := mul_lt_mul_of_pos_left hPR hq0
    field_simp [hq0.ne'] at hh
    nlinarith only [hh]
  exact hmass.trans ((mul_le_mul_of_nonneg_right hEp.le hP.le).trans hratio.le)

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.exists_central_kernel_mass_gt
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.exists_camera_kernel_with_strip_mass
