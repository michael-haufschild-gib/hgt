import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.AnalyticSmoothingJet
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Endpoint moments of analytic phase mixtures

The first Taylor moment is the endpoint derivative. Unit modulus forces
an imaginary endpoint tangent, preserved by real affine averaging.
Together with coefficient mass minus two, this forces a positive real
Taylor coefficient even when leading imaginary coefficients cancel.
-/

open Complex Filter Topology Metric Set
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The endpoint derivative is the absolutely convergent first Taylor moment. -/
theorem smoothingTaylor_hasSum_firstMoment {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) :
    HasSum (fun n : ℕ => (n : ℂ) * smoothingTaylorCoefficient Φ n) (deriv Φ 1) := by
  obtain ⟨ρ, hρ1, hρR⟩ := exists_between hR
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ1
  have hp := smoothingTaylor_hasFPowerSeriesOnBall hR hΦ
  have hmem : (ρ : ℂ) ∈ Metric.eball 0 (smoothingTaylorSeries Φ).radius := by
    apply Metric.eball_subset_eball hp.r_le
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, norm_real,
      Real.norm_eq_abs, abs_of_pos hρ0]
    exact hρR
  have hs : Summable (fun n : ℕ => ‖smoothingTaylorCoefficient Φ n‖ * ρ ^ n) := by
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, norm_smul, norm_pow,
      norm_real, Real.norm_eq_abs, abs_of_pos hρ0, smoothingTaylorCoefficient, mul_comm] using
      (smoothingTaylorSeries Φ).summable_norm_apply hmem
  have hd := Complex.hasSum_deriv_of_summable_norm hs
    (F := fun n z => smoothingTaylorCoefficient Φ n * z ^ n)
    (U := ball 0 ρ) (fun n z _ =>
      (analyticAt_const.mul (analyticAt_id.pow n)).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball (fun n z hz => by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (by exact le_of_lt (by simpa only [mem_ball, dist_zero_right] using hz)) n) (norm_nonneg _))
    (z := 1) (by simpa only [mem_ball, dist_zero_right, norm_one] using hρ1)
  have he : (fun z : ℂ => ∑' n : ℕ, smoothingTaylorCoefficient Φ n * z ^ n) =ᶠ[𝓝 1]
      (fun z => Φ z - 1) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (show (1 : ℂ) ∈ ball 0 (R : ℝ) by simpa using hR)] with z hz
    have hz' : z ∈ Metric.eball (0 : ℂ) R := by simpa only [Metric.eball_coe] using hz
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul,
      smoothingTaylorCoefficient, zero_add, mul_comm] using (hp.hasSum hz').tsum_eq
  rw [he.deriv_eq, deriv_sub_const] at hd
  have hterm (n : ℕ) : deriv (fun z : ℂ => smoothingTaylorCoefficient Φ n * z ^ n) 1 =
      (n : ℂ) * smoothingTaylorCoefficient Φ n := by
    have hh := (((hasDerivAt_id (1 : ℂ)).pow n).const_mul (smoothingTaylorCoefficient Φ n)).deriv
    simp only [Pi.pow_apply, id_eq, one_pow, mul_one] at hh
    exact hh.trans (mul_comm _ _)
  simpa only [hterm] using hd

/-- Unit modulus on the real interval forces an imaginary endpoint tangent. -/
theorem analyticPhase_endpoint_tangent {Φ : ℂ → ℂ}
    (hΦ : DifferentiableAt ℂ Φ 1) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) :
    (deriv Φ 1).re = 0 := by
  let G : ℂ → ℂ := fun z => dslope Φ 1 (1 - z)
  have hc : ContinuousAt (fun z : ℂ => 1 - z) 0 := continuousAt_const.sub continuousAt_id
  have hd : ContinuousAt (dslope Φ 1) ((fun z : ℂ => 1 - z) 0) := by
    simpa only [sub_zero] using continuousAt_dslope_same.mpr hΦ
  have hG : ContinuousAt G 0 := hd.comp hc
  have hr := firstUnitCoefficient_re_eq_zero (m := 1) zero_lt_one hG (fun x hx => by
    have he := sub_smul_dslope Φ 1 (1 - (x : ℂ))
    simp only [smul_eq_mul, h1] at he
    have heq : 1 + (x : ℂ) * G (x : ℂ) = -Φ (1 - (x : ℂ)) := by
      dsimp only [G]
      linear_combination -he
    rw [pow_one, heq, norm_neg, ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact hunit (1 - x) ⟨by linarith only [hx.2], by linarith only [hx.1]⟩)
  simpa only [G, sub_zero, dslope_same] using hr

/-- Zero real endpoint moment and mass minus two force a positive real coefficient. -/
theorem analyticSmoothing_exists_positive_real_coefficient {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (h0 : Φ 0 = 1) (h1 : Φ 1 = -1) (ht : (deriv Φ 1).re = 0) :
    ∃ k : ℕ, 0 < k ∧ 0 < (smoothingTaylorCoefficient Φ k).re := by
  have hm := Complex.hasSum_re (smoothingTaylor_hasSum_firstMoment hR hΦ)
  have hc := Complex.hasSum_re
    (Summable.of_norm (summable_norm_smoothingTaylorCoefficient hR hΦ)).hasSum
  rw [tsum_smoothingTaylorCoefficient hR hΦ h1] at hc
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
    ht] at hm
  have hz := smoothingTaylorCoefficient_zero hR hΦ h0
  by_contra h
  have hn : ∀ k : ℕ, (smoothingTaylorCoefficient Φ k).re ≤ 0 := by
    intro k
    by_cases hk : k = 0
    · simp only [hk, hz, Complex.zero_re, le_refl]
    · exact le_of_not_gt (fun hp => h ⟨k, Nat.pos_of_ne_zero hk, hp⟩)
  have hle := hm.summable.tsum_le_tsum (g := fun n : ℕ => (smoothingTaylorCoefficient Φ n).re)
    (fun n => by
      by_cases hn0 : n = 0
      · simp only [hn0, hz, Complex.zero_re, mul_zero, le_refl]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
        nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hn1) (hn n)])
    hc.summable
  rw [hm.tsum_eq, hc.tsum_eq] at hle
  norm_num at hle


/-- Real affine mixtures preserve both normalization and the imaginary endpoint tangent. -/
theorem analyticPhase_affine_average {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (Φ : ι → ℂ → ℂ) {R : NNReal} (hR : 1 < (R : ℝ))
    (hc : ∑ j ∈ s, c j = 1)
    (hΦ : ∀ j ∈ s, AnalyticOnNhd ℂ (Φ j) (closedBall 0 R))
    (h0 : ∀ j ∈ s, Φ j 0 = 1) (h1 : ∀ j ∈ s, Φ j 1 = -1)
    (hu : ∀ j ∈ s, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ j (x : ℂ)‖ = 1) :
    let Ψ : ℂ → ℂ := fun z => ∑ j ∈ s, (c j : ℂ) * Φ j z
    AnalyticOnNhd ℂ Ψ (closedBall 0 R) ∧ Ψ 0 = 1 ∧ Ψ 1 = -1 ∧
      (deriv Ψ 1).re = 0 := by
  dsimp only
  have hcast : (∑ j ∈ s, (c j : ℂ)) = 1 := by exact_mod_cast hc
  have hd (j : ι) (hj : j ∈ s) : DifferentiableAt ℂ (Φ j) 1 :=
    (hΦ j hj 1 (by simpa only [mem_closedBall, dist_zero_right, norm_one] using hR.le)).differentiableAt
  have heq : (∑ j ∈ s, fun z : ℂ => (c j : ℂ) * Φ j z) =
      (fun z => ∑ j ∈ s, (c j : ℂ) * Φ j z) := by
    funext z
    simp only [Finset.sum_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [← heq]
    exact s.analyticAt_sum (fun j hj =>
      (show AnalyticAt ℂ (fun _ : ℂ => (c j : ℂ)) z from analyticAt_const).mul (hΦ j hj z hz))
  · calc
      _ = ∑ j ∈ s, (c j : ℂ) := Finset.sum_congr rfl (fun j hj => by rw [h0 j hj, mul_one])
      _ = 1 := hcast
  · calc
      _ = ∑ j ∈ s, -(c j : ℂ) := Finset.sum_congr rfl (fun j hj => by rw [h1 j hj, mul_neg_one])
      _ = -1 := by rw [Finset.sum_neg_distrib, hcast]
  · have hderiv := HasDerivAt.sum (u := s) (fun j hj => (hd j hj).hasDerivAt.const_mul (c j : ℂ))
    rw [← heq, hderiv.deriv, Complex.re_sum]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, analyticPhase_endpoint_tangent (hd j hj) (h1 j hj) (hu j hj), mul_zero]

#print axioms analyticPhase_affine_average
#print axioms smoothingTaylor_hasSum_firstMoment
#print axioms analyticPhase_endpoint_tangent
#print axioms analyticSmoothing_exists_positive_real_coefficient
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
