import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCutoffTail
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorReciprocalTest

/-!
# Actual reciprocal compact-test transport

The weight-one reciprocal lower test is exactly the complementary compact
upper test. Its Fourier-boundary pairing converges to the existing holomorphic
tail, with every test-support and integrability condition supplied explicitly.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff
namespace RHTower.WeilHigherDenominator

theorem mellinTailTest_admissible {ψ : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ)
    (s : ℂ) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (mellinTailTest ψ s R) ∧ HasCompactSupport (mellinTailTest ψ s R) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ x < a, mellinTailTest ψ s R x = 0 := by
  obtain ⟨a, ha, h0⟩ := hψ.zero_near_origin
  obtain ⟨b, hb⟩ := hψ.one_near_infinity
  have hη : ContDiff ℝ ∞ (fun x : ℝ => ψ (R⁻¹ * x)) :=
    hψ.smooth.comp (contDiff_const.mul contDiff_id)
  have hzero : ∀ x < a, mellinTailTest ψ s R x = 0 := by
    intro x hx
    simp [mellinTailTest, h0 x hx]
  refine ⟨?_, ?_, ⟨a, ha, hzero⟩⟩
  · have he : mellinTailTest ψ s R = fun x : ℝ =>
        (ψ x * (x : ℂ) ^ (s - 1)) * (1 - ψ (R⁻¹ * x)) := by
      funext x
      dsimp only [mellinTailTest]
      ring
    rw [he]
    exact (hψ.contDiff_mul_cpow (s - 1)).mul ((contDiff_const (c := (1 : ℂ))).sub hη)
  · apply HasCompactSupport.of_support_subset_isCompact (K := Icc a (R * b)) isCompact_Icc
    intro x hx
    constructor
    · by_contra hn
      exact hx (hzero x (lt_of_not_ge hn))
    · by_contra hn
      have hh : b < R⁻¹ * x := by
        have ht := (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using lt_of_not_ge hn)
        simpa only [div_eq_mul_inv, mul_comm] using ht
      exact hx (by simp [mellinTailTest, hb (R⁻¹ * x) hh])

private lemma integral_primitive_tail_pos {F φ : ℝ → ℂ}
    (h0 : ∃ a : ℝ, 0 < a ∧ ∀ x < a, φ x = 0) :
    (∫ x : ℝ, deriv (deriv φ) x * F x) =
      ∫ x : ℝ in Ioi 0, F x * iteratedDeriv 2 φ x := by
  have he : (fun x => F x * iteratedDeriv 2 φ x) = fun x => deriv (deriv φ) x * F x := by
    funext x
    simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero, mul_comm]
  rw [← he]
  symm
  apply integral_Ioi_eq_integral_of_zero_near_origin
  obtain ⟨a, ha, h0⟩ := h0
  refine ⟨a, ha, fun x hx => ?_⟩
  have hz : φ =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact h0 y hy
  have hd := hz.iteratedDeriv_eq 2
  simp only [iteratedDeriv_const, if_neg (by decide : ¬(2 : ℕ) = 0)] at hd
  rw [hd, mul_zero]

theorem fourierBoundaryPairing_eq_primitive_tail {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    (A : ℂ) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ)
    (h0 : ∃ a : ℝ, 0 < a ∧ ∀ x < a, φ x = 0) :
    fourierBoundaryPairing q A φ = A * (∫ x : ℝ in Ioi 0, φ x) +
      ∫ x : ℝ in Ioi 0, fourierBoundaryPrimitive q x * iteratedDeriv 2 φ x := by
  rw [fourierBoundaryPairing_eq_primitive hq A hφ hs,
    integral_Ioi_eq_integral_of_zero_near_origin h0, integral_primitive_tail_pos h0]

theorem tendsto_fourierBoundaryPairing_mellinTailTest {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    {ψ : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ) (A : ℂ) {s : ℂ} (hs : s.re < 0) :
    Tendsto (fun R : ℝ => fourierBoundaryPairing q A (mellinTailTest ψ s R)) atTop
      (𝓝 (primitiveMellinTail (fourierBoundaryPrimitive q) A ψ s)) := by
  have ht := tendsto_mellinTail_primitiveMellinTail hψ
    (continuous_fourierBoundaryPrimitive hq) ⟨_, norm_fourierBoundaryPrimitive_le hq⟩ A hs
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  obtain ⟨hφ, hs, h0⟩ := mellinTailTest_admissible hψ s hR
  exact (fourierBoundaryPairing_eq_primitive_tail hq A hφ hs h0).symm

/-- The reciprocal of the actual lower test is exactly a compact upper test. -/
theorem coPoissonReciprocalSeed_mellinHeadTest {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (s : ℂ) {R : ℝ} (hR : 0 < R) :
    coPoissonReciprocalSeed (mellinHeadTest ψ s R) =
      mellinTailTest (mellinReciprocalCutoff ψ) (1 - s) R := by
  funext x
  by_cases hx : 0 < x
  · have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hRx : 0 < R⁻¹ * x := mul_pos (inv_pos.mpr hR) hx
    have hi : (R⁻¹ * x)⁻¹ = R * x⁻¹ := by simp [mul_inv_rev, mul_comm]
    have ha : (x : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx.le]
      exact Real.pi_pos.ne
    have hp : (x : ℂ)⁻¹ * ((x⁻¹ : ℝ) : ℂ) ^ (s - 1) = (x : ℂ) ^ (-s) := by
      rw [Complex.ofReal_inv, Complex.inv_cpow _ _ ha, ← Complex.cpow_neg,
        ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hxC]
      congr 1
      ring
    dsimp only [coPoissonReciprocalSeed, mellinHeadTest, mellinTailTest]
    rw [mellinReciprocalCutoff, if_pos hx, mellinReciprocalCutoff, if_pos hRx,
      hi, sub_sub_cancel, show 1 - s - 1 = -s by ring]
    rw [Complex.ofReal_inv]
    simp only [Complex.ofReal_inv] at hp
    linear_combination (1 - ψ x⁻¹) * ψ (R * x⁻¹) * hp
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    have hxinv : x⁻¹ ≤ 0 := inv_nonpos.mpr hx0
    obtain ⟨a, ha, h0⟩ := hψ.zero_near_origin
    have hz : ψ (R * x⁻¹) = 0 := h0 _ ((mul_nonpos_of_nonneg_of_nonpos hR.le hxinv).trans_lt ha)
    simp [coPoissonReciprocalSeed, mellinHeadTest, mellinTailTest,
      mellinReciprocalCutoff, hx, hz]

/-- Actual reciprocal-test limit, with no regularity assumption on the boundary distribution. -/
theorem tendsto_fourierBoundaryPairing_reciprocal_head {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    {ψ : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ) (A : ℂ) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun R : ℝ => fourierBoundaryPairing q A
      (coPoissonReciprocalSeed (mellinHeadTest ψ s R))) atTop
      (𝓝 (primitiveMellinTail (fourierBoundaryPrimitive q) A (mellinReciprocalCutoff ψ) (1 - s))) := by
  have ht := tendsto_fourierBoundaryPairing_mellinTailTest hq hψ.reciprocal A
    (s := 1 - s) (by simp only [sub_re, one_re]; linarith)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [coPoissonReciprocalSeed_mellinHeadTest hψ s hR]
end RHTower.WeilHigherDenominator
