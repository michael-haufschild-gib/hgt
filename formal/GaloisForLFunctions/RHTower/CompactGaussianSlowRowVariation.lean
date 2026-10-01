import GaloisForLFunctions.RHTower.CompactGaussianSlowRow
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open Complex Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower

/-- Uniform compact bounds for the actual row amplitude and its conductor-scale
height derivative, with critical chi phase removed exactly. -/
theorem exists_compactGaussianSlowRow_disc_bounds
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ tau ∈ Icc (N : ℝ) (2 * N),
      ∀ s ∈ Metric.closedBall c r, ‖compactGaussianSlowRow s N tau‖ ≤ C ∧
        ‖deriv (compactGaussianSlowRow s N) tau‖ ≤ C / N := by
  obtain ⟨C, hC, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0 hc1
  let R := r + ‖c - (1 / 2 : ℂ)‖
  have hR : 0 ≤ R := add_nonneg hr (norm_nonneg _)
  let K := C + 10 * C * R + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hcost0 : 0 ≤ 10 * C * R := by positivity
  have hCK : C ≤ K := by dsimp only [K]; linarith
  have hlarge : ∀ᶠ N : ℕ in atTop, 4 + 2 * (|c.im| + r) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hrow, hlarge] with N hrowN hN
  have hNR : (0 : ℝ) < N := by linarith [abs_nonneg c.im]
  intro tau htau s hs
  have hd : dist s c ≤ r := hs
  have hre : |s.re - c.re| ≤ r := (by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c) :
      |s.re - c.re| ≤ dist s c).trans hd
  have him : |s.im - c.im| ≤ r := (by
    simpa only [Complex.sub_im, dist_eq_norm] using Complex.abs_im_le_norm (s - c) :
      |s.im - c.im| ≤ dist s c).trans hd
  have himabs : |s.im| ≤ |c.im| + r := by
    have h := abs_add_le (s.im - c.im) c.im
    rw [sub_add_cancel] at h
    linarith
  have hs0 : 0 < s.re := by linarith [(abs_le.mp hre).1]
  have hs1 : s.re < 1 := by linarith [(abs_le.mp hre).2]
  have htau4 : 4 ≤ tau := by linarith [htau.1, abs_nonneg c.im]
  have htau0 : 0 < tau := hNR.trans_le htau.1
  have himtau : 2 * |s.im| ≤ tau := by linarith [htau.1]
  have hsR : ‖s - (1 / 2 : ℂ)‖ ≤ R := by
    have heq : s - (1 / 2 : ℂ) = (s - c) + (c - (1 / 2 : ℂ)) := by ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (by simpa only [dist_eq_norm] using hd) (le_refl _))
  have hrN := (hrowN tau htau s hs).1
  constructor
  · rw [norm_compactGaussianSlowRow]
    exact hrN.trans hCK
  · calc
      _ ≤ ‖reflectedCompactGaussianRow s N tau‖ * ((10 / tau) * ‖s - (1 / 2 : ℂ)‖) :=
        norm_deriv_compactGaussianSlowRow_le hs0 hs1 N htau4 himtau
      _ ≤ C * ((10 / tau) * R) := mul_le_mul hrN
        (mul_le_mul_of_nonneg_left hsR (by positivity)) (by positivity) hC.le
      _ = (10 * C * R) / tau := by ring
      _ ≤ (10 * C * R) / N := div_le_div_of_nonneg_left (by positivity) hNR htau.1
      _ ≤ K / N := div_le_div_of_nonneg_right (by dsimp only [K]; linarith) hNR.le

/-- Dyadic total variation of the actual compact row amplitude is bounded,
including derivative integrability, uniformly in growing conductor. -/
theorem exists_compactGaussianSlowRow_disc_variation
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      IntervalIntegrable (deriv (compactGaussianSlowRow s N)) volume (N : ℝ) (2 * N) ∧
      ‖compactGaussianSlowRow s N (2 * N)‖ +
        (∫ tau in (N : ℝ)..(2 * N), ‖deriv (compactGaussianSlowRow s N) tau‖) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_compactGaussianSlowRow_disc_bounds c hr hc0 hc1
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hab : (N : ℝ) ≤ 2 * N := by linarith
  intro s hs
  have hpoint : ∀ tau ∈ Icc (N : ℝ) (2 * N),
      ‖deriv (compactGaussianSlowRow s N) tau‖ ≤ C / N := fun tau htau => (hN tau htau s hs).2
  have hi : IntervalIntegrable (deriv (compactGaussianSlowRow s N)) volume (N : ℝ) (2 * N) := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C / (N : ℝ)) volume N (2 * N)).mono_fun'
      (aestronglyMeasurable_deriv _ _)
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    exact Filter.Eventually.of_forall (fun tau htau => hpoint tau (by
      rw [uIoc_of_le hab] at htau
      exact ⟨htau.1.le, htau.2⟩))
  refine ⟨hi, ?_⟩
  have hint := intervalIntegral.integral_mono_on hab hi.norm
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C / (N : ℝ)) volume N (2 * N)) hpoint
  have heq : (∫ _tau in (N : ℝ)..(2 * N), C / (N : ℝ)) = C := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp [hNR.ne']
    ring
  rw [heq] at hint
  have hend := (hN (2 * N) ⟨hab, le_rfl⟩ s hs).1
  linarith

end RHTower
