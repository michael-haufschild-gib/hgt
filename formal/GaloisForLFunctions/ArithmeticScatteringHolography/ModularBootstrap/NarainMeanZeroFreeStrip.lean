import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanLineBounds
import GaloisForLFunctions.CountingHolography.ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip

/-!
# Interior Mellin bounds under a zero-free condition

An explicit zero-free half-plane condition gives analyticity and polynomial-times-exponential decay on each closed interior Mellin strip.
-/

open Complex RHTower
open GaloisForLFunctions.CountingHolography
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- A zero-free xi half-plane gives the corresponding regular half-plane of the actual mean. -/
theorem analyticAt_narainMellinMean_of_zeroFree (Y Z : Height) {σ₀ : ℝ}
    (hσ : 0 ≤ σ₀) (hξ : ∀ z : ℂ, σ₀ < z.re → xi z ≠ 0) {u : ℂ}
    (hu : σ₀ < 1 + 2 * u.re) (hmain : u ≠ 1 / 2) :
    AnalyticAt ℂ (narainMellinMean Y Z) u := by
  have hre : σ₀ < (1 + 2 * u).re := by simpa using hu
  have hlin : 1 + 2 * u ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre
    exact (not_lt_of_ge hσ) hre
  exact analyticAt_narainMellinMean_of_regular Y Z
    (mul_ne_zero hlin (hξ _ hre)) hmain

/-- Every closed interior strip retains exponential Mellin decay under the exact zero-free condition. -/
theorem exists_narainMellinMean_zeroFree_strip_bound (Y Z : Height) {σ₀ a : ℝ}
    (hσ₀ : 0 ≤ σ₀) (hσ₁ : σ₀ < 1)
    (hξ : ∀ z : ℂ, σ₀ < z.re → xi z ≠ 0)
    (ha : a < 0) (hmargin : σ₀ < 1 + 2 * a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ u : ℂ, a ≤ u.re → u.re ≤ 0 → 1 ≤ |u.im| →
      ‖narainMellinMean Y Z u‖ ≤
        C * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) := by
  have hζ : ∀ z : ℂ, σ₀ < z.re → z ≠ 1 → riemannZeta z ≠ 0 := by
    intro z hz hz₁ hz₀
    exact hξ z hz ((xi_eq_zero_iff (hσ₀.trans_lt hz) hz₁).mpr hz₀)
  obtain ⟨K, NK, hK, hk⟩ := (zeroFree_iff_zeta_lower_bound hσ₀ hσ₁).mp hζ
    (1 + 2 * a - σ₀) (sub_pos.mpr hmargin) 1
  obtain ⟨C, N, hC, hb⟩ := exists_narainMellinMean_strip_bound Y Z
    (B := -a) (neg_nonneg.mpr ha.le)
  refine ⟨C * K * 2 ^ NK, N + NK, by positivity, ?_⟩
  intro u hlo hhi ht
  have huB : |u.re| ≤ -a := by
    rw [abs_of_nonpos hhi]
    exact neg_le_neg hlo
  have hsre : σ₀ < (1 + 2 * u).re := by
    have he : (1 + 2 * u).re = 1 + 2 * u.re := by simp
    rw [he]
    linarith only [hmargin, hlo]
  have hsim : |(1 + 2 * u).im| = 2 * |u.im| := by
    have he : (1 + 2 * u).im = 2 * u.im := by simp
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hs₁ : 1 + 2 * u ≠ 1 := by
    intro h
    have he : |(1 + 2 * u).im| = 0 := by rw [h]; simp
    rw [hsim] at he
    linarith only [ht, he]
  have hn : 0 < ‖riemannZeta (1 + 2 * u)‖ := norm_pos_iff.mpr (hζ _ hsre hs₁)
  have hk' := hk (1 + 2 * u)
    (by simp; linarith only [hlo]) (by simp; linarith only [hhi])
    (by rw [hsim]; linarith only [ht])
  have hinv : ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ K * (2 * |u.im|) ^ NK := by
    rw [norm_inv, inv_le_iff_one_le_mul₀' hn]
    calc
      1 ≤ K * (2 * |u.im|) ^ NK * ‖riemannZeta (1 + 2 * u)‖ := by
        simpa only [hsim] using hk'
      _ = _ := mul_comm _ _
  have hp : (2 * |u.im|) ^ NK ≤ 2 ^ NK * (1 + |u.im|) ^ NK := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [abs_nonneg u.im]) NK
  calc
    _ ≤ C * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) *
        ‖(riemannZeta (1 + 2 * u))⁻¹‖ := hb u huB ht
    _ ≤ C * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) *
        (K * (2 ^ NK * (1 + |u.im|) ^ NK)) :=
      mul_le_mul_of_nonneg_left (hinv.trans (mul_le_mul_of_nonneg_left hp hK.le)) (by positivity)
    _ = _ := by rw [pow_add]; ring

#print axioms analyticAt_narainMellinMean_of_zeroFree
#print axioms exists_narainMellinMean_zeroFree_strip_bound
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
