import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.RHTower.LevinsonDetectorFE
import Mathlib.Analysis.Complex.Liouville

/-!
# Polynomial growth of the detector on a vertical strip

The crude polynomial bound for `ζ` on a strip transfers to `ζ'` by Cauchy's estimate on the unit
disc — every point of that disc still lies in a slightly wider strip at essentially the same height
— and hence to `G = ζ + λζ'` for every `‖λ‖ ≤ 1`.
-/

open Complex Metric

noncomputable section

namespace RHTower

theorem exists_bound_norm_deriv_riemannZeta_strip (M : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, |s.re| ≤ M → 2 ≤ |s.im| →
      ‖deriv riemannZeta s‖ ≤ C * (2 * |s.im|) ^ N := by
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_riemannZeta_strip (M + 1)
  refine ⟨C, N, hC0, fun s hre him => ?_⟩
  have hnb : ∀ w : ℂ, ‖w - s‖ ≤ 1 → |w.re| ≤ M + 1 ∧ 1 ≤ |w.im| ∧ |w.im| ≤ 2 * |s.im| := by
    intro w hw
    have h1 := Complex.abs_re_le_norm (w - s)
    have h2 := Complex.abs_im_le_norm (w - s)
    rw [Complex.sub_re] at h1
    rw [Complex.sub_im] at h2
    have hre1 : |w.re - s.re| ≤ 1 := le_trans h1 hw
    have him1 : |w.im - s.im| ≤ 1 := le_trans h2 hw
    rw [abs_le] at hre1 him1
    have hreabs : |s.re| ≤ M := hre
    rw [abs_le] at hreabs
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith [hreabs.1, hreabs.2, hre1.1, hre1.2]
    · rcases le_or_gt 0 s.im with hs | hs
      · have : 2 ≤ s.im := by rwa [abs_of_nonneg hs] at him
        rw [le_abs]; left; linarith [him1.1]
      · have : 2 ≤ -s.im := by rwa [abs_of_neg hs] at him
        rw [le_abs]; right; linarith [him1.2]
    · rcases le_or_gt 0 s.im with hs | hs
      · have hs2 : 2 ≤ s.im := by rwa [abs_of_nonneg hs] at him
        rw [abs_of_nonneg hs] at *
        rw [abs_le]; constructor <;> linarith [him1.1, him1.2]
      · have hs2 : 2 ≤ -s.im := by rwa [abs_of_neg hs] at him
        rw [abs_of_neg hs] at *
        rw [abs_le]; constructor <;> linarith [him1.1, him1.2]
  have hne : ∀ w : ℂ, ‖w - s‖ ≤ 1 → w ≠ 1 := by
    intro w hw heq
    obtain ⟨-, h1, -⟩ := hnb w hw
    rw [heq, Complex.one_im, abs_zero] at h1
    norm_num at h1
  have hdcc : DiffContOnCl ℂ riemannZeta (ball s 1) := by
    constructor
    · intro w hw
      rw [mem_ball, Complex.dist_eq] at hw
      exact (differentiableAt_riemannZeta (hne w hw.le)).differentiableWithinAt
    · rw [closure_ball s (by norm_num : (1 : ℝ) ≠ 0)]
      intro w hw
      rw [mem_closedBall, Complex.dist_eq] at hw
      exact (differentiableAt_riemannZeta (hne w hw)).continuousAt.continuousWithinAt
  have hbound : ∀ z ∈ sphere s (1 : ℝ), ‖riemannZeta z‖ ≤ C * (2 * |s.im|) ^ N := by
    intro z hz
    rw [mem_sphere, Complex.dist_eq] at hz
    obtain ⟨hre', him1, him2⟩ := hnb z hz.le
    have hz' : riemannZeta ((z.re : ℂ) + (z.im : ℂ) * I) = riemannZeta z := by
      rw [Complex.re_add_im]
    have h := hC z.re z.im hre' him1
    rw [hz'] at h
    refine le_trans h ?_
    have hmono : |z.im| ^ N ≤ (2 * |s.im|) ^ N := pow_le_pow_left₀ (abs_nonneg _) him2 N
    exact mul_le_mul_of_nonneg_left hmono hC0
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1) hdcc hbound
  simpa using h

/-- **Polynomial growth of the detector on a vertical strip.** -/
theorem exists_bound_norm_levinsonG_strip (M : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 1 ≤ C ∧ ∀ lam : ℂ, ‖lam‖ ≤ 1 → ∀ s : ℂ, |s.re| ≤ M → 2 ≤ |s.im| →
      ‖levinsonG lam s‖ ≤ C * (2 * |s.im|) ^ N := by
  obtain ⟨C₁, N₁, hC₁0, hC₁⟩ := exists_bound_norm_riemannZeta_strip M
  obtain ⟨C₂, N₂, hC₂0, hC₂⟩ := exists_bound_norm_deriv_riemannZeta_strip M
  refine ⟨C₁ + C₂ + 1, max N₁ N₂, by linarith, fun lam hlam s hre him => ?_⟩
  have hs2 : (2 : ℝ) ≤ |s.im| := him
  have hbase : (1 : ℝ) ≤ 2 * |s.im| := by linarith
  have hz : riemannZeta ((s.re : ℂ) + (s.im : ℂ) * I) = riemannZeta s := by
    rw [Complex.re_add_im]
  have h1 : ‖riemannZeta s‖ ≤ C₁ * (2 * |s.im|) ^ N₁ := by
    have h := hC₁ s.re s.im hre (by linarith)
    rw [hz] at h
    refine le_trans h ?_
    have : |s.im| ^ N₁ ≤ (2 * |s.im|) ^ N₁ :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith) N₁
    exact mul_le_mul_of_nonneg_left this hC₁0
  have h2 : ‖deriv riemannZeta s‖ ≤ C₂ * (2 * |s.im|) ^ N₂ := hC₂ s hre him
  have hmono₁ : (2 * |s.im|) ^ N₁ ≤ (2 * |s.im|) ^ (max N₁ N₂) :=
    pow_le_pow_right₀ hbase (le_max_left _ _)
  have hmono₂ : (2 * |s.im|) ^ N₂ ≤ (2 * |s.im|) ^ (max N₁ N₂) :=
    pow_le_pow_right₀ hbase (le_max_right _ _)
  have hpowpos : (0 : ℝ) ≤ (2 * |s.im|) ^ (max N₁ N₂) := by positivity
  have hlammul : ‖lam * deriv riemannZeta s‖ ≤ C₂ * (2 * |s.im|) ^ (max N₁ N₂) := by
    rw [norm_mul]
    calc ‖lam‖ * ‖deriv riemannZeta s‖
        ≤ 1 * (C₂ * (2 * |s.im|) ^ N₂) :=
          mul_le_mul hlam h2 (norm_nonneg _) (by norm_num)
      _ = C₂ * (2 * |s.im|) ^ N₂ := by ring
      _ ≤ C₂ * (2 * |s.im|) ^ (max N₁ N₂) := mul_le_mul_of_nonneg_left hmono₂ hC₂0
  calc ‖levinsonG lam s‖
      = ‖riemannZeta s + lam * deriv riemannZeta s‖ := by rw [levinsonG]
    _ ≤ ‖riemannZeta s‖ + ‖lam * deriv riemannZeta s‖ := norm_add_le _ _
    _ ≤ C₁ * (2 * |s.im|) ^ (max N₁ N₂) + C₂ * (2 * |s.im|) ^ (max N₁ N₂) := by
        exact add_le_add (le_trans h1 (mul_le_mul_of_nonneg_left hmono₁ hC₁0)) hlammul
    _ ≤ (C₁ + C₂ + 1) * (2 * |s.im|) ^ (max N₁ N₂) := by nlinarith [hpowpos]

end RHTower

end
