import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceMovedTests
import GaloisForLFunctions.ConjugateDiagonalGeometry.UniversalSourceWeight

/-!
# Uniform control of omitted moving source moments

Outside the source cutoff, an ordinate shift of at most half its radius leaves
the spectral ordinate comparable with its distance from the moving test. The
fourth-order C² transform decay then absorbs logarithmic Hecke growth and
leaves the existing summable xi reference density.
-/

open Complex Set Metric
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization

theorem depthKernel_zeta_le_exp (L : ℝ) (ρ : zetaZeroConfig.carrier) :
    depthKernel L (zetaDepth ρ) ≤ 2 * Real.exp |L| := by
  refine (depthKernel_mono_depth L (d := zetaDepth ρ) (e := (1 / 2 : ℝ))
    (by simpa using abs_zetaDepth_le ρ)).trans ?_
  unfold depthKernel
  rw [show 2 * (1 / 2 : ℝ) * L = L by ring, Real.cosh_eq]
  have hp := Real.exp_le_exp.mpr (le_abs_self L)
  have hm := Real.exp_le_exp.mpr (neg_le_abs L)
  linarith only [hp, hm]

/-- The inner cutoff contains every actual zero below its ordinate radius. -/
theorem sourceCutoff_eq_one_of_im_le (n : ℕ) (ρ : zetaZeroConfig.carrier)
    (h : |(ρ : ℂ).im| ≤ (n : ℝ)) : sourceCutoff n ρ = 1 := by
  have hs := zetaZeroConfig.strip ρ ρ.2
  have hn : ‖(ρ : ℂ)‖ ≤ |(ρ : ℂ).re| + |(ρ : ℂ).im| := by
    calc
      ‖(ρ : ℂ)‖ = ‖((ρ : ℂ).re : ℂ) + ((ρ : ℂ).im : ℂ) * Complex.I‖ :=
        congrArg norm (Complex.re_add_im (ρ : ℂ)).symm
      _ ≤ ‖((ρ : ℂ).re : ℂ)‖ + ‖((ρ : ℂ).im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = _ := by simp
  rw [abs_of_nonneg hs.1] at hn
  apply (sourceCutoff n).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖(ρ : ℂ)‖ ≤ (n : ℝ) + 1
  linarith only [hn, hs.2, h]

/-- The fixed universal weight absorbs every allowed moving depth moment outside the cutoff. -/
theorem universalSourceWeight_moving_tail_le (j n : ℕ) (L τ : ℝ)
    (hτ : |τ| ≤ (n : ℝ) / 2)
    (hL : (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1))
    (ρ : zetaZeroConfig.carrier) (hχ : sourceCutoff n ρ ≠ 1) :
    universalSourceWeight ((ρ : ℂ) - (τ : ℂ) * Complex.I) *
      depthKernel L (zetaDepth ρ) ^ j ≤
        (40 * Real.exp 1 * 2 ^ j) / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
  have hs := zetaZeroConfig.strip ρ ρ.2
  have hy : (n : ℝ) < |(ρ : ℂ).im| := by
    by_contra h
    exact hχ (sourceCutoff_eq_one_of_im_le n ρ (le_of_not_gt h))
  have hsep : |(ρ : ℂ).im| ≤ 2 * |(ρ : ℂ).im - τ| := by
    have h := abs_add_le ((ρ : ℂ).im - τ) τ
    rw [sub_add_cancel] at h
    linarith only [h, hτ, hy]
  have hysq : (ρ : ℂ).im ^ 2 ≤ 4 * ((ρ : ℂ).im - τ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (ρ : ℂ).im) hsep 2
    norm_num only [mul_pow, sq_abs] at h
    exact h
  have hn2 : (n : ℝ) ^ 2 ≤ (ρ : ℂ).im ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (Nat.cast_nonneg n) hy.le 2
  have hN : ((n : ℝ) + 1) ^ 2 ≤ 8 * (1 + ((ρ : ℂ).im - τ) ^ 2) := by
    nlinarith only [hn2, hysq, sq_nonneg ((n : ℝ) - 1), sq_nonneg ((ρ : ℂ).im - τ)]
  have hre : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := by
    rw [gammaOf, Complex.div_I]
    simp
  have him : (gammaOf (ρ : ℂ)).im = -((ρ : ℂ).re - 1 / 2) := by
    rw [gammaOf, Complex.div_I]
    simp
  have hgamma : Complex.normSq (gammaOf (ρ : ℂ)) ≤ (ρ : ℂ).im ^ 2 + 1 / 4 := by
    rw [Complex.normSq_apply, hre, him]
    nlinarith only [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  have hQ : 1 + Complex.normSq (gammaOf (ρ : ℂ)) ≤
      5 * (1 + ((ρ : ℂ).im - τ) ^ 2) := by
    nlinarith only [hgamma, hysq, sq_nonneg ((ρ : ℂ).im - τ)]
  have hQpos : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) :=
    add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)
  have hratio : ((n : ℝ) + 1) ^ 2 / (1 + ((ρ : ℂ).im - τ) ^ 2) ^ 2 ≤
      40 / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
    apply (div_le_div_iff₀ (by positivity) hQpos).2
    calc
      ((n : ℝ) + 1) ^ 2 * (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤
          (8 * (1 + ((ρ : ℂ).im - τ) ^ 2)) *
            (5 * (1 + ((ρ : ℂ).im - τ) ^ 2)) :=
        mul_le_mul hN hQ hQpos.le (by positivity)
      _ = _ := by ring
  have hexp : Real.exp ((j : ℝ) * |L|) ≤ ((n : ℝ) + 1) ^ 2 := by
    refine (Real.exp_le_exp.mpr hL).trans_eq ?_
    have he := Real.exp_nat_mul (Real.log ((n : ℝ) + 1)) 2
    norm_num only [Nat.cast_ofNat] at he
    rw [he, Real.exp_log (by positivity)]
  have hk : depthKernel L (zetaDepth ρ) ^ j ≤ 2 ^ j * ((n : ℝ) + 1) ^ 2 := by
    calc
      depthKernel L (zetaDepth ρ) ^ j ≤ (2 * Real.exp |L|) ^ j :=
        pow_le_pow_left₀ (depthKernel_nonneg _ _) (depthKernel_zeta_le_exp L ρ) j
      _ = 2 ^ j * Real.exp ((j : ℝ) * |L|) := by rw [mul_pow, Real.exp_nat_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hw : universalSourceWeight ((ρ : ℂ) - (τ : ℂ) * Complex.I) ≤
      Real.exp 1 / (1 + ((ρ : ℂ).im - τ) ^ 2) ^ 2 := by
    have hx : (ρ : ℂ).re ^ 2 ≤ 1 := by
      nlinarith only [hs.1, hs.2, mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
    have hr : ((ρ : ℂ) - (τ : ℂ) * Complex.I).re = (ρ : ℂ).re := by simp
    have hi : ((ρ : ℂ) - (τ : ℂ) * Complex.I).im = (ρ : ℂ).im - τ := by simp
    unfold universalSourceWeight
    rw [hr, hi]
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hx) (sq_nonneg _)
  calc
    universalSourceWeight ((ρ : ℂ) - (τ : ℂ) * Complex.I) *
        depthKernel L (zetaDepth ρ) ^ j ≤
        (Real.exp 1 / (1 + ((ρ : ℂ).im - τ) ^ 2) ^ 2) *
          (2 ^ j * ((n : ℝ) + 1) ^ 2) :=
      mul_le_mul hw hk (pow_nonneg (depthKernel_nonneg _ _) _) (by positivity)
    _ = (Real.exp 1 * 2 ^ j) *
        (((n : ℝ) + 1) ^ 2 / (1 + ((ρ : ℂ).im - τ) ^ 2) ^ 2) := by ring
    _ ≤ (Real.exp 1 * 2 ^ j) * (40 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

/-- Every actual compact C² source test has one summable majorant for all its omitted moving moments. -/
theorem sourceDepthKernel_moving_tail_bound (f : CompactTest) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      ∀ ρ : zetaZeroConfig.carrier, sourceCutoff n ρ ≠ 1 →
        sourceDepthKernel (sourceTwist τ f) L j ρ ≤
          C / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
  obtain ⟨B, hB, hb⟩ := normSq_tr_le_universalSourceWeight f
  refine ⟨B * (40 * Real.exp 1 * 2 ^ j), by positivity, ?_⟩
  intro n L τ hτ hL ρ hχ
  have h := universalSourceWeight_moving_tail_le j n L τ hτ hL ρ hχ
  dsimp only [sourceDepthKernel, sourceTwist]
  rw [tr_twist]
  change Complex.normSq (tr f.1 ((ρ : ℂ) - (τ : ℂ) * Complex.I)) *
    depthKernel L (zetaDepth ρ) ^ j ≤ _
  calc
    Complex.normSq (tr f.1 ((ρ : ℂ) - (τ : ℂ) * Complex.I)) *
        depthKernel L (zetaDepth ρ) ^ j ≤
        (B * universalSourceWeight ((ρ : ℂ) - (τ : ℂ) * Complex.I)) *
          depthKernel L (zetaDepth ρ) ^ j :=
      mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (depthKernel_nonneg _ _) _)
    _ = B * (universalSourceWeight ((ρ : ℂ) - (τ : ℂ) * Complex.I) *
        depthKernel L (zetaDepth ρ) ^ j) := by ring
    _ ≤ B * ((40 * Real.exp 1 * 2 ^ j) /
        (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := mul_le_mul_of_nonneg_left h hB
    _ = _ := by ring

end GaloisForLFunctions.ConjugateDiagonalGeometry
