import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanVerticalBounds
import GaloisForLFunctions.RHTower.XiMassJetIntegrand
import GaloisForLFunctions.HTGeometry.FinitePoleVerticalContourShift

/-!
# Vanishing horizontal edges of the averaged Narain contour

At the arithmetic good heights, reciprocal zeta grows polynomially.
The mean numerator retains enough exponential decay to absorb that loss,
including the inverse-Mellin weight on the full boundary strip.
-/

open Complex RHTower Set Filter Topology MeasureTheory
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Exponential decay on the actual escaping horizontal edges of the physical Mellin strip. -/
theorem exists_narainMellinMean_goodHeight_bound (Y Z : Height) :
    ∃ (C : ℝ) (N k₀ : ℕ), 0 ≤ C ∧ ∀ k : ℕ, k₀ ≤ k → 2 ≤ goodHeight k →
      ∀ u : ℂ, 0 ≤ u.re → u.re ≤ 3 / 2 → |u.im| = goodHeight k / 2 →
        ‖narainMellinMean Y Z u‖ ≤ C * (1 + goodHeight k) ^ N *
          Real.exp (-(Real.pi * goodHeight k / 4)) := by
  obtain ⟨C, N, hC, h⟩ := exists_narainMellinMean_strip_bound Y Z (B := 2) (by norm_num)
  obtain ⟨K, M, k₀, hK, hζ⟩ := exists_norm_inv_zeta_goodHeight 4 (by norm_num)
  refine ⟨C * K, N + M, k₀, mul_nonneg hC hK, ?_⟩
  intro k hk hT u hu₀ hu₁ huim
  have him : |(1 + 2 * u).im| = goodHeight k := by
    have he : (1 + 2 * u).im = 2 * u.im := by simp
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), huim]
    ring
  have hz := hζ k hk (1 + 2 * u) (by simp; linarith only [hu₀])
    (by simp; linarith only [hu₁]) him
  rw [him] at hz
  have hb := h u (by rw [abs_of_nonneg hu₀]; linarith only [hu₁])
    (by rw [huim]; linarith only [hT])
  rw [huim, show -(Real.pi * (goodHeight k / 2) / 2) =
    -(Real.pi * goodHeight k / 4) by ring] at hb
  calc
    _ ≤ _ := hb
    _ ≤ C * (1 + goodHeight k) ^ N * Real.exp (-(Real.pi * goodHeight k / 4)) *
        (K * (1 + goodHeight k) ^ M) := by
      gcongr
      linarith only [hT]
    _ = _ := by rw [pow_add]; ring

/-- Polynomial losses at the good heights are absorbed by half the remaining exponential. -/
theorem exists_narainMellinMean_goodHeight_exp_bound (Y Z : Height) :
    ∃ (C : ℝ) (k₀ : ℕ), 0 ≤ C ∧ ∀ k : ℕ, k₀ ≤ k → 2 ≤ goodHeight k →
      ∀ u : ℂ, 0 ≤ u.re → u.re ≤ 3 / 2 → |u.im| = goodHeight k / 2 →
        ‖narainMellinMean Y Z u‖ ≤ C * Real.exp (-(Real.pi * goodHeight k / 8)) := by
  obtain ⟨C, N, k₀, hC, h⟩ := exists_narainMellinMean_goodHeight_bound Y Z
  let D : ℝ := (Nat.factorial N : ℝ) / (Real.pi / 8) ^ N * Real.exp (Real.pi / 8)
  refine ⟨C * D, k₀, by dsimp only [D]; positivity, ?_⟩
  intro k hk hT u hu₀ hu₁ huim
  have hp := _root_.HTGeometry.one_add_pow_le_const_mul_exp
    (show 0 ≤ goodHeight k by linarith only [hT])
    (show 0 < Real.pi / 8 by positivity) N
  change (1 + goodHeight k) ^ N ≤ D * Real.exp (Real.pi / 8 * goodHeight k) at hp
  have he : Real.exp (Real.pi / 8 * goodHeight k) *
      Real.exp (-(Real.pi * goodHeight k / 4)) = Real.exp (-(Real.pi * goodHeight k / 8)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ C * (1 + goodHeight k) ^ N * Real.exp (-(Real.pi * goodHeight k / 4)) :=
      h k hk hT u hu₀ hu₁ huim
    _ ≤ C * (D * Real.exp (Real.pi / 8 * goodHeight k)) *
        Real.exp (-(Real.pi * goodHeight k / 4)) := by gcongr
    _ = C * D * (Real.exp (Real.pi / 8 * goodHeight k) *
        Real.exp (-(Real.pi * goodHeight k / 4))) := by ring
    _ = _ := by rw [he]

private theorem horizontal_tendsto_zero (Y Z : Height) {y : ℝ} (hy : 0 < y)
    (T : ℕ → ℝ) (hT : ∀ k, |T k| = goodHeight k / 2) :
    Tendsto (fun k => HIntegral (fun s : ℂ =>
      (y : ℂ) ^ (-s) * narainMellinMean Y Z (s - 1 / 2)) (1 / 2) 2 (T k)) atTop (𝓝 0) := by
  obtain ⟨C, k₀, hC, h⟩ := exists_narainMellinMean_goodHeight_exp_bound Y Z
  let P : ℝ := y ^ ((1 : ℝ) / 2 + 3) + y ^ ((1 : ℝ) / 2 - 3)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have he : Tendsto (fun k => Real.exp (-(Real.pi * goodHeight k / 8))) atTop (𝓝 0) := by
    convert Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (Tendsto.const_mul_atTop (show 0 < Real.pi / 8 by positivity) tendsto_goodHeight)) using 1
    funext k
    dsimp only [Function.comp_apply]
    congr 1
    ring
  have hlim : Tendsto (fun k => (P * C * (3 / 2)) *
      Real.exp (-(Real.pi * goodHeight k / 8))) atTop (𝓝 0) := by
    simpa using he.const_mul (P * C * (3 / 2))
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop k₀,
    (tendsto_atTop.1 tendsto_goodHeight) 2] with k hk hlarge
  rw [HIntegral]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := 2)
    (f := fun r : ℝ => (y : ℂ) ^ (-((r : ℂ) + (T k : ℂ) * I)) *
      narainMellinMean Y Z (((r : ℂ) + (T k : ℂ) * I) - 1 / 2))
    (C := P * C * Real.exp (-(Real.pi * goodHeight k / 8))) (fun r hr => by
      rw [uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hr
      have hp : ‖(y : ℂ) ^ (-((r : ℂ) + (T k : ℂ) * I))‖ ≤ P :=
        norm_cpow_strip_le hy _ (by simp; linarith only [hr.2])
          (by simp; linarith only [hr.1])
      have hm := h k hk hlarge (((r : ℂ) + (T k : ℂ) * I) - 1 / 2)
        (by simp; linarith only [hr.1]) (by simp; linarith only [hr.2]) (by simpa using hT k)
      rw [norm_mul]
      calc
        _ ≤ P * (C * Real.exp (-(Real.pi * goodHeight k / 8))) :=
          mul_le_mul hp hm (norm_nonneg _) hP
        _ = _ := by ring)
  refine hb.trans (le_of_eq ?_)
  norm_num
  ring

/-- Both horizontal sides vanish for the actual weighted mean Mellin transform. -/
theorem narainMellinMean_horizontal_tendsto_zero (Y Z : Height) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun k => HIntegral (fun s : ℂ =>
      (y : ℂ) ^ (-s) * narainMellinMean Y Z (s - 1 / 2)) (1 / 2) 2
        (goodHeight k / 2)) atTop (𝓝 0) ∧
    Tendsto (fun k => HIntegral (fun s : ℂ =>
      (y : ℂ) ^ (-s) * narainMellinMean Y Z (s - 1 / 2)) (1 / 2) 2
        (-(goodHeight k / 2))) atTop (𝓝 0) := by
  have hpos (k : ℕ) : 0 ≤ goodHeight k / 2 := by linarith only [one_le_goodHeight k]
  exact ⟨horizontal_tendsto_zero Y Z hy _ (fun k => abs_of_nonneg (hpos k)),
    horizontal_tendsto_zero Y Z hy _ (fun k => by rw [abs_neg, abs_of_nonneg (hpos k)])⟩

#print axioms narainMellinMean_horizontal_tendsto_zero
#print axioms exists_narainMellinMean_goodHeight_bound
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
