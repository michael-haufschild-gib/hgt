import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanVKEnvelope
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanBoundaryTail
import GaloisForLFunctions.RHTower.ExpDecayFourierAnalytic

/-!
# Exponential decay of the actual Narain Mellin boundary

The compact arithmetic rectangle and the high-frequency strip envelope give a global exponential majorant. This controls complex-clock integrability and uniform truncated tails.
-/

open Complex RHTower Filter MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

private theorem polynomial_boundary_absorption (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
      (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2)) ≤
        D * Real.exp (-(Real.pi * |t| / 4)) := by
  let D : ℝ := (Nat.factorial N : ℝ) / (Real.pi / 4) ^ N * Real.exp (Real.pi / 4)
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro t
  have hp := _root_.HTGeometry.one_add_pow_le_const_mul_exp (abs_nonneg t)
    (show 0 < Real.pi / 4 by positivity) N
  change (1 + |t|) ^ N ≤ D * Real.exp (Real.pi / 4 * |t|) at hp
  calc
    _ ≤ (D * Real.exp (Real.pi / 4 * |t|)) * Real.exp (-(Real.pi * |t| / 2)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = D * Real.exp (-(Real.pi * |t| / 4)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Central removability and the strip envelope give one global exponential spectral majorant. -/
theorem exists_narainMeanBoundary_exponential_bound (Y Z : Height) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖narainMellinMean Y Z ((t : ℂ) * I)‖ ≤ C * Real.exp (-(Real.pi * |t| / 4)) := by
  obtain ⟨B, n, hB, hbase⟩ := exists_narainMellinMean_boundary_bound Y Z
  obtain ⟨δ, T₀, C, m, hδ, hT₀, hTexp, hC, henv⟩ := exists_narainMellinMean_vk_envelope Y Z
  obtain ⟨hd, hd8, hrect⟩ := henv T₀ le_rfl
  have hQ : 0 ≤ narainVKCost T₀ := (zero_le_one : (0 : ℝ) ≤ 1).trans
    (one_le_narainVKCost (by linarith only [hTexp, hT₀]))
  obtain ⟨D, hD, hDn⟩ := polynomial_boundary_absorption n
  obtain ⟨E, hE, hEm⟩ := polynomial_boundary_absorption m
  refine ⟨B * D + C * narainVKCost T₀ * E, by positivity, ?_⟩
  intro t
  by_cases ht : |t| ≤ T₀
  · have hb := (hrect ((t : ℂ) * I) (by simpa using hd.le) (by simp) (by simpa using ht)).2
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hb
    calc
      _ ≤ C * (1 + |t|) ^ m * Real.exp (-(Real.pi * |t| / 2)) * narainVKCost T₀ := hb
      _ = (C * narainVKCost T₀) * ((1 + |t|) ^ m * Real.exp (-(Real.pi * |t| / 2))) := by ring
      _ ≤ (C * narainVKCost T₀) * (E * Real.exp (-(Real.pi * |t| / 4))) :=
        mul_le_mul_of_nonneg_left (hEm t) (mul_nonneg hC hQ)
      _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg hB hD) (Real.exp_nonneg (-(Real.pi * |t| / 4)))]
  · have ht1 : 1 ≤ |t| := by linarith only [lt_of_not_ge ht, hT₀]
    calc
      _ ≤ B * (1 + |t|) ^ n * Real.exp (-(Real.pi * |t| / 2)) := hbase t ht1
      _ = B * ((1 + |t|) ^ n * Real.exp (-(Real.pi * |t| / 2))) := by ring
      _ ≤ B * (D * Real.exp (-(Real.pi * |t| / 4))) :=
        mul_le_mul_of_nonneg_left (hDn t) hB
      _ ≤ _ := by
        have hn := mul_nonneg (mul_nonneg (mul_nonneg hC hQ) hE)
          (Real.exp_nonneg (-(Real.pi * |t| / 4)))
        nlinarith only [hn]

/-- Complex clock frequencies inside the exponential strip have absolutely convergent boundary integrals. -/
theorem integrable_narainMeanBoundary_complex (Y Z : Height) {z : ℂ}
    (hz : |z.im| < Real.pi / 4) :
    Integrable (fun t : ℝ => Complex.exp (z * ((t : ℂ) * I)) * narainMellinMean Y Z ((t : ℂ) * I)) := by
  obtain ⟨C, hC, hb⟩ := exists_narainMeanBoundary_exponential_bound Y Z
  have hc : Continuous (fun t : ℝ => narainMellinMean Y Z ((t : ℂ) * I)) := by
    simpa using continuous_narainMellinMean_vertical Y Z (a := 0) le_rfl (by norm_num)
  have h := integrable_expFourier_kernel (ε := Real.pi / 4) hc.aestronglyMeasurable hC
    (fun t => by simpa only [div_mul_eq_mul_div] using hb t)
    (w := -z) (by simpa using hz)
  apply h.congr
  filter_upwards [] with t
  rw [mul_comm]
  congr 2
  ring

/-- The discarded tails stay exponentially small throughout a fixed complex clock strip. -/
theorem exists_narainMeanBoundary_complex_tail_bound (Y Z : Height) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (T : ℝ), |z.im| ≤ Real.pi / 8 → 0 ≤ T →
      ‖(∫ t : ℝ, Complex.exp (z * ((t : ℂ) * I)) * narainMellinMean Y Z ((t : ℂ) * I)) -
        ∫ t : ℝ in (-T)..T, Complex.exp (z * ((t : ℂ) * I)) *
          narainMellinMean Y Z ((t : ℂ) * I)‖ ≤ C * Real.exp (-(Real.pi * T / 8)) := by
  obtain ⟨C, hC, hb⟩ := exists_narainMeanBoundary_exponential_bound Y Z
  refine ⟨2 * C / (Real.pi / 8), by positivity, ?_⟩
  intro z T hz hT
  have hint := integrable_narainMeanBoundary_complex Y Z
    (lt_of_le_of_lt hz (by nlinarith only [Real.pi_pos]))
  have h := norm_integral_sub_truncated_le hint hT (show 0 < Real.pi / 8 by positivity)
    (C := C) (fun t ht => by
      have hp : -(z.im * t) ≤ (Real.pi / 8) * |t| := by
        calc
          _ ≤ |z.im * t| := neg_le_abs _
          _ = |z.im| * |t| := abs_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
      have hn : ‖Complex.exp (z * ((t : ℂ) * I))‖ = Real.exp (-(z.im * t)) := by
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re, Complex.mul_im]
      rw [norm_mul, hn]
      calc
        _ ≤ Real.exp ((Real.pi / 8) * |t|) *
            (C * Real.exp (-(Real.pi * |t| / 4))) :=
          mul_le_mul (Real.exp_le_exp.mpr hp) (hb t) (norm_nonneg _) (Real.exp_nonneg _)
        _ = C * (Real.exp ((Real.pi / 8) * |t|) * Real.exp (-(Real.pi * |t| / 4))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring)
  simpa only [div_mul_eq_mul_div] using h

#print axioms exists_narainMeanBoundary_exponential_bound
#print axioms integrable_narainMeanBoundary_complex
#print axioms exists_narainMeanBoundary_complex_tail_bound
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
