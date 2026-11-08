import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanVKEnvelope
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanBoundaryExponential
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.ComplexMellinShift

/-!
# Arithmetic contour bounds at complex clock frequencies

The finite Mellin rectangle and exponential boundary tails control the actual transform uniformly in a fixed complex clock strip.
-/

open Complex RHTower Filter MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The actual boundary transform admits a finite-height arithmetic contour bound.
The two errors are the left edge and exponentially small horizontal edges and tails. -/
theorem exists_narainMeanBoundary_complex_vk_contour_bound (Y Z : Height) :
    ∃ δ T₀ C : ℝ, ∃ N : ℕ, 0 < δ ∧ 3 ≤ T₀ ∧
      Real.exp (Real.exp 1) ≤ T₀ ∧ 0 ≤ C ∧
      ∀ (z : ℂ) (T : ℝ), 0 ≤ z.re → |z.im| ≤ Real.pi / 8 → T₀ ≤ T →
        ‖∫ t : ℝ, Complex.exp (z * ((t : ℂ) * I)) * narainMellinMean Y Z ((t : ℂ) * I)‖ ≤
          C * (1 + T) ^ N * narainVKCost T *
            (Real.exp (-(narainVKWidth δ T * z.re)) + Real.exp (-(Real.pi * T / 8))) := by
  obtain ⟨δ, T₀, C, N, hδ, hT₀, hTexp, hC, henv⟩ := exists_narainMellinMean_vk_envelope Y Z
  obtain ⟨B, hB, htail⟩ := exists_narainMeanBoundary_complex_tail_bound Y Z
  refine ⟨δ, T₀, 2 * C + B, N + 1, hδ, hT₀, hTexp, by positivity, ?_⟩
  intro z T hL hz hT
  have hT3 : 3 ≤ T := hT₀.trans hT
  have hT0 : 0 ≤ T := by linarith only [hT3]
  have hQ : 1 ≤ narainVKCost T := one_le_narainVKCost (by linarith only [hTexp, hT, hT3])
  obtain ⟨hd, hd8, hrect⟩ := henv T hT
  have hfinite := norm_finite_complex_mellin_shift_le hd.le hT0 hL hz
    (show Real.pi / 8 ≤ Real.pi / 2 by nlinarith only [Real.pi_pos]) (mul_nonneg hC (zero_le_one.trans hQ))
    (N := N) (fun u hlo hhi ht => (hrect u hlo hhi ht).1)
    (fun u hlo hhi ht => by
      have h := (hrect u hlo hhi ht).2
      calc
        _ ≤ C * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) *
            narainVKCost T := h
        _ = _ := by
          rw [show -(Real.pi / 2 * |u.im|) = -(Real.pi * |u.im| / 2) by ring]
          ring)
  have htail' := htail z T hz hT0
  have hp : 1 ≤ (1 + T) ^ (N + 1) := one_le_pow₀ (by linarith only [hT0])
  have hpoly : T * (1 + T) ^ N ≤ (1 + T) ^ (N + 1) := by
    rw [pow_succ]
    nlinarith only [pow_nonneg (show 0 ≤ 1 + T by positivity) N]
  have hdpoly : narainVKWidth δ T * (1 + T) ^ N ≤ (1 + T) ^ (N + 1) := by
    rw [pow_succ]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right (show narainVKWidth δ T ≤ 1 + T by linarith only [hd8, hT0])
        (show 0 ≤ (1 + T) ^ N by positivity)
  have he : Real.exp (-((Real.pi / 2 - Real.pi / 8) * T)) ≤ Real.exp (-(Real.pi * T / 8)) := by
    have hprod := mul_le_mul_of_nonneg_right
      (show Real.pi / 8 ≤ Real.pi / 2 - Real.pi / 8 by linarith only [Real.pi_pos]) hT0
    apply Real.exp_le_exp.mpr
    linarith only [hprod]
  have hvertical : 2 * T * (C * narainVKCost T) * (1 + T) ^ N *
      Real.exp (-(narainVKWidth δ T * z.re)) ≤
        (2 * C) * (1 + T) ^ (N + 1) * narainVKCost T *
          Real.exp (-(narainVKWidth δ T * z.re)) := by
    calc
      _ = (2 * C) * (T * (1 + T) ^ N) * narainVKCost T *
          Real.exp (-(narainVKWidth δ T * z.re)) := by ring
      _ ≤ _ := by gcongr
  have hhorizontal : 2 * narainVKWidth δ T * (C * narainVKCost T) * (1 + T) ^ N *
      Real.exp (-((Real.pi / 2 - Real.pi / 8) * T)) ≤
        (2 * C) * (1 + T) ^ (N + 1) * narainVKCost T * Real.exp (-(Real.pi * T / 8)) := by
    calc
      _ = (2 * C) * (narainVKWidth δ T * (1 + T) ^ N) * narainVKCost T *
          Real.exp (-((Real.pi / 2 - Real.pi / 8) * T)) := by ring
      _ ≤ _ := by gcongr
  have htailCost : B * Real.exp (-(Real.pi * T / 8)) ≤
      B * (1 + T) ^ (N + 1) * narainVKCost T * Real.exp (-(Real.pi * T / 8)) := by
    calc
      _ = B * 1 * 1 * Real.exp (-(Real.pi * T / 8)) := by ring
      _ ≤ _ := by gcongr
  have htriangle := norm_add_le
    (∫ t : ℝ in (-T)..T, Complex.exp (z * ((t : ℂ) * I)) * narainMellinMean Y Z ((t : ℂ) * I))
    ((∫ t : ℝ, Complex.exp (z * ((t : ℂ) * I)) * narainMellinMean Y Z ((t : ℂ) * I)) -
      ∫ t : ℝ in (-T)..T, Complex.exp (z * ((t : ℂ) * I)) * narainMellinMean Y Z ((t : ℂ) * I))
  have hcancel (a b : ℂ) : a + (b - a) = b := by ring
  rw [hcancel] at htriangle
  have hv := (add_le_add hvertical hhorizontal).trans_eq (by ring :
      (2 * C) * (1 + T) ^ (N + 1) * narainVKCost T * Real.exp (-(narainVKWidth δ T * z.re)) +
      (2 * C) * (1 + T) ^ (N + 1) * narainVKCost T * Real.exp (-(Real.pi * T / 8)) =
      (2 * C) * (1 + T) ^ (N + 1) * narainVKCost T *
        (Real.exp (-(narainVKWidth δ T * z.re)) + Real.exp (-(Real.pi * T / 8))))
  have htotal := htriangle.trans (add_le_add (hfinite.trans hv) (htail'.trans htailCost))
  exact htotal.trans (by
    have hnonneg : 0 ≤ B * (1 + T) ^ (N + 1) * narainVKCost T *
        Real.exp (-(narainVKWidth δ T * z.re)) := by positivity
    nlinarith only [hnonneg])

#print axioms exists_narainMeanBoundary_complex_vk_contour_bound
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
