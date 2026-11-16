import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCompletedThetaSquaresHavePolynomialGrowth
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubeZetaReciprocalHasPolynomialGrowth
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaMellinReciprocalHasExponentialGrowth

/-!
# Gaussian decay of the untwisted squarefree continuation

The completed theta pairing has cubic growth. Cube removal and the pole-clearing
factor raise this to degree six; division by the Bessel Mellin factor contributes
at most exponential growth in height. Multiplication by `exp(w²)` absorbs both
bounds uniformly on closed strips inside `5/8<Re w<13/6`.
-/

noncomputable section
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicEisenstein

private theorem unitFrequencyWeight_inv_bound (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ B →
      ‖(unitFrequencyWeight s)⁻¹‖ ≤ C := by
  let A : ℝ := 4 * Real.pi * ‖cuspFrequency 1‖
  have hA : 0 < A := by
    have hξ := norm_pos_iff.mpr (cuspFrequency_ne_zero 1 one_ne_zero)
    dsimp only [A]
    positivity
  refine ⟨Real.exp (|Real.log A| * B), (Real.exp_pos _).le, ?_⟩
  intro s hs hB
  change ‖(((A : ℂ) ^ (-s))⁻¹)‖ ≤ _
  rw [Complex.cpow_neg, inv_inv, Complex.norm_cpow_eq_rpow_re_of_pos hA,
    Real.rpow_def_of_pos hA]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul (le_abs_self _) hB hs (abs_nonneg _)

/-- Cube removal leaves at most degree-six growth in the completed untwisted series. -/
theorem completedUntwistedS_vertical_bound (a B : ℝ) (ha : 5 / 4 < a)
    (haB : a ≤ B) (hB : B < 13 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ B → 1 ≤ |s.im| →
      ‖completedUntwistedS s‖ ≤ C * (1 + ‖s‖) ^ 6 := by
  obtain ⟨C, hC, hc⟩ := completedThetaSquares_vertical_bound a B (by linarith) haB hB
  obtain ⟨D, hD, hd⟩ := clearedCubeZeta_inv_vertical_bound a ha
  obtain ⟨F, hF, hf⟩ := unitFrequencyWeight_inv_bound B
  let K : ℝ := ‖(2 * star rationalSourceThetaScalar ^ 2 * (2 / 3) : ℂ)⁻¹‖
  have hK : 0 ≤ K := norm_nonneg _
  refine ⟨2 * C * F * K * D, by positivity, ?_⟩
  intro s hsa hsb hsi
  have hfull := (hc s hsa hsb hsi).2.2
  have hcube := hd s hsa hsi
  have hfreq := hf s (by linarith) hsb
  have hsub : ‖s - 4 / 3‖ ≤ 2 * (1 + ‖s‖) := by
    have h := norm_sub_le s (4 / 3 : ℂ)
    norm_num at h
    linarith only [h, norm_nonneg s]
  have hheight : 1 + |s.im| ^ 2 ≤ (1 + ‖s‖) ^ 2 := by
    have h := Complex.abs_im_le_norm s
    nlinarith only [h, abs_nonneg s.im, norm_nonneg s]
  have hcube' := hcube.trans (mul_le_mul_of_nonneg_left hheight hD)
  have heq : completedUntwistedS s = (s - 4 / 3) * completedUnramified s *
      (unitFrequencyWeight s)⁻¹ * (2 * star rationalSourceThetaScalar ^ 2 * (2 / 3))⁻¹ *
        (clearedCubeZeta s)⁻¹ := by
    simp only [completedUntwistedS, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, norm_mul, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ (2 * (1 + ‖s‖)) * (C * (1 + ‖s‖) ^ 3) * F * K *
        (D * (1 + ‖s‖) ^ 2) := by gcongr
    _ = _ := by ring

/-- Removing the Mellin factor gives exponential growth on the wider squarefree strip. -/
theorem continuedUntwistedTheta_vertical_bound (a B : ℝ) (ha : 5 / 8 < a)
    (haB : a ≤ B) (hB : B < 13 / 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ B → 1 ≤ |w.im| →
      ‖continuedUntwistedTheta w‖ ≤
        C * (1 + ‖w‖) ^ 6 * Real.exp (4 * Real.pi * |w.im|) := by
  obtain ⟨C, hC, hc⟩ := completedUntwistedS_vertical_bound (2 * a) (2 * B)
    (by linarith) (by linarith) (by linarith)
  obtain ⟨D, hD, hd⟩ := besselSqMellin_inv_vertical_bound a B (by linarith)
  refine ⟨64 * C * D, by positivity, ?_⟩
  intro w hwa hwb hwi
  have hi : 1 ≤ |(2 * w).im| := by
    have he : (2 * w).im = 2 * w.im := by simp
    rw [he, abs_mul]
    norm_num
    linarith only [hwi]
  have hs := hc (2 * w) (by simp; linarith) (by simp; linarith) hi
  have hm := hd w hwa hwb hwi
  have hn : 1 + ‖2 * w‖ ≤ 2 * (1 + ‖w‖) := by
    rw [norm_mul]
    norm_num
    linarith
  have hs' : ‖completedUntwistedS (2 * w)‖ ≤ C * (2 * (1 + ‖w‖)) ^ 6 :=
    hs.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn 6) hC)
  rw [continuedUntwistedTheta, div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (C * (2 * (1 + ‖w‖)) ^ 6) * (D * Real.exp (4 * Real.pi * |w.im|)) := by gcongr
    _ = _ := by ring

/-- Gaussian smoothing absorbs the completed-series and reciprocal Mellin growth. -/
theorem continuedUntwistedTheta_gaussian_vertical_bound (a B : ℝ) (ha : 5 / 8 < a)
    (haB : a ≤ B) (hB : B < 13 / 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ B → 1 ≤ |w.im| →
      ‖Complex.exp (w ^ 2) * continuedUntwistedTheta w‖ ≤ C * (1 + w.im ^ 2)⁻¹ := by
  obtain ⟨C, hC, hc⟩ := continuedUntwistedTheta_vertical_bound a B ha haB hB
  have hB0 : 0 ≤ B := by linarith
  let E : ℝ := B ^ 2 + (4 * Real.pi + 8) ^ 2 / 4
  refine ⟨C * (1 + B) ^ 6 * Real.exp E, by positivity, ?_⟩
  intro w hwa hwb hwi
  let t : ℝ := |w.im|
  have ht : 0 ≤ t := abs_nonneg _
  have ht2 : t ^ 2 = w.im ^ 2 := sq_abs _
  have hw0 : 0 ≤ w.re := by linarith
  have hn : 1 + ‖w‖ ≤ (1 + B) * (1 + t) := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_nonneg hw0] at h
    nlinarith only [h, hwb, mul_nonneg hB0 ht]
  have hsq : w.re ^ 2 ≤ B ^ 2 := by nlinarith only [hw0, hwb]
  have htwo : 1 + t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith only [ht]
  have hnorm : ‖Complex.exp (w ^ 2)‖ = Real.exp (w.re ^ 2 - t ^ 2) := by
    rw [Complex.norm_exp, ht2]
    congr 1
    simp only [pow_two, Complex.mul_re]
  have hgeom : (1 + t) ^ 8 * Real.exp (4 * Real.pi * t) *
      Real.exp (w.re ^ 2 - t ^ 2) ≤ Real.exp E := by
    calc
      _ ≤ Real.exp (8 * t) * Real.exp (4 * Real.pi * t) *
          Real.exp (w.re ^ 2 - t ^ 2) := by
        gcongr
        exact GaloisForLFunctions.one_add_pow_le_exp ht 8
      _ = Real.exp (w.re ^ 2 - t ^ 2 + (4 * Real.pi + 8) * t) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp E := by
        apply Real.exp_le_exp.mpr
        dsimp only [E]
        linarith only [hsq, GaloisForLFunctions.neg_sq_add_mul_le t (4 * Real.pi + 8)]
  have hseries : ‖continuedUntwistedTheta w‖ ≤
      C * ((1 + B) * (1 + t)) ^ 6 * Real.exp (4 * Real.pi * t) := by
    exact (hc w hwa hwb hwi).trans (by gcongr)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + w.im ^ 2), ← ht2,
    norm_mul, hnorm]
  calc
    _ ≤ Real.exp (w.re ^ 2 - t ^ 2) *
        (C * ((1 + B) * (1 + t)) ^ 6 * Real.exp (4 * Real.pi * t)) * (1 + t) ^ 2 := by
      gcongr
    _ = C * (1 + B) ^ 6 * ((1 + t) ^ 8 * Real.exp (4 * Real.pi * t) *
        Real.exp (w.re ^ 2 - t ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgeom (by positivity)

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
