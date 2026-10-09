import GaloisForLFunctions.RHTower.RiemannAutocorrWeightedTranslation
import GaloisForLFunctions.RHTower.WeilLogShiftFiniteTailCompensation

/-!
# A global logarithmic-separation envelope for paired kernels

The local translation modulus and the individual inverse-square envelope
together control the difference between any ordered pair of arithmetic indices.
The estimate remains valid when their logarithmic gap exceeds one.
-/

noncomputable section

namespace RHTower

/-- One envelope controls every ordered pair of actual arithmetic kernel
columns, with their logarithmic separation displayed explicitly. -/
theorem exists_pairedLogKernel_logSeparation_envelope :
    ∃ B : ℝ, 0 < B ∧ ∀ (y : ℝ) (n m : ℕ), 1 ≤ n → n ≤ m →
      |pairedLogKernel y m - pairedLogKernel y n| ≤
        (B * Real.exp (2 * |y|)) *
          ((Real.log m - Real.log n) * ((n : ℝ) ^ 2)⁻¹) := by
  obtain ⟨E, hE, htranslate⟩ := exists_riemannAutocorr_translation_envelope
  obtain ⟨A, hA, hindividual⟩ := exists_pairedLogKernel_inverseSquare_envelope
  let B := 2 * (E + A)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro y n m hn hnm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hm0 : (0 : ℝ) < m := hn0.trans_le hnmR
  let δ := Real.log m - Real.log n
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr (Real.log_le_log hn0 hnmR)
  change |pairedLogKernel y m - pairedLogKernel y n| ≤
    (B * Real.exp (2 * |y|)) * (δ * ((n : ℝ) ^ 2)⁻¹)
  by_cases hδ1 : δ ≤ 1
  · have hδabs : |δ| ≤ 1 := by rwa [abs_of_nonneg hδ0]
    have hp : |riemannAutocorr (y + Real.log m) - riemannAutocorr (y + Real.log n)| ≤
        E * δ * Real.exp (-(2 * |y + Real.log n|)) := by
      have heq : y + Real.log m = (y + Real.log n) + δ := by dsimp only [δ]; ring
      rw [heq]
      simpa only [abs_of_nonneg hδ0] using htranslate (y + Real.log n) δ hδabs
    have hm : |riemannAutocorr (y - Real.log m) - riemannAutocorr (y - Real.log n)| ≤
        E * δ * Real.exp (-(2 * |y - Real.log n|)) := by
      have heq : y - Real.log m = (y - Real.log n) + -δ := by dsimp only [δ]; ring
      rw [heq]
      simpa only [abs_neg, abs_of_nonneg hδ0] using
        htranslate (y - Real.log n) (-δ) (by simpa only [abs_neg] using hδabs)
    have hlog := Real.log_natCast_nonneg n
    have hexp : Real.exp (-(2 * Real.log n)) = ((n : ℝ) ^ 2)⁻¹ := by
      rw [show -(2 * Real.log n) = -Real.log ((n : ℝ) ^ 2) by
        rw [Real.log_pow]; norm_num only, Real.exp_neg, Real.exp_log (by positivity)]
    have hterm (z : ℝ) (hz : Real.log n - |y| ≤ |z|) :
        E * δ * Real.exp (-(2 * |z|)) ≤
        (E * Real.exp (2 * |y|)) * (δ * ((n : ℝ) ^ 2)⁻¹) := by
      have he : Real.exp (-(2 * |z|)) ≤
          Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹ := by
        calc
          _ ≤ Real.exp (2 * |y| + -(2 * Real.log n)) :=
            Real.exp_le_exp.mpr (by linarith)
          _ = _ := by rw [Real.exp_add, hexp]
      calc
        _ ≤ (E * δ) * (Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg hE.le hδ0)
        _ = _ := by ring
    have hplus := hterm (y + Real.log n) (by
      simpa only [abs_of_nonneg hlog, add_comm] using abs_sub_abs_le_abs_add (Real.log n) y)
    have hminus := hterm (y - Real.log n) (by
      simpa only [abs_of_nonneg hlog, abs_sub_comm] using abs_sub_abs_le_abs_sub (Real.log n) y)
    calc
      _ = |(riemannAutocorr (y + Real.log m) - riemannAutocorr (y + Real.log n)) +
          (riemannAutocorr (y - Real.log m) - riemannAutocorr (y - Real.log n))| := by
        congr 1
        unfold pairedLogKernel
        ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ (E * Real.exp (2 * |y|)) * (δ * ((n : ℝ) ^ 2)⁻¹) +
          (E * Real.exp (2 * |y|)) * (δ * ((n : ℝ) ^ 2)⁻¹) :=
        add_le_add (hp.trans hplus) (hm.trans hminus)
      _ = ((2 * E) * Real.exp (2 * |y|)) * (δ * ((n : ℝ) ^ 2)⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith : 2 * E ≤ B)
          (Real.exp_pos _).le) (by positivity)
  · have hinv : ((m : ℝ) ^ 2)⁻¹ ≤ ((n : ℝ) ^ 2)⁻¹ := by gcongr
    have hpm : pairedLogKernel y m ≤ A * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹ :=
      (hindividual y m (hn.trans hnm)).trans
        (mul_le_mul_of_nonneg_left hinv (by positivity))
    have hpn := hindividual y n hn
    have hscale : 2 * A ≤ B * δ := by
      have hlarge : 1 ≤ δ := by linarith
      dsimp only [B]
      nlinarith
    calc
      _ ≤ |pairedLogKernel y m| + |pairedLogKernel y n| := abs_sub _ _
      _ = pairedLogKernel y m + pairedLogKernel y n := by
        rw [abs_of_pos (pairedLogKernel_pos y m), abs_of_pos (pairedLogKernel_pos y n)]
      _ ≤ A * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹ +
          A * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹ := add_le_add hpm hpn
      _ = (2 * A) * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹ := by ring
      _ ≤ (B * δ) * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hscale (Real.exp_pos _).le) (by positivity)
      _ = _ := by ring

end RHTower
