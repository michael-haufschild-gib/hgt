import GaloisForLFunctions.HTGeometry.DiscreteTimeCrystalSpinChain
/-!
# Finite-observation stability of time-crystal and localization indicators

Equation (17) of arXiv:2609.04037 defines alternating and unsigned finite-window
indicators. Both are Lipschitz in the mean absolute observation error. Thus
arbitrary noise has a certified effect on the extracted period-doubled amplitude,
without assuming a phase diagram or any dynamics of that noise.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section
/-- DTC demodulation is additive for every finite nonempty window. -/
theorem finiteDTCIndicator_add (N : ℕ) (f g : ℕ → ℝ) :
    finiteDTCIndicator N (fun n => f n + g n) = finiteDTCIndicator N f + finiteDTCIndicator N g := by
  simp only [finiteDTCIndicator, mul_add, Finset.sum_add_distrib]
/-- Differences of signals commute with finite DTC demodulation. -/
theorem finiteDTCIndicator_sub (N : ℕ) (f g : ℕ → ℝ) :
    finiteDTCIndicator N (fun n => f n - g n) = finiteDTCIndicator N f - finiteDTCIndicator N g := by
  simp only [finiteDTCIndicator, mul_sub, Finset.sum_sub_distrib]
/-- Indicator error is bounded by the measured mean absolute signal error. -/
theorem finiteDTCIndicator_lipschitz (N : ℕ) (f g : ℕ → ℝ) :
    |finiteDTCIndicator N f - finiteDTCIndicator N g| ≤
      finiteMBLIndicator N (fun n => f n - g n) := by
  rw [← finiteDTCIndicator_sub]
  exact abs_finiteDTCIndicator_le_finiteMBLIndicator N _
/-- Memory is subadditive under superposition of signals. -/
theorem finiteMBLIndicator_add_le (N : ℕ) (f g : ℕ → ℝ) :
    finiteMBLIndicator N (fun n => f n + g n) ≤ finiteMBLIndicator N f + finiteMBLIndicator N g := by
  unfold finiteMBLIndicator
  rw [← mul_add, ← Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => abs_add_le _ _) (by positivity)
/-- Reversing a signal leaves its unsigned memory unchanged. -/
theorem finiteMBLIndicator_neg (N : ℕ) (f : ℕ → ℝ) :
    finiteMBLIndicator N (fun n => -f n) = finiteMBLIndicator N f := by
  simp [finiteMBLIndicator]
/-- The unsigned memory indicator is also Lipschitz in the mean absolute signal error. -/
theorem finiteMBLIndicator_lipschitz (N : ℕ) (f g : ℕ → ℝ) :
    |finiteMBLIndicator N f - finiteMBLIndicator N g| ≤
      finiteMBLIndicator N (fun n => f n - g n) := by
  apply abs_le.mpr
  have hfg := finiteMBLIndicator_add_le N (fun n => f n - g n) g
  have hgf := finiteMBLIndicator_add_le N (fun n => -(f n - g n)) f
  simp only [sub_add_cancel] at hfg
  rw [finiteMBLIndicator_neg] at hgf
  have heq : (fun n => -(f n - g n) + f n) = g := by funext n; ring
  rw [heq] at hgf
  constructor <;> linarith
/-- Arbitrary additive noise perturbs recovered subharmonic amplitude by at most its mean modulus. -/
theorem finiteDTCIndicator_noisy_periodDoubledSignal (N : ℕ) (a : ℝ) (noise : ℕ → ℝ) :
    |finiteDTCIndicator N (fun n => periodDoubledSignal a n + noise n) - a| ≤
      finiteMBLIndicator N noise := by
  rw [finiteDTCIndicator_add, finiteDTCIndicator_periodDoubledSignal]
  simpa using abs_finiteDTCIndicator_le_finiteMBLIndicator N noise
/-- The same noise budget controls the localization-memory amplitude. -/
theorem finiteMBLIndicator_noisy_periodDoubledSignal (N : ℕ) (a : ℝ) (noise : ℕ → ℝ) :
    abs (finiteMBLIndicator N (fun n => periodDoubledSignal a n + noise n) - |a|) ≤
      finiteMBLIndicator N noise := by
  have h := finiteMBLIndicator_lipschitz N
    (fun n => periodDoubledSignal a n + noise n) (periodDoubledSignal a)
  rw [finiteMBLIndicator_periodDoubledSignal] at h
  simpa only [add_sub_cancel_left] using h
end
end GaloisForLFunctions.HTGeometry
