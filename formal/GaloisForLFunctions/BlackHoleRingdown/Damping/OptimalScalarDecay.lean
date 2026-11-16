import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Optimal damping of a scalar mode

For `a'' + 2|d| a' + ω² a = 0`, the slow characteristic decay rate is
`|d| - √(d² - ω²)`, with the real square root zero in the oscillatory regime.
It is maximized at critical damping. A zero-frequency mode cannot decay.
This is the scalar optimization underlying §6.1 of arXiv:2610.33953.
-/

noncomputable section
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Slow characteristic decay rate, including the underdamped and zero-frequency cases. -/
def scalarDecayRate (d ω : ℝ) : ℝ := |d| - Real.sqrt (d ^ 2 - ω ^ 2)

/-- Every scalar mode has nonnegative characteristic decay. -/
theorem scalarDecayRate_nonneg (d ω : ℝ) : 0 ≤ scalarDecayRate d ω := by
  unfold scalarDecayRate
  apply sub_nonneg.mpr
  apply (Real.sqrt_le_iff).mpr
  exact ⟨abs_nonneg d, by nlinarith only [sq_abs d, sq_nonneg ω]⟩

/-- Damping cannot beat the undamped natural frequency. -/
theorem scalarDecayRate_le_frequency (d ω : ℝ) : scalarDecayRate d ω ≤ |ω| := by
  unfold scalarDecayRate
  by_cases h : |d| ≤ |ω|
  · linarith only [Real.sqrt_nonneg (d ^ 2 - ω ^ 2), h]
  · have hdiff : 0 ≤ d ^ 2 - ω ^ 2 := by
      nlinarith only [sq_abs d, sq_abs ω, abs_nonneg d, abs_nonneg ω, h]
    have hs := Real.sq_sqrt hdiff
    have hp := mul_nonneg (abs_nonneg ω) (le_of_lt (sub_pos.mpr (lt_of_not_ge h)))
    nlinarith only [hs, sq_abs d, sq_abs ω, hp,
      Real.sqrt_nonneg (d ^ 2 - ω ^ 2), h]

/-- Critical damping attains the optimal rate. -/
@[simp] theorem scalarDecayRate_critical (ω : ℝ) : scalarDecayRate ω ω = |ω| := by
  simp [scalarDecayRate]

/-- Zero-frequency modes have zero rate at every damping. -/
@[simp] theorem scalarDecayRate_zero (d : ℝ) : scalarDecayRate d 0 = 0 := by
  simp [scalarDecayRate, Real.sqrt_sq_eq_abs]

/-- Only critical damping maximizes a nonzero mode; zero modes are the exact exception. -/
theorem scalarDecayRate_eq_frequency_iff (d ω : ℝ) :
    scalarDecayRate d ω = |ω| ↔ ω = 0 ∨ |d| = |ω| := by
  constructor
  · intro he
    by_cases h : |d| ≤ |ω|
    · right
      unfold scalarDecayRate at he
      linarith only [he, h, Real.sqrt_nonneg (d ^ 2 - ω ^ 2)]
    · left
      have hdiff : 0 ≤ d ^ 2 - ω ^ 2 := by
        nlinarith only [sq_abs d, sq_abs ω, abs_nonneg d, abs_nonneg ω, h]
      have hs := Real.sq_sqrt hdiff
      unfold scalarDecayRate at he
      have hz : |ω| = 0 := by
        nlinarith only [hs, he, sq_abs d, sq_abs ω, h]
      exact abs_eq_zero.mp hz
  · rintro (rfl | h)
    · simp
    · have hs : d ^ 2 = ω ^ 2 := by rw [← sq_abs d, h, sq_abs ω]
      simp [scalarDecayRate, hs, h]

/-- Increasing the natural frequency cannot worsen the slow rate at fixed damping. -/
theorem scalarDecayRate_mono_frequency (d : ℝ) :
    Monotone (fun ω : Set.Ici (0 : ℝ) => scalarDecayRate d ω) := by
  intro a b hab
  unfold scalarDecayRate
  apply sub_le_sub_left
  apply Real.sqrt_le_sqrt
  have hs : (a : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 :=
    (sq_le_sq₀ (show 0 ≤ (a : ℝ) from a.property)
      (show 0 ≤ (b : ℝ) from b.property)).mpr (show (a : ℝ) ≤ b from hab)
  exact sub_le_sub_left hs _

/-- The maximum over all damping choices is attained, with no compactness assumption. -/
theorem scalarDecayRate_isGreatest (ω : ℝ) :
    IsGreatest (Set.range (fun d : ℝ => scalarDecayRate d ω)) |ω| := by
  refine ⟨⟨ω, scalarDecayRate_critical ω⟩, ?_⟩
  rintro _ ⟨d, rfl⟩
  exact scalarDecayRate_le_frequency d ω

#print axioms scalarDecayRate_eq_frequency_iff
#print axioms scalarDecayRate_isGreatest
#print axioms scalarDecayRate_mono_frequency

end GaloisForLFunctions.BlackHoleRingdown
