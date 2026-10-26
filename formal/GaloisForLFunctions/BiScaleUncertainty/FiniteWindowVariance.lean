import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonCoercivityClassification
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MultiGapFermiSchedulesPAdicTracesAndOriginBulkTightness
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Attained variance and optimal integer-window coercivity

The arithmetic mean minimizes squared error on each finite window. Fixing this
center makes the set of valid coercivity constants closed under its finite
infimum, so its best constant is itself valid.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

/-- Arithmetic mean of the actual integer-window signal; the empty mean is zero. -/
def integerWindowMean (N : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Icc 1 N, f n) / (N : ℝ)

/-- The minimum squared distance to constants, evaluated at its explicit minimizer. -/
def integerWindowVariance (N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, (f n - integerWindowMean N f) ^ 2

private theorem sum_Icc_one_eq_range (N : ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, g n) = ∑ j ∈ range N, g (j + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  simpa only [Nat.add_sub_cancel, Nat.add_comm 1] using
    Finset.sum_Ico_eq_sum_range g 1 (N + 1)

/-- The explicit mean attains the minimum about all real centers. -/
theorem integerWindowVariance_le_centered (N : ℕ) (f : ℕ → ℝ) (c : ℝ) :
    integerWindowVariance N f ≤ ∑ n ∈ Icc 1 N, (f n - c) ^ 2 := by
  cases N with
  | zero => simp [integerWindowVariance]
  | succ N =>
    simpa only [integerWindowVariance, integerWindowMean, sum_Icc_one_eq_range,
      Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
      TransHorizonIncidenceMechanics.sum_range_sq_sub_mean_le (fun j => f (j + 1)) N c

/-- Coercivity to some constant is exactly coercivity of the attained mean variance. -/
theorem windowCoercivityBound_iff_variance (K N : ℕ) (C : ℝ) :
    WindowCoercivityBound K N C ↔
      ∀ f : ℕ → ℝ, integerWindowVariance N f ≤ C * biScaleJointEnergy K N f := by
  constructor
  · intro h f
    obtain ⟨c, hc⟩ := h f
    exact (integerWindowVariance_le_centered N f c).trans hc
  · intro h f
    exact ⟨integerWindowMean N f, h f⟩

/-- The infimum of all valid constants is itself valid whenever a valid constant exists. -/
theorem windowCoercivityBound_sInf (K N : ℕ)
    (hne : {C : ℝ | WindowCoercivityBound K N C}.Nonempty) :
    WindowCoercivityBound K N (sInf {C : ℝ | WindowCoercivityBound K N C}) := by
  apply (windowCoercivityBound_iff_variance K N _).mpr
  intro f
  have he0 := biScaleJointEnergy_nonneg K N f
  rcases eq_or_lt_of_le he0 with he | he
  · obtain ⟨C, hC⟩ := hne
    have hc := (windowCoercivityBound_iff_variance K N C).mp hC f
    rw [← he, mul_zero] at hc ⊢
    exact hc
  · apply (div_le_iff₀ he).mp
    apply le_csInf hne
    intro C hC
    exact (div_le_iff₀ he).mpr ((windowCoercivityBound_iff_variance K N C).mp hC f)

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
