import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.Detuning
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Absolute sinc weights of dense near-resonances -/

open Finset Real
open scoped symmDiff
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
noncomputable section
variable {I : Type*} [DecidableEq I]

/-- An inverse-width detuning contributes a positive sinc weight. -/
theorem sinc_half {y : ℝ} (hy : |y|≤1/2) : 1/2≤sinc y := by
  have h (t : ℝ) (ht : 0<t) (hh : t≤1/2) : 1/2≤sinc t := by
    rw [sinc_of_ne_zero ht.ne',le_div_iff₀ ht]
    apply le_trans _ (mul_le_sin ht.le (by linarith only [hh,pi_gt_three]))
    apply mul_le_mul_of_nonneg_right _ ht.le
    rw [le_div_iff₀ pi_pos]
    linarith only [pi_lt_four]
  rcases lt_trichotomy y 0 with hneg|hzero|hpos
  · rw [←sinc_neg y]
    exact h _ (neg_pos.mpr hneg) (by rwa [abs_of_neg hneg] at hy)
  · norm_num [hzero]
  · exact h _ hpos (by rwa [abs_of_pos hpos] at hy)

/-- Sum of absolute kernel weights for the empty circuit after deleting
every pair whose symmetric difference is too small. -/
def absoluteWindow (F : Finset (Finset I)) (x : Finset I → ℝ) (r : ℕ) (w : ℝ) : ℝ :=
  ∑ S ∈ F, ∑ T ∈ F.filter (fun T => r<(S ∆ T).card), |sinc (w*(x S-x T)/2)|

/-- Each same-bin macroscopic pair contributes at least half in absolute
value, independently of the starting phase. -/
theorem count_le_absolute (F : Finset (Finset I)) (x : Finset I → ℝ) (r : ℕ) (w : ℝ) :
    (pairCount F r (fun S T => |w*(x S-x T)|≤1):ℝ)/2 ≤ absoluteWindow F x r w := by
  classical
  unfold pairCount absoluteWindow
  rw [Nat.cast_sum,div_eq_mul_inv,sum_mul]
  apply sum_le_sum
  intro S hS
  let U := F.filter fun T => r<(S ∆ T).card ∧ |w*(x S-x T)|≤1
  let V := F.filter fun T => r<(S ∆ T).card
  have hsub : U⊆V := fun _ hT => mem_filter.mpr ⟨(mem_filter.mp hT).1,(mem_filter.mp hT).2.1⟩
  change (U.card:ℝ)*2⁻¹≤∑ T ∈ V, _
  calc
    _ = ∑ _T ∈ U, (1/2:ℝ) := by simp [div_eq_mul_inv]
    _ ≤ ∑ T ∈ U, |sinc (w*(x S-x T)/2)| := by
      apply sum_le_sum
      intro T hT
      apply le_trans (sinc_half ?_) (le_abs_self _)
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact div_le_div_of_nonneg_right (mem_filter.mp hT).2.2 (by norm_num)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)

#print axioms count_le_absolute
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
