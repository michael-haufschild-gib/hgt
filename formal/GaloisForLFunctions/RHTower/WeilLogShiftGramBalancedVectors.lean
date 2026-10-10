import GaloisForLFunctions.RHTower.WeilLogShiftGramCoordinates

/-! The actual coordinate dictionary supplies a balanced spanning family of
coefficient vectors, discharging the two inputs to quadratic local surjectivity. -/

open scoped BigOperators
noncomputable section
namespace RHTower
namespace FiniteWeilGramCoordinates

variable {s : Finset ℕ} (D : FiniteWeilGramCoordinates s)

def coefficientBalance (w : D.tests) : s → ℝ :=
  D.balance w • finiteWeilGramCoefficientVector s w.1

theorem coefficientBalance_sum : ∑ w, D.coefficientBalance w = 0 := by
  funext k
  change (∑ w, D.coefficientBalance w) k = 0
  simp only [Finset.sum_apply, coefficientBalance, Pi.smul_apply, smul_eq_mul]
  exact D.balance_zero (Pi.single k 1)

theorem coefficientBalance_spans :
    Function.Surjective (fun t : D.tests → ℝ => ∑ w, t w • D.coefficientBalance w) := by
  classical
  intro y
  let L : (s → ℝ) →ₗ[ℝ] ℝ := ∑ k : s, y k • LinearMap.proj k
  have hL (k : s) : L (Pi.single k 1) = y k := by
    simp [L, Pi.single_apply]
  refine ⟨fun w => D.weights L w / D.balance w, ?_⟩
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coefficientBalance]
  calc
    (∑ w, D.weights L w / D.balance w *
        (D.balance w * finiteWeilGramCoefficientVector s w.1 k)) =
        ∑ w, D.weights L w * finiteWeilGramCoefficientVector s w.1 k := by
      apply Finset.sum_congr rfl
      intro w _
      rw [← mul_assoc, div_mul_cancel₀ _ (D.balance_pos w).ne']
    _ = L (Pi.single k 1) := (D.represents L (Pi.single k 1)).symm
    _ = y k := hL k

end FiniteWeilGramCoordinates
end RHTower
