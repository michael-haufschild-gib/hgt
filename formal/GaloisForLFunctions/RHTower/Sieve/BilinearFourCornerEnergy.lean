import GaloisForLFunctions.HTGeometry.Analysis.FourCornerCoefficientRemoval
import GaloisForLFunctions.RHTower.Sieve.BilinearCauchySchwarz

/-!
# Coefficient removal in the finite Type-II bilinear form

The Gram-energy form of the second Cauchy--Schwarz step removes the inner
coefficient sequence from the existing bilinear sum. The residual quantity
can be read as row correlations or column correlations, and retains the
signed four-corner products inside each squared correlation.
-/

noncomputable section
open GaloisForLFunctions.HTGeometry
namespace RHTower.Sieve

/-- Exact equality of the row and column correlation energies on finite arithmetic windows. -/
theorem rowCorrelationEnergy_eq_columnCorrelationEnergy
    (D M : Finset ℕ) (z : ℕ → ℕ → ℂ) :
    (∑ d ∈ D, ∑ k ∈ D, ‖∑ m ∈ M, z d m * star (z k m)‖ ^ 2) =
      ∑ m ∈ M, ∑ l ∈ M, ‖∑ d ∈ D, star (z d m) * z d l‖ ^ 2 := by
  classical
  have h := (fourCornerEnergy_eq_rows (fun (d : D) (m : M) => z d m)).symm.trans
    (fourCornerEnergy_eq_columns (fun (d : D) (m : M) => z d m))
  simpa only [← Finset.sum_coe_sort D, ← Finset.sum_coe_sort M] using h

/-- Removing the inner coefficients leaves an unweighted row-correlation energy. -/
theorem sum_normSq_inner_sq_le_fourCornerEnergy
    (D M : Finset ℕ) (b : ℕ → ℂ) (z : ℕ → ℕ → ℂ) :
    (∑ d ∈ D, ‖∑ m ∈ M, z d m * b m‖ ^ 2) ^ 2 ≤
      (∑ d ∈ D, ∑ k ∈ D, ‖∑ m ∈ M, z d m * star (z k m)‖ ^ 2) *
        (∑ m ∈ M, ‖b m‖ ^ 2) ^ 2 := by
  classical
  have h := weightedColumnEnergy_sq_le_fourCornerEnergy
    (fun (d : D) (m : M) => z d m) (fun m : M => b m)
  simpa only [fourCornerEnergy_eq_rows, ← Finset.sum_coe_sort D,
    ← Finset.sum_coe_sort M] using h

/-- Both coefficient sequences contribute only their ℓ² masses to the fourth-power bound. -/
theorem norm_bilinear_fourth_le_rowCorrelationEnergy
    (D M : Finset ℕ) (a b : ℕ → ℂ) (z : ℕ → ℕ → ℂ) :
    ‖∑ d ∈ D, a d * ∑ m ∈ M, z d m * b m‖ ^ 4 ≤
      (∑ d ∈ D, ‖a d‖ ^ 2) ^ 2 * (∑ m ∈ M, ‖b m‖ ^ 2) ^ 2 *
        ∑ d ∈ D, ∑ k ∈ D, ‖∑ m ∈ M, z d m * star (z k m)‖ ^ 2 := by
  classical
  have h := norm_bilinear_fourth_le_fourCornerEnergy
    (fun (d : D) (m : M) => z d m) (fun d : D => a d) (fun m : M => b m)
  simpa only [fourCornerEnergy_eq_rows, ← Finset.sum_coe_sort D,
    ← Finset.sum_coe_sort M] using h

#print axioms rowCorrelationEnergy_eq_columnCorrelationEnergy
#print axioms sum_normSq_inner_sq_le_fourCornerEnergy
#print axioms norm_bilinear_fourth_le_rowCorrelationEnergy

end RHTower.Sieve
