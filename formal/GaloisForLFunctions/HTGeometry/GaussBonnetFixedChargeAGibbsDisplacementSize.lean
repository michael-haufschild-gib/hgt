import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsDisplacement

/-!
# A vanishing common bound for every Gibbs displacement

A finite sum of coordinate displacements controls all coordinates together.
Its limit supplies the eventual Taylor interval for arbitrary Gibbs inputs.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

/-- A common absolute displacement bound for the whole Gibbs population. -/
def egbFixedChargeAGibbsDisplacementSize (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  ∑ i, |egbFixedChargeAGibbsDisplacement n m β E i|

/-- The common displacement bound is nonnegative. -/
theorem egbFixedChargeAGibbsDisplacementSize_nonneg (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : 0 ≤ egbFixedChargeAGibbsDisplacementSize n m β E :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Every displacement coordinate is bounded by the same scalar quantity. -/
theorem egbFixedChargeAGibbsDisplacementSize_coordinate (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    |egbFixedChargeAGibbsDisplacement n m β E i| ≤ egbFixedChargeAGibbsDisplacementSize n m β E := by
  unfold egbFixedChargeAGibbsDisplacementSize
  exact Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
      abs_nonneg (egbFixedChargeAGibbsDisplacement n m β E j))
    (Finset.mem_univ i)

/-- The common coordinate bound tends to zero for every Gibbs input. -/
theorem egbFixedChargeAGibbsDisplacementSize_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m => egbFixedChargeAGibbsDisplacementSize n m β E) atTop (nhds 0) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin (2 ^ (n + 3))))
    (fun i _ => (egbFixedChargeAGibbsDisplacement_limit n β E i).abs)
  simpa only [egbFixedChargeAGibbsDisplacementSize, abs_zero, Finset.sum_const_zero] using h

/-- Every Gibbs input eventually enters one common logarithm Taylor interval. -/
theorem egbFixedChargeAGibbsDisplacementSize_eventually_half (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    ∀ᶠ m : ℕ in atTop, egbFixedChargeAGibbsDisplacementSize n m β E ≤ 1 / 2 :=
  (egbFixedChargeAGibbsDisplacementSize_limit n β E).eventually_le_const (by norm_num)

/-- The common bound controls the total cubic error by the squared displacement mass. -/
theorem egbFixedChargeAGibbsDisplacementSize_cubic_bound (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ i, |egbFixedChargeAGibbsDisplacement n m β E i| ^ (3 : ℕ)) ≤
      egbFixedChargeAGibbsDisplacementSize n m β E *
        ∑ i, egbFixedChargeAGibbsDisplacement n m β E i ^ (2 : ℕ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_right (egbFixedChargeAGibbsDisplacementSize_coordinate n m β E i)
    (sq_nonneg (egbFixedChargeAGibbsDisplacement n m β E i))
  have he : |egbFixedChargeAGibbsDisplacement n m β E i| ^ (3 : ℕ) =
      |egbFixedChargeAGibbsDisplacement n m β E i| * egbFixedChargeAGibbsDisplacement n m β E i ^ (2 : ℕ) := by
    rw [pow_succ _ 2, sq_abs]
    ring
  rw [he]
  exact h

end
end GaloisForLFunctions.HTGeometry
