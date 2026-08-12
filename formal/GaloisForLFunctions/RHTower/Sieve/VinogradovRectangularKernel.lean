import GaloisForLFunctions.RHTower.Sieve.VinogradovSmoothedMoment

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovCoordinateDifferenceInRange
    {X b k : ℕ}
    (g : Fin k → Fin (vinogradovDifferenceBoxSize X b k))
    (j : Fin k) : Prop :=
  |vinogradovCenteredDifference g j| ≤
    (vinogradovFejerCoordinateBound X b j : ℝ)

instance vinogradovCoordinateDifferenceInRangeDecidable
    {X b k : ℕ}
    (g : Fin k → Fin (vinogradovDifferenceBoxSize X b k))
    (j : Fin k) : Decidable (vinogradovCoordinateDifferenceInRange g j) :=
  Classical.dec _

def vinogradovRectangularKernelWeight
    {X Y b k : ℕ} (α : Fin k → ℝ)
    (g : Fin k → Fin (vinogradovDifferenceBoxSize X b k)) : ℝ :=
  ∏ j : Fin k,
    if vinogradovCoordinateDifferenceInRange g j then
      finiteFejerKernel (vinogradovFejerLength Y b j)
        (α j * vinogradovCenteredDifference g j)
    else 0

theorem vinogradovCoordinateDifferenceInRange_signature
    {X b k : ℕ} (hX : X ≠ 0)
    (uv : (Fin b → Fin X) × (Fin b → Fin X)) (j : Fin k) :
    vinogradovCoordinateDifferenceInRange
      (vinogradovBoundedDifferenceSignature hX uv) j := by
  unfold vinogradovCoordinateDifferenceInRange
  rw [vinogradovCenteredDifference_signature hX uv j]
  have hu := vinogradovPowerSum_le_coordinate uv.1 j
  have hv := vinogradovPowerSum_le_coordinate uv.2 j
  have hu0 : (0 : ℝ) ≤
      ∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1) := by positivity
  have hv0 : (0 : ℝ) ≤
      ∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1) := by positivity
  have hur : (∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1)) ≤
      vinogradovFejerCoordinateBound X b j := by exact_mod_cast hu
  have hvr : (∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1)) ≤
      vinogradovFejerCoordinateBound X b j := by exact_mod_cast hv
  rw [abs_le]
  constructor <;> nlinarith

theorem vinogradovRectangularKernelWeight_nonneg
    {X Y b k : ℕ} (α : Fin k → ℝ)
    (g : Fin k → Fin (vinogradovDifferenceBoxSize X b k)) :
    0 ≤ vinogradovRectangularKernelWeight (Y := Y) α g := by
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · exact finiteFejerKernel_nonneg _ _
  · exact le_rfl

theorem vinogradovRectangularKernelWeight_signature
    {X Y b k : ℕ} (hX : X ≠ 0) (α : Fin k → ℝ)
    (uv : (Fin b → Fin X) × (Fin b → Fin X)) :
    vinogradovRectangularKernelWeight (Y := Y) α
        (vinogradovBoundedDifferenceSignature hX uv) =
      ∏ j : Fin k,
        finiteFejerKernel (vinogradovFejerLength Y b j)
          (α j *
            ((∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1)) -
              ∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1))) := by
  unfold vinogradovRectangularKernelWeight
  apply Finset.prod_congr rfl
  intro j _
  rw [if_pos (vinogradovCoordinateDifferenceInRange_signature hX uv j)]
  rw [vinogradovCenteredDifference_signature hX uv j]

theorem sum_vinogradovFejerWeight_mul_polynomialMoment_le_rectangular
    {X Y b k : ℕ} (hX : X ≠ 0) (hY : Y ≠ 0)
    (α : Fin k → ℝ) :
    (∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
        (vinogradovFejerRadius Y b k)),
      vinogradovFejerWeight hY l *
        Complex.normSq (finitePhaseSum
          (vinogradovFejerPolynomialPhase α l : Fin X → ℝ)) ^ b) ≤
      Fintype.card (VinogradovDiagonalSolution X b k) *
        ∑ g : Fin k → Fin (vinogradovDifferenceBoxSize X b k),
          vinogradovRectangularKernelWeight (Y := Y) α g := by
  rw [sum_vinogradovFejerWeight_mul_polynomialMoment_eq hX hY α]
  calc
    (∑ uv : (Fin b → Fin X) × (Fin b → Fin X),
        ∏ j : Fin k,
          finiteFejerKernel (vinogradovFejerLength Y b j)
            (α j *
              ((∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1)) -
                ∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1)))) =
      ∑ uv : (Fin b → Fin X) × (Fin b → Fin X),
        vinogradovRectangularKernelWeight (Y := Y) α
          (vinogradovBoundedDifferenceSignature hX uv) := by
      apply Finset.sum_congr rfl
      intro uv _
      exact (vinogradovRectangularKernelWeight_signature hX α uv).symm
    _ ≤ Fintype.card (VinogradovDiagonalSolution X b k) *
        ∑ g : Fin k → Fin (vinogradovDifferenceBoxSize X b k),
          vinogradovRectangularKernelWeight (Y := Y) α g :=
      sum_weight_vinogradovBoundedDifference_le hX
        (vinogradovRectangularKernelWeight (Y := Y) α)
        (vinogradovRectangularKernelWeight_nonneg α)

def vinogradovCoordinateKernelWeight
    {X Y b k : ℕ} (α : Fin k → ℝ) (j : Fin k)
    (g : Fin (vinogradovDifferenceBoxSize X b k)) : ℝ :=
  if |(g.val : ℝ) - b * X ^ k| ≤
      (vinogradovFejerCoordinateBound X b j : ℝ) then
    finiteFejerKernel (vinogradovFejerLength Y b j)
      (α j * ((g.val : ℝ) - b * X ^ k))
  else 0

theorem vinogradovRectangularKernelWeight_eq_prod_coordinate
    {X Y b k : ℕ} (α : Fin k → ℝ)
    (g : Fin k → Fin (vinogradovDifferenceBoxSize X b k)) :
    vinogradovRectangularKernelWeight (Y := Y) α g =
      ∏ j : Fin k, vinogradovCoordinateKernelWeight (Y := Y) α j (g j) := by
  rfl

theorem sum_vinogradovRectangularKernelWeight_eq_prod
    {X Y b k : ℕ} (α : Fin k → ℝ) :
    (∑ g : Fin k → Fin (vinogradovDifferenceBoxSize X b k),
      vinogradovRectangularKernelWeight (Y := Y) α g) =
      ∏ j : Fin k,
        ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
          vinogradovCoordinateKernelWeight (Y := Y) α j g := by
  simp_rw [vinogradovRectangularKernelWeight_eq_prod_coordinate]
  exact (Fintype.prod_sum
    (fun j : Fin k => vinogradovCoordinateKernelWeight (Y := Y) α j)).symm

/-- Product form of the smoothed moment estimate.  Every remaining factor is
one-dimensional and has the sharp coordinate range `b X^(j+1)`. -/
theorem sum_vinogradovFejerWeight_mul_polynomialMoment_le_coordinateProduct
    {X Y b k : ℕ} (hX : X ≠ 0) (hY : Y ≠ 0)
    (α : Fin k → ℝ) :
    (∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
        (vinogradovFejerRadius Y b k)),
      vinogradovFejerWeight hY l *
        Complex.normSq (finitePhaseSum
          (vinogradovFejerPolynomialPhase α l : Fin X → ℝ)) ^ b) ≤
      Fintype.card (VinogradovDiagonalSolution X b k) *
        ∏ j : Fin k,
          ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
            vinogradovCoordinateKernelWeight (Y := Y) α j g := by
  rw [← sum_vinogradovRectangularKernelWeight_eq_prod]
  exact sum_vinogradovFejerWeight_mul_polynomialMoment_le_rectangular
    hX hY α

end

end RHTower.Sieve
