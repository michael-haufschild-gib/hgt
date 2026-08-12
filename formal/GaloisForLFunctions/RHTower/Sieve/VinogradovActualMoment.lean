import GaloisForLFunctions.RHTower.Sieve.VinogradovCoordinateKernelBound

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovActualDifference
    {Y b k : ℕ}
    (uv : (Fin b → Fin Y) × (Fin b → Fin Y)) (j : Fin k) : ℝ :=
  (∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1)) -
    ∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1)

def vinogradovActualPolynomialPhase
    {X Y b k : ℕ} (α : Fin k → ℝ)
    (uv : (Fin b → Fin Y) × (Fin b → Fin Y)) : Fin X → ℝ :=
  finiteVinogradovPolynomialPhase
    (fun j => α j * vinogradovActualDifference uv j)

theorem vinogradovFejerPolynomialPhase_signature
    {X Y b k : ℕ} (hY : Y ≠ 0) (α : Fin k → ℝ)
    (uv : (Fin b → Fin Y) × (Fin b → Fin Y)) :
    (vinogradovFejerPolynomialPhase α
      (vinogradovWideDifferenceSignature hY
        (vinogradovRawDifference_le_fejerRadius Y b k) uv) : Fin X → ℝ) =
      vinogradovActualPolynomialPhase α uv := by
  funext n
  unfold vinogradovFejerPolynomialPhase vinogradovActualPolynomialPhase
  unfold finiteVinogradovPolynomialPhase
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  have hcenter :
      vinogradovFejerCenteredCoordinate
        (vinogradovWideDifferenceSignature hY
          (vinogradovRawDifference_le_fejerRadius Y b k) uv j) =
        vinogradovActualDifference uv j := by
    change vinogradovWideCenteredDifference
      (vinogradovWideDifferenceSignature hY
        (vinogradovRawDifference_le_fejerRadius Y b k) uv) j = _
    exact vinogradovWideCenteredDifference_signature hY _ uv j
  rw [hcenter]

/-- Every actual `Y`-tuple difference is pointwise dominated by the
constructive Fejér majorant, and exact wide-box grouping costs only its
Vinogradov fibre cardinality.  This closes the first use of `J_k(Y,b)` in
the MV24.7 bridge. -/
theorem sum_vinogradovActualPolynomialMoment_le_smoothed
    {X Y b k : ℕ} (hY : Y ≠ 0) (α : Fin k → ℝ) :
    (∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
      Complex.normSq (finitePhaseSum
        (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)) ^ b) ≤
      Fintype.card (VinogradovDiagonalSolution Y b k) *
        ∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
            (vinogradovFejerRadius Y b k)),
          vinogradovFejerWeight hY l *
            Complex.normSq (finitePhaseSum
              (vinogradovFejerPolynomialPhase α l : Fin X → ℝ)) ^ b := by
  let R : ℕ := vinogradovFejerRadius Y b k
  let hR : b * Y ^ k ≤ R := vinogradovRawDifference_le_fejerRadius Y b k
  let sig : ((Fin b → Fin Y) × (Fin b → Fin Y)) →
      (Fin k → Fin (vinogradovWideDifferenceBoxSize R)) :=
    vinogradovWideDifferenceSignature hY hR
  let moment : (Fin k → Fin (vinogradovWideDifferenceBoxSize R)) → ℝ :=
    fun l => Complex.normSq (finitePhaseSum
      (vinogradovFejerPolynomialPhase α l : Fin X → ℝ)) ^ b
  let weighted : (Fin k → Fin (vinogradovWideDifferenceBoxSize R)) → ℝ :=
    fun l => vinogradovFejerWeight hY l * moment l
  have hmoment : ∀ l, 0 ≤ moment l := by
    intro l
    exact pow_nonneg (Complex.normSq_nonneg _) _
  have hweighted : ∀ l, 0 ≤ weighted l := by
    intro l
    exact mul_nonneg (vinogradovFejerWeight_nonneg hY l) (hmoment l)
  have hpoint : ∀ uv, Complex.normSq (finitePhaseSum
        (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)) ^ b ≤
      weighted (sig uv) := by
    intro uv
    have hphase := vinogradovFejerPolynomialPhase_signature
      (X := X) hY α uv
    have hone := one_le_vinogradovFejerWeight_signature (k := k) hY uv
    unfold weighted moment sig R hR
    rw [hphase]
    exact le_mul_of_one_le_left (pow_nonneg (Complex.normSq_nonneg _) _) hone
  calc
    (∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
        Complex.normSq (finitePhaseSum
          (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)) ^ b) ≤
        ∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y), weighted (sig uv) :=
      Finset.sum_le_sum fun uv _ => hpoint uv
    _ ≤ Fintype.card (VinogradovDiagonalSolution Y b k) *
        ∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize R), weighted l :=
      sum_weight_vinogradovWideDifference_le hY hR weighted hweighted
    _ = Fintype.card (VinogradovDiagonalSolution Y b k) *
        ∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
            (vinogradovFejerRadius Y b k)),
          vinogradovFejerWeight hY l *
            Complex.normSq (finitePhaseSum
              (vinogradovFejerPolynomialPhase α l : Fin X → ℝ)) ^ b := by
      rfl

/-- Actual tuple-difference moment after both exact Vinogradov groupings.
All remaining analytic content is the product of one-dimensional kernels. -/
theorem sum_vinogradovActualPolynomialMoment_le_coordinateProduct
    {X Y b k : ℕ} (hX : X ≠ 0) (hY : Y ≠ 0)
    (α : Fin k → ℝ) :
    (∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
      Complex.normSq (finitePhaseSum
        (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)) ^ b) ≤
      (Fintype.card (VinogradovDiagonalSolution Y b k) *
        Fintype.card (VinogradovDiagonalSolution X b k)) *
          ∏ j : Fin k,
            ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
              vinogradovCoordinateKernelWeight (Y := Y) α j g := by
  calc
    _ ≤ Fintype.card (VinogradovDiagonalSolution Y b k) *
        ∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
            (vinogradovFejerRadius Y b k)),
          vinogradovFejerWeight hY l *
            Complex.normSq (finitePhaseSum
              (vinogradovFejerPolynomialPhase α l : Fin X → ℝ)) ^ b :=
      sum_vinogradovActualPolynomialMoment_le_smoothed hY α
    _ ≤ Fintype.card (VinogradovDiagonalSolution Y b k) *
        (Fintype.card (VinogradovDiagonalSolution X b k) *
          ∏ j : Fin k,
            ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
              vinogradovCoordinateKernelWeight (Y := Y) α j g) := by
      apply mul_le_mul_of_nonneg_left
        (sum_vinogradovFejerWeight_mul_polynomialMoment_le_coordinateProduct
          hX hY α)
      positivity
    _ = (Fintype.card (VinogradovDiagonalSolution Y b k) *
        Fintype.card (VinogradovDiagonalSolution X b k)) *
          ∏ j : Fin k,
            ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
              vinogradovCoordinateKernelWeight (Y := Y) α j g := by ring

theorem sum_vinogradovActualPolynomialMoment_le_rationalProduct
    {X Y b k : ℕ} (hX : X ≠ 0) (hY : Y ≠ 0)
    (α : Fin k → ℝ) (a q : Fin k → ℕ)
    (hq : ∀ j, 0 < q j) (hcop : ∀ j, Nat.Coprime (a j) (q j))
    (happrox : ∀ j,
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ 2) :
    (∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
      Complex.normSq (finitePhaseSum
        (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)) ^ b) ≤
      ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
        Fintype.card (VinogradovDiagonalSolution X b k)) *
          ∏ j : Fin k,
            vinogradovRationalCoordinateCost X Y b (q j) j := by
  calc
    _ ≤ ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
        Fintype.card (VinogradovDiagonalSolution X b k)) *
          ∏ j : Fin k,
            ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
              vinogradovCoordinateKernelWeight (Y := Y) α j g :=
      sum_vinogradovActualPolynomialMoment_le_coordinateProduct hX hY α
    _ ≤ ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
        Fintype.card (VinogradovDiagonalSolution X b k)) *
          ∏ j : Fin k,
            vinogradovRationalCoordinateCost X Y b (q j) j := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.prod_le_prod
        · intro j _
          exact Finset.sum_nonneg fun g _ =>
            vinogradovCoordinateKernelWeight_nonneg α j g
        · intro j _
          exact sum_vinogradovCoordinateKernelWeight_le_rationalApprox
            hX (hq j) α j (hcop j) (happrox j)
      · positivity

end

end RHTower.Sieve
