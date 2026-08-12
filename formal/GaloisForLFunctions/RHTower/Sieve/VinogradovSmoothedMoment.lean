import GaloisForLFunctions.RHTower.Sieve.VinogradovFejerFourier
import GaloisForLFunctions.RHTower.Sieve.VinogradovPolynomialMomentExpansion

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovFejerPolynomialPhase
    {N Y b k : ℕ} (α : Fin k → ℝ)
    (l : Fin k → Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius Y b k))) (n : Fin N) : ℝ :=
  finiteVinogradovPolynomialPhase
    (fun j => α j * vinogradovFejerCenteredCoordinate (l j)) n

/-- Exact smoothed polynomial moment identity.  Averaging the `2b`-moment
over the constructive difference majorant converts every power-difference
coordinate into its one-dimensional Fejér kernel. -/
theorem sum_vinogradovFejerWeight_mul_polynomialMoment_eq
    {N Y b k : ℕ} (hN : N ≠ 0) (hY : Y ≠ 0)
    (α : Fin k → ℝ) :
    (∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
        (vinogradovFejerRadius Y b k)),
      vinogradovFejerWeight hY l *
        Complex.normSq (finitePhaseSum
          (vinogradovFejerPolynomialPhase α l : Fin N → ℝ)) ^ b) =
      ∑ uv : (Fin b → Fin N) × (Fin b → Fin N),
        ∏ j : Fin k,
          finiteFejerKernel (vinogradovFejerLength Y b j)
            (α j *
              (((∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1)) -
                ∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1)))) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, Complex.ofReal_pow]
  simp_rw [finitePhaseMoment_expansion]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro uv _
  rw [Complex.ofReal_prod]
  have hphase : ∀ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius Y b k)),
      (∑ i : Fin b, vinogradovFejerPolynomialPhase α l (uv.1 i)) -
          ∑ i : Fin b, vinogradovFejerPolynomialPhase α l (uv.2 i) =
        ∑ j : Fin k, vinogradovFejerCenteredCoordinate (l j) *
          (α j *
            ((∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1)) -
              ∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1))) := by
    intro l
    rw [show vinogradovFejerPolynomialPhase α l =
      finiteVinogradovPolynomialPhase
        (fun j => α j * vinogradovFejerCenteredCoordinate (l j)) from rfl]
    rw [finiteVinogradovPolynomialPhase_tupleDifference hN]
    apply Finset.sum_congr rfl
    intro j _
    rw [vinogradovCenteredDifference_signature hN uv j]
    ring
  simp_rw [hphase]
  exact sum_vinogradovFejerWeight_mul_phase hY
    (fun j => α j *
      ((∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1)) -
        ∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1)))

def vinogradovFejerKernelWeight
    {X Y b k : ℕ} (α : Fin k → ℝ)
    (g : Fin k → Fin (vinogradovDifferenceBoxSize X b k)) : ℝ :=
  ∏ j : Fin k,
    finiteFejerKernel (vinogradovFejerLength Y b j)
      (α j * vinogradovCenteredDifference g j)

theorem vinogradovFejerKernelWeight_nonneg
    {X Y b k : ℕ} (α : Fin k → ℝ)
    (g : Fin k → Fin (vinogradovDifferenceBoxSize X b k)) :
    0 ≤ vinogradovFejerKernelWeight (Y := Y) α g := by
  exact Finset.prod_nonneg fun j _ => finiteFejerKernel_nonneg _ _

theorem vinogradovFejerKernelWeight_signature
    {X Y b k : ℕ} (hX : X ≠ 0) (α : Fin k → ℝ)
    (uv : (Fin b → Fin X) × (Fin b → Fin X)) :
    vinogradovFejerKernelWeight (Y := Y) α
        (vinogradovBoundedDifferenceSignature hX uv) =
      ∏ j : Fin k,
        finiteFejerKernel (vinogradovFejerLength Y b j)
          (α j *
            ((∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1)) -
              ∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1))) := by
  unfold vinogradovFejerKernelWeight
  apply Finset.prod_congr rfl
  intro j _
  rw [vinogradovCenteredDifference_signature hX]

/-- Smoothed Vinogradov moment bound after the second tuple grouping.  This
is MV24.7 up to the purely one-dimensional Diophantine kernel sum. -/
theorem sum_vinogradovFejerWeight_mul_polynomialMoment_le
    {X Y b k : ℕ} (hX : X ≠ 0) (hY : Y ≠ 0)
    (α : Fin k → ℝ) :
    (∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
        (vinogradovFejerRadius Y b k)),
      vinogradovFejerWeight hY l *
        Complex.normSq (finitePhaseSum
          (vinogradovFejerPolynomialPhase α l : Fin X → ℝ)) ^ b) ≤
      Fintype.card (VinogradovDiagonalSolution X b k) *
        ∑ g : Fin k → Fin (vinogradovDifferenceBoxSize X b k),
          vinogradovFejerKernelWeight (Y := Y) α g := by
  rw [sum_vinogradovFejerWeight_mul_polynomialMoment_eq hX hY α]
  calc
    (∑ uv : (Fin b → Fin X) × (Fin b → Fin X),
        ∏ j : Fin k,
          finiteFejerKernel (vinogradovFejerLength Y b j)
            (α j *
              ((∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1)) -
                ∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1)))) =
      ∑ uv : (Fin b → Fin X) × (Fin b → Fin X),
        vinogradovFejerKernelWeight (Y := Y) α
          (vinogradovBoundedDifferenceSignature hX uv) := by
      apply Finset.sum_congr rfl
      intro uv _
      exact (vinogradovFejerKernelWeight_signature hX α uv).symm
    _ ≤ Fintype.card (VinogradovDiagonalSolution X b k) *
        ∑ g : Fin k → Fin (vinogradovDifferenceBoxSize X b k),
          vinogradovFejerKernelWeight (Y := Y) α g :=
      sum_weight_vinogradovBoundedDifference_le hX
        (vinogradovFejerKernelWeight (Y := Y) α)
        (vinogradovFejerKernelWeight_nonneg α)

end

end RHTower.Sieve
