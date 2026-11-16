import GaloisForLFunctions.RHTower.Sieve.BilinearFourCornerEnergy
import GaloisForLFunctions.RHTower.Sieve.TypeIIEnergyBound

/-!
# Four-corner energy of the actual near-diagonal phase

After removing both coefficient sequences, the Type-II phase leaves the
increment of its existing difference phase at two long-variable points.
The resulting signed exponential sum is exactly a nonnegative Gram energy.
This identifies the arithmetic object left by the coefficient-removal step;
it does not assume cancellation of that object.
-/

noncomputable section
open GaloisForLFunctions.HTGeometry
namespace RHTower.Sieve

/-- Four actual Type-II phases combine into one increment of the difference phase. -/
theorem ndExp_four_corner (T r : ℝ) (d k m l : ℕ) :
    ndExp T r m d * star (ndExp T r m k) * star (ndExp T r l d) * ndExp T r l k =
      phaseExp (diffPhase T (r / m) (r / l) d - diffPhase T (r / m) (r / l) k) := by
  have hpair (n : ℕ) :
      ndExp T r m n * (starRingEnd ℂ) (ndExp T r l n) =
        phaseExp (diffPhase T (r / m) (r / l) n) := by
    simp only [ndExp]
    rw [phaseExp_mul_conj, nearDiagonalPhase_mul T r (m : ℝ) (n : ℝ),
      nearDiagonalPhase_mul T r (l : ℝ) (n : ℝ), diffPhase]
  calc
    _ = (ndExp T r m d * (starRingEnd ℂ) (ndExp T r l d)) *
        (starRingEnd ℂ) (ndExp T r m k * (starRingEnd ℂ) (ndExp T r l k)) := by
      simp only [map_mul, starRingEnd_apply, star_star]
      ring
    _ = _ := by rw [hpair, hpair, phaseExp_mul_conj]

/-- The coefficient-free exponential sum on a rectangle of arithmetic indices. -/
def ndFourCornerSum (T r : ℝ) (D M : Finset ℕ) : ℂ :=
  ∑ d ∈ D, ∑ k ∈ D, ∑ m ∈ M, ∑ l ∈ M,
    phaseExp (diffPhase T (r / m) (r / l) d - diffPhase T (r / m) (r / l) k)

/-- The signed fourfold exponential sum is exactly the row-correlation energy. -/
theorem ndFourCornerSum_eq_energy (T r : ℝ) (D M : Finset ℕ) :
    ndFourCornerSum T r D M =
      ((∑ d ∈ D, ∑ k ∈ D, ‖∑ m ∈ M, ndExp T r m d * star (ndExp T r m k)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have h := fourCornerEnergy_eq_four_sum (fun (d : D) (m : M) => ndExp T r m d)
  rw [fourCornerEnergy_eq_rows] at h
  simpa only [ndFourCornerSum, ← Finset.sum_coe_sort D, ← Finset.sum_coe_sort M,
    ndExp_four_corner] using h.symm

@[simp] theorem ndFourCornerSum_im (T r : ℝ) (D M : Finset ℕ) :
    (ndFourCornerSum T r D M).im = 0 := by
  rw [ndFourCornerSum_eq_energy]
  rfl

theorem ndFourCornerSum_re_nonneg (T r : ℝ) (D M : Finset ℕ) :
    0 ≤ (ndFourCornerSum T r D M).re := by
  rw [ndFourCornerSum_eq_energy]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem ndExp_mul_star_self (T r : ℝ) (m d : ℕ) :
    ndExp T r m d * star (ndExp T r m d) = 1 := by
  rw [RCLike.star_def, ndExp, phaseExp_mul_conj, sub_self]
  simp [phaseExp]

private theorem ndExp_star_mul_self (T r : ℝ) (m d : ℕ) :
    star (ndExp T r m d) * ndExp T r m d = 1 := by
  rw [mul_comm, ndExp_mul_star_self]

/-- The row diagonal is an exact main term; all remaining row-correlation energies are nonnegative. -/
theorem ndFourCornerSum_re_eq_diagonal_add (T r : ℝ) (D M : Finset ℕ) :
    (ndFourCornerSum T r D M).re = (D.card : ℝ) * (M.card : ℝ) ^ 2 +
      ∑ d ∈ D, ∑ k ∈ D.erase d, ‖∑ m ∈ M, ndExp T r m d * star (ndExp T r m k)‖ ^ 2 := by
  have hdiag (d : ℕ) :
      ‖∑ m ∈ M, ndExp T r m d * star (ndExp T r m d)‖ ^ 2 = (M.card : ℝ) ^ 2 := by
    simp only [ndExp_mul_star_self]
    simp
  calc
    (ndFourCornerSum T r D M).re =
        ∑ d ∈ D, ∑ k ∈ D, ‖∑ m ∈ M, ndExp T r m d * star (ndExp T r m k)‖ ^ 2 := by
      rw [ndFourCornerSum_eq_energy]
      rfl
    _ = ∑ d ∈ D, ((M.card : ℝ) ^ 2 +
        ∑ k ∈ D.erase d, ‖∑ m ∈ M, ndExp T r m d * star (ndExp T r m k)‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro d hd
      have h := Finset.sum_erase_add D
        (fun k => ‖∑ m ∈ M, ndExp T r m d * star (ndExp T r m k)‖ ^ 2) hd
      rw [hdiag] at h
      linarith only [h]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- Neither row nor column diagonals can be removed by cancellation of the signed fourfold sum. -/
theorem ndFourCornerSum_re_ge_diagonals (T r : ℝ) (D M : Finset ℕ) :
    max ((D.card : ℝ) * (M.card : ℝ) ^ 2) ((M.card : ℝ) * (D.card : ℝ) ^ 2) ≤
      (ndFourCornerSum T r D M).re := by
  have hrow : (D.card : ℝ) * (M.card : ℝ) ^ 2 ≤ (ndFourCornerSum T r D M).re := by
    rw [ndFourCornerSum_re_eq_diagonal_add]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hcol : (M.card : ℝ) * (D.card : ℝ) ^ 2 ≤ (ndFourCornerSum T r D M).re := by
    rw [ndFourCornerSum_eq_energy, Complex.ofReal_re,
      rowCorrelationEnergy_eq_columnCorrelationEnergy D M (fun d m => ndExp T r m d)]
    calc
      (M.card : ℝ) * (D.card : ℝ) ^ 2 =
          ∑ m ∈ M, ‖∑ d ∈ D, star (ndExp T r m d) * ndExp T r m d‖ ^ 2 := by
        simp only [ndExp_star_mul_self]
        simp
      _ ≤ ∑ m ∈ M, ∑ l ∈ M, ‖∑ d ∈ D, star (ndExp T r m d) * ndExp T r l d‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        exact Finset.single_le_sum
          (f := fun l => ‖∑ d ∈ D, star (ndExp T r m d) * ndExp T r l d‖ ^ 2)
          (fun _ _ => sq_nonneg _) hm
  exact max_le hrow hcol

/-- Both Type-II coefficient sequences are removed with their exact ℓ² costs. -/
theorem norm_ndExp_bilinear_fourth_le (T r : ℝ) (D M : Finset ℕ) (a b : ℕ → ℂ) :
    ‖∑ d ∈ D, a d * ∑ m ∈ M, ndExp T r m d * b m‖ ^ 4 ≤
      (∑ d ∈ D, ‖a d‖ ^ 2) ^ 2 * (∑ m ∈ M, ‖b m‖ ^ 2) ^ 2 *
        (ndFourCornerSum T r D M).re := by
  rw [ndFourCornerSum_eq_energy]
  exact norm_bilinear_fourth_le_rowCorrelationEnergy D M a b (fun d m => ndExp T r m d)

#print axioms ndExp_four_corner
#print axioms ndFourCornerSum_eq_energy
#print axioms ndFourCornerSum_re_nonneg
#print axioms ndFourCornerSum_re_eq_diagonal_add
#print axioms ndFourCornerSum_re_ge_diagonals
#print axioms norm_ndExp_bilinear_fourth_le

end RHTower.Sieve
