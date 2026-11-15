import GaloisForLFunctions.BiarithmeticGeometry.Affine.MixedMatrixOverlap
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovShearMinors
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Cube overlap bounds for homogeneous binomial shear blocks

Retain the final `q+r` original coordinates and select the last `q`
transformed coordinates. The selected matrix is block triangular with the
binomial shear minor on its diagonal. Its exact determinant therefore gives
the decay power `q(q+r)` in the full `2q+r` dimensional space.
-/

open MeasureTheory Matrix
open scoped ENNReal
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Split the initial `q` coordinates from the remaining `q+r` coordinates. -/
def shearSplit (q r : ℕ) : Fin q ⊕ Fin (q + r) ≃ Fin (2 * q + r) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- Select high transformed coordinates and retain the complementary original ones. -/
def shearSelector (q r : ℕ) (i : Fin (2 * q + r)) :
    Fin (2 * q + r) ⊕ Fin (2 * q + r) :=
  Sum.elim (fun j => Sum.inr (shearMinorRows q r j))
    (fun _ => Sum.inl i) ((shearSplit q r).symm i)

private theorem shear_selected_blocks (q r : ℕ) (θ : ℝ) :
    (selectedMatrix (shearBlock (2 * q + r) θ) (shearSelector q r)).submatrix
      (shearSplit q r) (shearSplit q r) =
    Matrix.fromBlocks (shearMinor q r θ)
      ((shearBlock (2 * q + r) θ).submatrix (shearMinorRows q r)
        (fun j => shearSplit q r (Sum.inr j))) 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change Sum.elim _ _ (shearSelector q r (shearSplit q r (Sum.inl i))) = _
    simp only [shearSelector, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    rfl
  · change Sum.elim _ _ (shearSelector q r (shearSplit q r (Sum.inl i))) = _
    simp only [shearSelector, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    rfl
  · change Sum.elim _ _ (shearSelector q r (shearSplit q r (Sum.inr i))) = 0
    simp only [shearSelector, Equiv.symm_apply_apply, Sum.elim_inr, Sum.elim_inl,
      Matrix.one_apply, Equiv.apply_eq_iff_eq, reduceCtorEq, ite_false]
  · change Sum.elim _ _ (shearSelector q r (shearSplit q r (Sum.inr i))) =
      (1 : Matrix (Fin (q + r)) (Fin (q + r)) ℝ) i j
    simp only [shearSelector, Equiv.symm_apply_apply, Sum.elim_inr, Sum.elim_inl,
      Matrix.one_apply, Equiv.apply_eq_iff_eq, Sum.inr.injEq]

/-- The selected ambient matrix has exactly the determinant of the shear minor. -/
theorem det_shear_selectedMatrix (q r : ℕ) (θ : ℝ) :
    (selectedMatrix (shearBlock (2 * q + r) θ) (shearSelector q r)).det =
      shearMinorConstant q r * θ ^ (q * (q + r)) := by
  rw [← Matrix.det_submatrix_equiv_self (shearSplit q r), shear_selected_blocks,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, det_shearMinor]

/-- Exact polynomial determinant weights bound the overlap, uniformly in both centers. -/
theorem shear_power_mul_volume_overlap_le (q r : ℕ) (θ ρ : ℝ)
    (a b : Fin (2 * q + r) → ℝ) :
    ENNReal.ofReal (|shearMinorConstant q r| * |θ| ^ (q * (q + r))) *
      volume (centeredCube a ρ ∩
        (Matrix.toLin' (shearBlock (2 * q + r) θ)) ⁻¹' centeredCube b ρ) ≤
      ENNReal.ofReal (2 * ρ) ^ (2 * q + r) := by
  simpa only [det_shear_selectedMatrix, abs_mul, abs_pow, Fintype.card_fin] using
    selectedMatrix_det_mul_volume_overlap_le (shearBlock (2 * q + r) θ)
      (shearSelector q r) a b ρ

/-- The unit-cube overlap for the full homogeneous shear, with independent centers. -/
def shearCubeOverlap (q r : ℕ) (θ : ℝ) (a b : Fin (2 * q + r) → ℝ) :
    Set (Fin (2 * q + r) → ℝ) :=
  centeredCube a 1 ∩
    (Matrix.toLin' (shearBlock (2 * q + r) θ)) ⁻¹' centeredCube b 1

/-- The ambient cube gives a uniform finite bound, including at zero shear. -/
theorem volume_shearCubeOverlap_le (q r : ℕ) (θ : ℝ)
    (a b : Fin (2 * q + r) → ℝ) :
    volume (shearCubeOverlap q r θ a b) ≤ (2 : ℝ≥0∞) ^ (2 * q + r) := by
  calc
    _ ≤ volume (centeredCube a 1) := measure_mono Set.inter_subset_left
    _ = _ := by rw [volume_centeredCube]; norm_num

private theorem regularize_power_bound (x c v : ℝ) (m d : ℕ)
    (hx : 0 ≤ x) (hv : 0 ≤ v) (h0 : v ≤ 2 ^ m) (h1 : c * x ^ d * v ≤ 2 ^ m) :
    min 1 c * (1 + x) ^ d * v ≤ 2 ^ (m + d) := by
  by_cases hc : c ≤ 0
  · have hn : min 1 c * (1 + x) ^ d * v ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg ((min_le_right 1 c).trans hc) (by positivity)) hv
    exact hn.trans (by positivity)
  have hcpos : 0 < c := lt_of_not_ge hc
  by_cases hsmall : x ≤ 1
  · have hp : (1 + x) ^ d ≤ (2 : ℝ) ^ d := by gcongr; linarith only [hsmall]
    calc
      _ ≤ 1 * (2 : ℝ) ^ d * v := by gcongr; exact min_le_left 1 c
      _ ≤ 2 ^ d * 2 ^ m := by simpa only [one_mul] using mul_le_mul_of_nonneg_left h0 (by positivity)
      _ = _ := by rw [pow_add]; ring
  · have hp : (1 + x) ^ d ≤ (2 * x) ^ d := by gcongr; linarith only [hsmall]
    calc
      _ ≤ c * (2 * x) ^ d * v := by gcongr; exact min_le_right 1 c
      _ = 2 ^ d * (c * x ^ d * v) := by rw [mul_pow]; ring
      _ ≤ 2 ^ d * 2 ^ m := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by rw [pow_add]; ring

/-- A regularized polynomial weight remains bounded uniformly in the cube centers. -/
theorem regularized_shear_mul_real_volume_le (q r : ℕ) (θ : ℝ)
    (a b : Fin (2 * q + r) → ℝ) :
    min 1 |shearMinorConstant q r| * (1 + |θ|) ^ (q * (q + r)) *
      (volume (shearCubeOverlap q r θ a b)).toReal ≤
        (2 : ℝ) ^ (2 * q + r + q * (q + r)) := by
  have h0 : (volume (shearCubeOverlap q r θ a b)).toReal ≤ (2 : ℝ) ^ (2 * q + r) := by
    have h := ENNReal.toReal_mono (by finiteness) (volume_shearCubeOverlap_le q r θ a b)
    simpa using h
  have h1 := ENNReal.toReal_mono (by finiteness) (shear_power_mul_volume_overlap_le q r θ 1 a b)
  have h1' : |shearMinorConstant q r| * |θ| ^ (q * (q + r)) *
      (volume (shearCubeOverlap q r θ a b)).toReal ≤ (2 : ℝ) ^ (2 * q + r) := by
    simpa only [shearCubeOverlap, mul_one, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)),
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 by norm_num)] using h1
  exact regularize_power_bound |θ| |shearMinorConstant q r| _ _ _
    (abs_nonneg θ) ENNReal.toReal_nonneg h0 h1'

/-- Every homogeneous shear block has the minor's regularized overlap decay. -/
theorem volume_shearCubeOverlap_le_decay (q r : ℕ) (θ : ℝ)
    (a b : Fin (2 * q + r) → ℝ) :
    volume (shearCubeOverlap q r θ a b) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * q + r + q * (q + r)) /
        (min 1 |shearMinorConstant q r| * (1 + |θ|) ^ (q * (q + r)))) := by
  have hc : 0 < min 1 |shearMinorConstant q r| :=
    lt_min (by norm_num) (abs_pos.mpr (shearMinorConstant_ne_zero q r))
  have hd : 0 < min 1 |shearMinorConstant q r| * (1 + |θ|) ^ (q * (q + r)) := by
    positivity
  have hreal : (volume (shearCubeOverlap q r θ a b)).toReal ≤
      (2 : ℝ) ^ (2 * q + r + q * (q + r)) /
        (min 1 |shearMinorConstant q r| * (1 + |θ|) ^ (q * (q + r))) := by
    apply (le_div_iff₀ hd).mpr
    rw [mul_comm]
    exact regularized_shear_mul_real_volume_le q r θ a b
  have hfinite : volume (shearCubeOverlap q r θ a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (volume_shearCubeOverlap_le q r θ a b)
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The quarter-square exponent holds for every block size, uniformly over translations. -/
theorem exists_uniform_shear_overlap_decay (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ) (a b : Fin m → ℝ),
      volume (centeredCube a 1 ∩
        (Matrix.toLin' (shearBlock m θ)) ⁻¹' centeredCube b 1) ≤
          ENNReal.ofReal (C / (1 + |θ|) ^ (m ^ 2 / 4)) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r ≤ 1 ∧ m = 2 * q + r := by
    refine ⟨m / 2, m % 2, ?_, ?_⟩ <;> omega
  have he : (2 * q + r) ^ 2 / 4 = q * (q + r) := by
    have hr' : r = 0 ∨ r = 1 := by omega
    rcases hr' with rfl | rfl
    · have h : (2 * q + 0) ^ 2 = 4 * (q * (q + 0)) := by ring
      rw [h]; omega
    · have h : (2 * q + 1) ^ 2 = 4 * (q * (q + 1)) + 1 := by ring
      rw [h]; omega
  have hc : 0 < min 1 |shearMinorConstant q r| :=
    lt_min (by norm_num) (abs_pos.mpr (shearMinorConstant_ne_zero q r))
  refine ⟨2 ^ (2 * q + r + q * (q + r)) / min 1 |shearMinorConstant q r|,
    by positivity, ?_⟩
  intro θ a b
  rw [he, div_div]
  exact volume_shearCubeOverlap_le_decay q r θ a b

#print axioms det_shear_selectedMatrix
#print axioms shear_power_mul_volume_overlap_le
#print axioms volume_shearCubeOverlap_le
#print axioms regularized_shear_mul_real_volume_le
#print axioms volume_shearCubeOverlap_le_decay
#print axioms exists_uniform_shear_overlap_decay

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
