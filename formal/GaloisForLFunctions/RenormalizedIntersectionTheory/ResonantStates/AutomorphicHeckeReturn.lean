import GaloisForLFunctions.RHTower.EisensteinHeckeMaassSelberg
import GaloisForLFunctions.HTGeometry.HolomorphicPoincareSeries

/-!
# The compact-core correction to the dyadic Hecke operator

Automorphic truncation removes the constant term at every modular cusp lift.
At height one, the two downward dyadic branches encounter precisely the
three disks `(x+k)²+(y-1)²<1`, for `k=-1,0,1`.
-/

open Complex Set UpperHalfPlane ModularGroup EisensteinSeries
open GaloisForLFunctions.HTGeometry RHTower
open scoped MatrixGroups

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- The downward branch `(z+b)/2`. -/
def dyadicLower (b : ℤ) (z : ℍ) : ℍ :=
  ⟨((z : ℂ) + b) / 2, by simpa using half_pos z.im_pos⟩

private theorem dyadicLower_re (b : ℤ) (z : ℍ) :
    (dyadicLower b z).re = (z.re + b) / 2 := by
  simp [dyadicLower]

private theorem dyadicLower_im (b : ℤ) (z : ℍ) :
    (dyadicLower b z).im = z.im / 2 := by
  simp [dyadicLower]

private theorem fd_height_half {z : ℍ} (hz : z ∈ fd) : 1 / 2 < z.im := by
  have hx := abs_le.mp hz.2
  have hn := hz.1
  rw [Complex.normSq_apply] at hn
  change 1 ≤ z.re * z.re + z.im * z.im at hn
  have hy := z.im_pos
  nlinarith [sq_nonneg (z.re + 1 / 2), sq_nonneg (z.re - 1 / 2)]

private theorem lower_row_height (v : gammaSet 1 1 0) (b : ℤ) (z : ℍ) :
    rowHeight v (dyadicLower b z) =
      2 * z.im / (((v.1 0 : ℝ) * z.im) ^ 2 +
        ((v.1 0 : ℝ) * z.re + ((v.1 0 * b + 2 * v.1 1 : ℤ) : ℝ)) ^ 2) := by
  rw [rowHeight_eq_div, normSq_int_mul_add, dyadicLower_re, dyadicLower_im]
  push_cast
  rw [show ((v.1 0 : ℝ) * (z.im / 2)) ^ 2 +
      ((v.1 0 : ℝ) * ((z.re + b) / 2) + v.1 1) ^ 2 =
      (((v.1 0 : ℝ) * z.im) ^ 2 +
        ((v.1 0 : ℝ) * z.re + ((v.1 0 : ℝ) * b + 2 * v.1 1)) ^ 2) / 4 by ring]
  simp [div_eq_mul_inv]
  ring

/-- A primitive row returning above height one has first entry `0` or `±1`;
for a nonzero first entry, its shifted second entry lies in `[-1,1]`. -/
theorem dyadic_return_row_bound {z : ℍ} (hz : z ∈ fd) (b : ℤ)
    (v : gammaSet 1 1 0) (hv : 1 < rowHeight v (dyadicLower b z)) :
    v.1 0 = 0 ∨ ((v.1 0 = 1 ∨ v.1 0 = -1) ∧
      -1 ≤ v.1 0 * b + 2 * v.1 1 ∧ v.1 0 * b + 2 * v.1 1 ≤ 1) := by
  by_cases hc : v.1 0 = 0
  · exact Or.inl hc
  right
  let c : ℤ := v.1 0
  let k : ℤ := c * b + 2 * v.1 1
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hy := fd_height_half hz
  have hx := abs_le.mp hz.2
  have hden : 0 < ((c : ℝ) * z.im) ^ 2 + ((c : ℝ) * z.re + k) ^ 2 := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (mul_ne_zero hcR z.im_pos.ne'))
      (sq_nonneg _)
  rw [lower_row_height, lt_div_iff₀ hden] at hv
  have hlt : ((c : ℝ) * z.im) ^ 2 + ((c : ℝ) * z.re + k) ^ 2 < 2 * z.im := by
    simpa only [one_mul] using hv
  have hc1 : c = 1 ∨ c = -1 := by
    rcases horoball_int_cases (d := 0) hc with hlarge | hsmall
    · have hm := mul_le_mul_of_nonneg_right hlarge (sq_nonneg z.im)
      have hsq : ((c : ℝ) * z.im) ^ 2 = (c : ℝ) ^ 2 * z.im ^ 2 := mul_pow _ _ _
      nlinarith only [hlt, hm, hsq, hy, sq_nonneg ((c : ℝ) * z.re + k),
        mul_pos z.im_pos (show 0 < 4 * z.im - 2 by linarith)]
    · have hsq : c ^ 2 = 1 := by exact_mod_cast hsmall.1
      have hfactor : (c - 1) * (c + 1) = 0 := by nlinarith only [hsq]
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  have hxsq : ((c : ℝ) * z.re + k) ^ 2 < 1 := by
    rcases hc1 with hc1 | hc1 <;> rw [hc1] at hlt ⊢ <;>
      norm_num only [Int.cast_one, Int.cast_neg, one_mul, neg_mul, neg_sq] at hlt ⊢ <;>
      nlinarith only [hlt, sq_nonneg (z.im - 1)]
  have hxlt : -1 < (c : ℝ) * z.re + k ∧ (c : ℝ) * z.re + k < 1 := by
    constructor <;> nlinarith only [hxsq, sq_nonneg ((c : ℝ) * z.re + k + 1),
      sq_nonneg ((c : ℝ) * z.re + k - 1)]
  have hk : (-2 : ℝ) < k ∧ (k : ℝ) < 2 := by
    rcases hc1 with hc1 | hc1 <;> rw [hc1] at hxlt <;>
      norm_num at hxlt <;> constructor <;> linarith
  have hk' : -2 < k ∧ k < 2 := by exact_mod_cast hk
  change c = 1 ∨ c = -1 at hc1
  change (v.1 0 = 1 ∨ v.1 0 = -1) ∧ -1 ≤ k ∧ k ≤ 1
  exact ⟨hc1, by omega, by omega⟩

private def unitRow (d : ℤ) : gammaSet 1 1 0 :=
  ⟨![1, d], (gammaSet_one_mem_iff 1 _).mpr (by simp)⟩

private def negUnitRow (d : ℤ) : gammaSet 1 1 0 :=
  ⟨![-1, -d], (gammaSet_one_mem_iff 1 _).mpr (by simp)⟩

private theorem eq_unitRow (v : gammaSet 1 1 0) (d : ℤ) :
    v = unitRow d ↔ v.1 0 = 1 ∧ v.1 1 = d := by
  constructor
  · rintro rfl; simp [unitRow]
  · rintro ⟨hc, hd⟩
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [unitRow, hc, hd]

private theorem eq_negUnitRow (v : gammaSet 1 1 0) (d : ℤ) :
    v = negUnitRow d ↔ v.1 0 = -1 ∧ v.1 1 = -d := by
  constructor
  · rintro rfl; simp [negUnitRow]
  · rintro ⟨hc, hd⟩
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [negUnitRow, hc, hd]

private theorem lower_zero_support {z : ℍ} (hz : z ∈ fd)
    (v : gammaSet 1 1 0) (hv : 1 < rowHeight v (dyadicLower 0 z)) :
    v ∈ ({rowPlus, rowMinus, unitRow 0, negUnitRow 0} : Finset _) := by
  rcases dyadic_return_row_bound hz 0 v hv with hc | ⟨hc, hlo, hhi⟩
  · rcases (first_zero_iff v).mp hc with rfl | rfl <;> simp
  · have hd : v.1 1 = 0 := by omega
    rcases hc with hc | hc
    · rw [(eq_unitRow v 0).mpr ⟨hc, hd⟩]; simp
    · rw [(eq_negUnitRow v 0).mpr ⟨hc, by simpa using hd⟩]; simp

private theorem lower_one_support {z : ℍ} (hz : z ∈ fd)
    (v : gammaSet 1 1 0) (hv : 1 < rowHeight v (dyadicLower 1 z)) :
    v ∈ ({rowPlus, rowMinus, unitRow 0, negUnitRow 0,
      unitRow (-1), negUnitRow (-1)} : Finset _) := by
  rcases dyadic_return_row_bound hz 1 v hv with hc | ⟨hc, hlo, hhi⟩
  · rcases (first_zero_iff v).mp hc with rfl | rfl <;> simp
  · rcases hc with hc | hc
    · have hd : v.1 1 = 0 ∨ v.1 1 = -1 := by omega
      rcases hd with hd | hd
      · rw [(eq_unitRow v 0).mpr ⟨hc, hd⟩]; simp
      · rw [(eq_unitRow v (-1)).mpr ⟨hc, hd⟩]; simp
    · have hd : v.1 1 = 0 ∨ v.1 1 = 1 := by omega
      rcases hd with hd | hd
      · rw [(eq_negUnitRow v 0).mpr ⟨hc, by simpa using hd⟩]; simp
      · rw [(eq_negUnitRow v (-1)).mpr ⟨hc, by simpa using hd⟩]; simp

/-- The height of a return through the disk centered at `-k+i`. -/
def returnHeight (k : ℤ) (z : ℍ) : ℝ :=
  2 * z.im / ((z.re + k) ^ 2 + z.im ^ 2)

theorem returnHeight_gt_one_iff (k : ℤ) (z : ℍ) :
    1 < returnHeight k z ↔ (z.re + k) ^ 2 + (z.im - 1) ^ 2 < 1 := by
  have hd : 0 < (z.re + k) ^ 2 + z.im ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos z.im_pos)
  rw [returnHeight, lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith only [h]

private theorem unitRow_lower_height (d b : ℤ) (z : ℍ) :
    rowHeight (unitRow d) (dyadicLower b z) = returnHeight (b + 2 * d) z := by
  rw [lower_row_height]
  simp only [unitRow, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_one, one_mul, returnHeight]
  rw [add_comm (z.im ^ 2)]

private theorem negUnitRow_height (d : ℤ) (z : ℍ) :
    rowHeight (negUnitRow d) z = rowHeight (unitRow d) z := by
  rw [rowHeight_eq_div, rowHeight_eq_div, normSq_int_mul_add, normSq_int_mul_add]
  congr 1
  simp only [negUnitRow, unitRow, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one]
  ring

/-- Periodization of a height profile; the factor halves the signed primitive rows. -/
def cuspLift (f : ℝ → ℂ) (z : ℍ) : ℂ :=
  (1 / 2 : ℂ) * ∑' v : gammaSet 1 1 0, f (rowHeight v z)

theorem cuspLift_smul (f : ℝ → ℂ) (g : SL(2, ℤ)) (z : ℍ) :
    cuspLift f (g • z) = cuspLift f z := by
  have he (v : gammaSet 1 1 0) :
      rowHeight v (g • z) = rowHeight (gammaSetSelfEquiv g v) z := by
    unfold rowHeight
    rw [← mul_smul, ModularGroup.im_smul_eq_div_normSq,
      ModularGroup.im_smul_eq_div_normSq, denom_SL2Z, denom_SL2Z,
      gammaSetMatrix_mul_apply_one, gammaSetMatrix_mul_apply_one,
      gammaSetMatrix_apply_one_zero, gammaSetMatrix_apply_one_one,
      gammaSetSelfEquiv_apply_val]
  unfold cuspLift
  simp_rw [he]
  rw [(gammaSetSelfEquiv g).tsum_eq (fun v => f (rowHeight v z))]

theorem cuspLift_eq_of_mem_fd (f : ℝ → ℂ) (hf : ∀ y ≤ 1, f y = 0)
    {z : ℍ} (hz : z ∈ fd) : cuspLift f z = f z.im := by
  classical
  unfold cuspLift
  rw [tsum_eq_sum (s := {rowPlus, rowMinus})]
  · rw [Finset.sum_pair rowPlus_ne_rowMinus, rowHeight_rowPlus, rowHeight_rowMinus]
    ring
  · intro v hv
    apply hf
    apply rowHeight_le_one_of_mem_fd hz
    intro hc
    rcases (first_zero_iff v).mp hc with rfl | rfl <;> simp at hv

theorem cuspLift_lower_zero (f : ℝ → ℂ) (hf : ∀ y ≤ 1, f y = 0)
    {z : ℍ} (hz : z ∈ fd) :
    cuspLift f (dyadicLower 0 z) = f (z.im / 2) + f (returnHeight 0 z) := by
  classical
  unfold cuspLift
  rw [tsum_eq_sum (s := {rowPlus, rowMinus, unitRow 0, negUnitRow 0})]
  · rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_pair]
    · rw [rowHeight_rowPlus, rowHeight_rowMinus, negUnitRow_height,
        unitRow_lower_height, dyadicLower_im]
      norm_num
      ring
    all_goals simp [rowPlus, rowMinus, unitRow, negUnitRow]
  · intro v hv
    apply hf
    exact le_of_not_gt (fun h => hv (lower_zero_support hz v h))

theorem cuspLift_lower_one (f : ℝ → ℂ) (hf : ∀ y ≤ 1, f y = 0)
    {z : ℍ} (hz : z ∈ fd) :
    cuspLift f (dyadicLower 1 z) =
      f (z.im / 2) + f (returnHeight 1 z) + f (returnHeight (-1) z) := by
  classical
  unfold cuspLift
  rw [tsum_eq_sum (s :=
    {rowPlus, rowMinus, unitRow 0, negUnitRow 0, unitRow (-1), negUnitRow (-1)})]
  · rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert,
      Finset.sum_insert, Finset.sum_pair]
    · rw [rowHeight_rowPlus, rowHeight_rowMinus, negUnitRow_height,
        negUnitRow_height, unitRow_lower_height, unitRow_lower_height, dyadicLower_im]
      norm_num
      ring
    all_goals simp [rowPlus, rowMinus, unitRow, negUnitRow]
  · intro v hv
    apply hf
    exact le_of_not_gt (fun h => hv (lower_one_support hz v h))

/-- The upward branch `2z`. -/
def dyadicUpper (z : ℍ) : ℍ :=
  ⟨2 * (z : ℂ), by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) z.im_pos⟩

private theorem rowHeight_le_one_of_im_ge_one {z : ℍ} (hz : 1 ≤ z.im)
    (v : gammaSet 1 1 0) (hc : v.1 0 ≠ 0) : rowHeight v z ≤ 1 := by
  have hcR : (v.1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
  have hden : 0 < Complex.normSq ((v.1 0 : ℂ) * (z : ℂ) + v.1 1) := by
    rw [normSq_int_mul_add]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (mul_ne_zero hcR z.im_pos.ne'))
      (sq_nonneg _)
  rw [rowHeight_eq_div, div_le_one hden, normSq_int_mul_add]
  have hc2 : 1 ≤ (v.1 0 : ℝ) ^ 2 := by
    rcases horoball_int_cases (d := 0) hc with h | h
    · linarith
    · exact h.1.ge
  have hm := mul_le_mul_of_nonneg_right hc2 (sq_nonneg z.im)
  rw [mul_pow]
  nlinarith only [hm, sq_nonneg ((v.1 0 : ℝ) * z.re + v.1 1),
    mul_nonneg (sub_nonneg.mpr hz) z.im_pos.le]

theorem cuspLift_upper (f : ℝ → ℂ) (hf : ∀ y ≤ 1, f y = 0)
    {z : ℍ} (hz : z ∈ fd) : cuspLift f (dyadicUpper z) = f (2 * z.im) := by
  classical
  have him : (dyadicUpper z).im = 2 * z.im := by simp [dyadicUpper]
  unfold cuspLift
  rw [tsum_eq_sum (s := {rowPlus, rowMinus})]
  · rw [Finset.sum_pair rowPlus_ne_rowMinus, rowHeight_rowPlus, rowHeight_rowMinus, him]
    ring
  · intro v hv
    apply hf
    apply rowHeight_le_one_of_im_ge_one (by rw [him]; linarith [fd_height_half hz])
    intro hc
    rcases (first_zero_iff v).mp hc with rfl | rfl <;> simp at hv

/-- The globally automorphic truncation, obtained by removing every cusp lift. -/
def automorphicTruncation (u : ℂ) (Y : ℝ) (z : ℍ) : ℂ :=
  eisensteinLineModel u z - cuspLift
    (fun y => if Y < y then d4BMCompletedEisensteinCuspConstantPart .scalar u y else 0) z

theorem automorphicTruncation_smul {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (Y : ℝ) (g : SL(2, ℤ)) (z : ℍ) :
    automorphicTruncation u Y (g • z) = automorphicTruncation u Y z := by
  rw [automorphicTruncation, automorphicTruncation, eisensteinLineModel_smul hu,
    cuspLift_smul]

theorem automorphicTruncation_eq_of_mem_fd (u : ℂ) {Y : ℝ} (hY : 1 ≤ Y)
    {z : ℍ} (hz : z ∈ fd) :
    automorphicTruncation u Y z = truncatedLineModel u Y z := by
  rw [automorphicTruncation, cuspLift_eq_of_mem_fd _ _ hz]
  · rfl
  · intro y hy
    exact if_neg (not_lt.mpr (hy.trans hY))

/-- The normalized dyadic correspondence on functions on the upper half-plane. -/
def dyadicHecke (F : ℍ → ℂ) (z : ℍ) : ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
    (F (dyadicUpper z) + F (dyadicLower 0 z) + F (dyadicLower 1 z))

theorem dyadicHecke_coordinate (u : ℂ) (Y : ℝ) (z : ℍ) :
    dyadicHecke (truncatedLineModel u Y) z = heckeTruncated 2 u Y z := by
  simp only [dyadicHecke, heckeTruncated, heckeOp, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    zero_add, add_zero, truncatedLineModel_eq_truncatedLeg,
    dyadicLower_re, dyadicLower_im]
  have hr : (dyadicUpper z).re = 2 * z.re := by simp [dyadicUpper]
  have hi : (dyadicUpper z).im = 2 * z.im := by simp [dyadicUpper]
  rw [hr, hi]
  ring

/-- The missing compact-core term in the coordinate dyadic Hecke formula. -/
theorem automorphic_dyadic_correction (u : ℂ) {z : ℍ} (hz : z ∈ fd) :
    dyadicHecke (automorphicTruncation u 1) z = heckeTruncated 2 u 1 z -
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        ((if 1 < returnHeight 0 z then
            d4BMCompletedEisensteinCuspConstantPart .scalar u (returnHeight 0 z) else 0) +
          (if 1 < returnHeight 1 z then
            d4BMCompletedEisensteinCuspConstantPart .scalar u (returnHeight 1 z) else 0) +
          (if 1 < returnHeight (-1) z then
            d4BMCompletedEisensteinCuspConstantPart .scalar u (returnHeight (-1) z) else 0)) := by
  let f : ℝ → ℂ := fun y =>
    if 1 < y then d4BMCompletedEisensteinCuspConstantPart .scalar u y else 0
  have hf (y : ℝ) (hy : y ≤ 1) : f y = 0 := if_neg (not_lt.mpr hy)
  have h0 := cuspLift_lower_zero f hf hz
  have h1 := cuspLift_lower_one f hf hz
  have hu := cuspLift_upper f hf hz
  rw [← dyadicHecke_coordinate]
  change (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      ((eisensteinLineModel u (dyadicUpper z) - cuspLift f (dyadicUpper z)) +
        (eisensteinLineModel u (dyadicLower 0 z) - cuspLift f (dyadicLower 0 z)) +
        (eisensteinLineModel u (dyadicLower 1 z) - cuspLift f (dyadicLower 1 z))) = _
  rw [h0, h1, hu]
  have hi : (dyadicUpper z).im = 2 * z.im := by simp [dyadicUpper]
  simp only [dyadicHecke, truncatedLineModel, hi, dyadicLower_im]
  change _ = _ - (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
    (f (returnHeight 0 z) + f (returnHeight 1 z) + f (returnHeight (-1) z))
  dsimp [f]
  ring

/-- At a resonance, the three return disks carry the single surviving Weyl power. -/
theorem resonant_automorphic_dyadic_correction {u : ℂ} (hAu : msA u = 0)
    {z : ℍ} (hz : z ∈ fd) :
    dyadicHecke (automorphicTruncation u 1) z = heckeTruncated 2 u 1 z -
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * msB u *
        ((if 1 < returnHeight 0 z then (returnHeight 0 z : ℂ) ^ (1 / 2 - u) else 0) +
          (if 1 < returnHeight 1 z then (returnHeight 1 z : ℂ) ^ (1 / 2 - u) else 0) +
          (if 1 < returnHeight (-1) z then
            (returnHeight (-1) z : ℂ) ^ (1 / 2 - u) else 0)) := by
  rw [automorphic_dyadic_correction u hz]
  simp only [cuspConstantPart_eq_msAB, hAu, zero_mul, add_zero]
  split_ifs <;> ring

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
