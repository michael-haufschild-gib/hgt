import GaloisForLFunctions.RHTower.WeilWorkDeficitSharedMass
import GaloisForLFunctions.HTGeometry.SteinitzInverseCovariance

/-!
# Inverse-potential energy of the actual Weil spectral deficit

The inverse branch of the Steinitz matrix-energy remainder is applied to the
canonical shared atom weight of each Xi divisor copy. Its square representation
gives quantitative comparisons with the actual deficit count. All sums retain
multiplicity and every off-critical-line copy; no atomicity of the boundary
measure or decay estimate for this new energy is assumed.
-/

open GaloisForLFunctions.HTGeometry
open scoped BigOperators

noncomputable section

namespace RHTower.WeilSpectral

/-- Resolvent displacement of the actual clipped atom share from full overlap. -/
def deficitInverseDisplacement {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (q : XiZeroCopy) : ℝ := (1 + sharedCopyWeight hW q)⁻¹ - 1 / 2

/-- The source inverse-potential remainder, evaluated on the actual shared mass. -/
def deficitInverseWeight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (q : XiZeroCopy) : ℝ :=
  steinitzInverseBranchRemainder (1 + sharedCopyWeight hW q) 2

/-- Total inverse-potential energy on the actual positive-ordinate window. -/
def deficitInverseEnergy {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) : ℝ :=
  ∑ q ∈ (finite_deficitWindow T).toFinset, deficitInverseWeight hW q

theorem deficitInverseDisplacement_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (q : XiZeroCopy) :
    deficitInverseDisplacement hW q =
      deficitWeight hW q / (2 * (1 + sharedCopyWeight hW q)) := by
  have hs : 1 + sharedCopyWeight hW q ≠ 0 := ne_of_gt (by
    linarith [sharedCopyWeight_nonneg hW q])
  unfold deficitInverseDisplacement
  field_simp [hs]
  simp only [sharedCopyWeight]
  ring

theorem deficitInverseDisplacement_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (q : XiZeroCopy) : 0 ≤ deficitInverseDisplacement hW q := by
  rw [deficitInverseDisplacement_eq]
  exact div_nonneg (deficitWeight_nonneg hW q)
    (by linarith [sharedCopyWeight_nonneg hW q])

/-- The paper's rational remainder is exactly the squared reciprocal discrepancy. -/
theorem deficitInverseWeight_eq_sq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (q : XiZeroCopy) :
    deficitInverseWeight hW q = deficitInverseDisplacement hW q ^ 2 := by
  have hs : 1 + sharedCopyWeight hW q ≠ 0 := ne_of_gt (by
    linarith [sharedCopyWeight_nonneg hW q])
  unfold deficitInverseWeight deficitInverseDisplacement steinitzInverseBranchRemainder
  field_simp [hs]
  ring

theorem deficitInverseWeight_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (q : XiZeroCopy) : 0 ≤ deficitInverseWeight hW q := by
  rw [deficitInverseWeight_eq_sq]
  exact sq_nonneg _

/-- Exact recovery of the deficit from its reciprocal displacement. -/
theorem deficitWeight_eq_inverseDisplacement {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (q : XiZeroCopy) :
    deficitWeight hW q =
      2 * (1 + sharedCopyWeight hW q) * deficitInverseDisplacement hW q := by
  rw [deficitInverseDisplacement_eq]
  have hs : 1 + sharedCopyWeight hW q ≠ 0 := ne_of_gt (by
    linarith [sharedCopyWeight_nonneg hW q])
  field_simp [hs]

/-- The square loss is uniformly comparable with the inverse-potential remainder. -/
theorem deficitWeight_sq_inverse_bounds {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (q : XiZeroCopy) :
    4 * deficitInverseWeight hW q ≤ deficitWeight hW q ^ 2 ∧
      deficitWeight hW q ^ 2 ≤ 16 * deficitInverseWeight hW q := by
  have hs0 := sharedCopyWeight_nonneg hW q
  have hs1 := sharedCopyWeight_le_one hW q
  have hlo : 4 ≤ 4 * (1 + sharedCopyWeight hW q) ^ 2 := by nlinarith
  have hhi : 4 * (1 + sharedCopyWeight hW q) ^ 2 ≤ 16 := by nlinarith
  have hid : deficitWeight hW q ^ 2 =
      (4 * (1 + sharedCopyWeight hW q) ^ 2) * deficitInverseWeight hW q := by
    rw [deficitInverseWeight_eq_sq, deficitWeight_eq_inverseDisplacement]
    ring
  rw [hid]
  exact ⟨mul_le_mul_of_nonneg_right hlo (deficitInverseWeight_nonneg hW q),
    mul_le_mul_of_nonneg_right hhi (deficitInverseWeight_nonneg hW q)⟩

theorem deficitInverseEnergy_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (T : ℝ) : 0 ≤ deficitInverseEnergy hW T :=
  Finset.sum_nonneg fun q _ => deficitInverseWeight_nonneg hW q

private theorem deficitCount_eq_sum {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) :
    deficitCount hW T =
      ∑ q ∈ (finite_deficitWindow T).toFinset, deficitWeight hW q := by
  rw [deficitCount_eq_sum_window hW le_rfl]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Set.Finite.mem_toFinset] at hq
  exact if_pos hq

/-- Weighted comparison retaining the actual overlap-dependent coefficient. -/
theorem deficitCount_sq_le_inverseEnergy_weighted {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (T : ℝ) :
    deficitCount hW T ^ 2 ≤
      4 * (∑ q ∈ (finite_deficitWindow T).toFinset,
        (1 + sharedCopyWeight hW q) ^ 2) * deficitInverseEnergy hW T := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (finite_deficitWindow T).toFinset
    (fun q => 1 + sharedCopyWeight hW q) (deficitInverseDisplacement hW)
  have hd : deficitCount hW T = 2 *
      ∑ q ∈ (finite_deficitWindow T).toFinset,
        (1 + sharedCopyWeight hW q) * deficitInverseDisplacement hW q := by
    rw [deficitCount_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [deficitWeight_eq_inverseDisplacement]
    ring
  rw [hd]
  simp only [deficitInverseEnergy, deficitInverseWeight_eq_sq]
  nlinarith

/-- A uniform comparison with the actual number of zero copies in the window. -/
theorem deficitCount_sq_le_inverseEnergy {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (T : ℝ) :
    deficitCount hW T ^ 2 ≤
      16 * (finite_deficitWindow T).toFinset.card * deficitInverseEnergy hW T := by
  have hw := deficitCount_sq_le_inverseEnergy_weighted hW T
  have hb : (∑ q ∈ (finite_deficitWindow T).toFinset,
      (1 + sharedCopyWeight hW q) ^ 2) ≤
        4 * ((finite_deficitWindow T).toFinset.card : ℝ) := by
    calc
      _ ≤ ∑ _q ∈ (finite_deficitWindow T).toFinset, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro q _
        have := sharedCopyWeight_nonneg hW q
        have := sharedCopyWeight_le_one hW q
        nlinarith
      _ = _ := by simp [mul_comm]
  have he := deficitInverseEnergy_nonneg hW T
  nlinarith [mul_le_mul_of_nonneg_right hb he]

/-- Zero inverse energy is exactly complete coverage of this actual divisor window. -/
theorem deficitInverseEnergy_eq_zero_iff {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (T : ℝ) :
    deficitInverseEnergy hW T = 0 ↔ deficitCount hW T = 0 := by
  constructor
  · intro h
    have hb := deficitCount_sq_le_inverseEnergy hW T
    rw [h, mul_zero] at hb
    exact sq_eq_zero_iff.mp (le_antisymm hb (sq_nonneg _))
  · intro h
    rw [deficitCount_eq_sum] at h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun q _ => deficitWeight_nonneg hW q)).mp h
    apply Finset.sum_eq_zero
    intro q hq
    have hb := (deficitWeight_sq_inverse_bounds hW q).1
    rw [hz q hq, zero_pow (by norm_num)] at hb
    exact le_antisymm (by linarith) (deficitInverseWeight_nonneg hW q)

/-- The inverse remainder never exceeds one quarter of the missing mass. -/
theorem four_mul_deficitInverseEnergy_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (T : ℝ) :
    4 * deficitInverseEnergy hW T ≤ deficitCount hW T := by
  rw [deficitCount_eq_sum, deficitInverseEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  apply (deficitWeight_sq_inverse_bounds hW q).1.trans
  have := deficitWeight_nonneg hW q
  have := deficitWeight_le_one hW q
  nlinarith

/-- An off-critical-line copy pays the full reciprocal energy `1/4`. -/
theorem deficitInverseWeight_of_offLine {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (q : XiZeroCopy)
    (hq : (q.1 : ℂ).re ≠ 1 / 2) : deficitInverseWeight hW q = 1 / 4 := by
  rw [deficitInverseWeight_eq_sq]
  norm_num [deficitInverseDisplacement, sharedCopyWeight, deficitWeight, hq]

/-- The reciprocal energy counts every off-line copy, without losing multiplicity. -/
theorem offLine_card_le_four_mul_deficitInverseEnergy {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (T : ℝ) :
    (((finite_deficitWindow T).toFinset.filter
      (fun q => (q.1 : ℂ).re ≠ 1 / 2)).card : ℝ) ≤ 4 * deficitInverseEnergy hW T := by
  classical
  have hsub : (∑ q ∈ (finite_deficitWindow T).toFinset.filter
      (fun q => (q.1 : ℂ).re ≠ 1 / 2), deficitInverseWeight hW q) ≤
        deficitInverseEnergy hW T :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _ _ => deficitInverseWeight_nonneg hW q)
  have he : (∑ q ∈ (finite_deficitWindow T).toFinset.filter
      (fun q => (q.1 : ℂ).re ≠ 1 / 2), deficitInverseWeight hW q) =
        (((finite_deficitWindow T).toFinset.filter
          (fun q => (q.1 : ℂ).re ≠ 1 / 2)).card : ℝ) / 4 := by
    calc
      _ = ∑ _q ∈ (finite_deficitWindow T).toFinset.filter
          (fun q => (q.1 : ℂ).re ≠ 1 / 2), (1 / 4 : ℝ) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact deficitInverseWeight_of_offLine hW q (Finset.mem_filter.mp hq).2
      _ = _ := by simp [div_eq_mul_inv]
  linarith

end RHTower.WeilSpectral
