import GaloisForLFunctions.RHTower.WeilPaperDeficitInverseEnergy

/-!
# Recovering the inverse-potential deficit energy from the Weil continuation

The inverse energy is accessible through the existing Poisson atom recovery.
Clipping the recovered shared weights and taking the reciprocal square does not
increase the total atom-recovery error. One analytic scale controls every prefix
of a bounded ordinate window. No height-uniform recovery rate is asserted.
-/

open Filter Topology Set
open scoped BigOperators

noncomputable section

namespace RHTower.WeilSpectral

/-- Nonnegative overlap recovered from the actual Weil continuation at scale `b`. -/
def recoveredSharedCopyWeight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (b : ℝ) (q : XiZeroCopy) : ℝ := max (1 - regularizedDeficitWeight hW b q) 0

/-- Clipping the recovered share cannot magnify the original atom-recovery error. -/
theorem abs_recoveredSharedCopyWeight_sub_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (b : ℝ) (q : XiZeroCopy) :
    |recoveredSharedCopyWeight hW b q - sharedCopyWeight hW q| ≤
      |regularizedDeficitWeight hW b q - deficitWeight hW q| := by
  have h := abs_max_sub_max_le_abs (1 - regularizedDeficitWeight hW b q)
    (1 - deficitWeight hW q) 0
  rw [max_eq_left (show 0 ≤ 1 - deficitWeight hW q from sharedCopyWeight_nonneg hW q)] at h
  have he : (1 - regularizedDeficitWeight hW b q) - (1 - deficitWeight hW q) =
      -(regularizedDeficitWeight hW b q - deficitWeight hW q) := by ring
  rw [he, abs_neg] at h
  exact h

private theorem inverse_overlap_sq_lipschitz {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |((1 + s)⁻¹ - 1 / 2) ^ 2 - ((1 + t)⁻¹ - 1 / 2) ^ 2| ≤ |s - t| := by
  have hsp : 0 < 1 + s := by linarith
  have htp : 0 < 1 + t := by linarith
  have habs {x : ℝ} (hx : 0 ≤ x) : |(1 + x)⁻¹ - 1 / 2| ≤ 1 / 2 := by
    have hp : 0 < 1 + x := by linarith
    have h0 := inv_nonneg.mpr hp.le
    have h1 : (1 + x)⁻¹ ≤ 1 := by
      rw [← one_div, div_le_iff₀ hp]
      linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsum : |((1 + s)⁻¹ - 1 / 2) + ((1 + t)⁻¹ - 1 / 2)| ≤ 1 :=
    (abs_add_le _ _).trans (by linarith [habs hs, habs ht])
  have hp : 0 < (1 + s) * (1 + t) := mul_pos hsp htp
  calc
    _ = |((1 + s)⁻¹ - 1 / 2) - ((1 + t)⁻¹ - 1 / 2)| *
        |((1 + s)⁻¹ - 1 / 2) + ((1 + t)⁻¹ - 1 / 2)| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |((1 + s)⁻¹ - 1 / 2) - ((1 + t)⁻¹ - 1 / 2)| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |s - t| / ((1 + s) * (1 + t)) := by
      rw [sub_sub_sub_cancel_right, inv_sub_inv hsp.ne' htp.ne', abs_div,
        abs_of_pos hp]
      congr 1
      rw [show (1 + t) - (1 + s) = -(s - t) by ring, abs_neg]
    _ ≤ |s - t| := by
      apply (div_le_iff₀ hp).mpr
      have hden : 1 ≤ (1 + s) * (1 + t) := by nlinarith
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hden (abs_nonneg (s - t))

/-- The inverse energy computed from Poisson approximations to the actual atoms. -/
def recoveredDeficitInverseEnergy {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (b T : ℝ) : ℝ :=
  ∑ q ∈ (finite_deficitWindow T).toFinset,
    ((1 + recoveredSharedCopyWeight hW b q)⁻¹ - 1 / 2) ^ 2

/-- The same finite recovery error controls inverse energy at every smaller height. -/
theorem abs_recoveredDeficitInverseEnergy_sub_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (b : ℝ) {T M : ℝ} (hTM : T ≤ M) :
    |recoveredDeficitInverseEnergy hW b T - deficitInverseEnergy hW T| ≤
      deficitRecoveryError hW M b := by
  classical
  rw [recoveredDeficitInverseEnergy, deficitInverseEnergy, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ q ∈ (finite_deficitWindow T).toFinset,
        |regularizedDeficitWeight hW b q - deficitWeight hW q| := by
      apply Finset.sum_le_sum
      intro q _
      rw [deficitInverseWeight_eq_sq]
      apply (inverse_overlap_sq_lipschitz
        (le_max_right _ _) (sharedCopyWeight_nonneg hW q)).trans
      exact abs_recoveredSharedCopyWeight_sub_le hW b q
    _ ≤ deficitRecoveryError hW M b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        rw [Set.Finite.mem_toFinset] at hq ⊢
        exact ⟨hq.1, hq.2.trans hTM⟩
      · intro q _ _
        exact abs_nonneg _

/-- A comparison using values of the actual Weil continuation and its exact recovery error. -/
theorem deficitCount_sq_le_recoveredInverseEnergy {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (b T : ℝ) :
    deficitCount hW T ^ 2 ≤ 16 * (finite_deficitWindow T).toFinset.card *
      (recoveredDeficitInverseEnergy hW b T + deficitRecoveryError hW T b) := by
  have hr := abs_recoveredDeficitInverseEnergy_sub_le hW b (T := T) le_rfl
  have he : deficitInverseEnergy hW T ≤
      recoveredDeficitInverseEnergy hW b T + deficitRecoveryError hW T b := by
    linarith [(abs_le.mp hr).1]
  exact (deficitCount_sq_le_inverseEnergy hW T).trans
    (mul_le_mul_of_nonneg_left he (by positivity))

/-- Every bounded family of prefixes admits a common analytic inverse-energy recovery scale. -/
theorem exists_uniform_deficitInverseRecovery_scale {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b : ℝ, 0 < b → b < δ → ∀ T : ℝ, T ≤ M →
      |recoveredDeficitInverseEnergy hW b T - deficitInverseEnergy hW T| < ε := by
  have hev := (tendsto_deficitRecoveryError hW M).eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  exact ⟨δ, hδ, fun b hb hbδ T hTM =>
    (abs_recoveredDeficitInverseEnergy_sub_le hW b hTM).trans_lt (hsub ⟨hb, hbδ⟩)⟩

end RHTower.WeilSpectral
