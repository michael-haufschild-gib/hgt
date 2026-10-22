import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality
import GaloisForLFunctions.RHTower.Deninger.DeningerFailureNerveMixedDaggerCoboundary

/-!
# Hasse support rigidity for the Deninger mixed-defect square

The four signed channels in the mixed source-reversal/analytic-dagger Bianchi square form a
zero-sum profile.  Consequently a nonzero square defect cannot be isolated in one channel.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry.ABHN

/-- Four signed channels in the Deninger mixed-defect Bianchi square. -/
noncomputable def deningerMixedDefectBianchiProfile
    (Sp Sq Ap Aq : ℂ) : Fin 4 →₀ ℂ :=
  Finsupp.equivFunOnFinite.symm ![
    Sp * (Sq - Aq),
    (Sp - Ap) * Aq,
    -(Sq * (Sp - Ap)),
    -((Sq - Aq) * Ap)]

@[simp]
theorem deningerMixedDefectBianchiProfile_zero (Sp Sq Ap Aq : ℂ) :
    deningerMixedDefectBianchiProfile Sp Sq Ap Aq 0 = Sp * (Sq - Aq) := rfl

@[simp]
theorem deningerMixedDefectBianchiProfile_one (Sp Sq Ap Aq : ℂ) :
    deningerMixedDefectBianchiProfile Sp Sq Ap Aq 1 = (Sp - Ap) * Aq := rfl

@[simp]
theorem deningerMixedDefectBianchiProfile_two (Sp Sq Ap Aq : ℂ) :
    deningerMixedDefectBianchiProfile Sp Sq Ap Aq 2 = -(Sq * (Sp - Ap)) := rfl

@[simp]
theorem deningerMixedDefectBianchiProfile_three (Sp Sq Ap Aq : ℂ) :
    deningerMixedDefectBianchiProfile Sp Sq Ap Aq 3 = -((Sq - Aq) * Ap) := rfl

/-- The signed Deninger square profile has total defect zero. -/
theorem deningerMixedDefectBianchiProfile_sum_eq_zero (Sp Sq Ap Aq : ℂ) :
    (deningerMixedDefectBianchiProfile Sp Sq Ap Aq).sum (fun _ z => z) = 0 := by
  rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
  change ∑ i : Fin 4, (![Sp * (Sq - Aq), (Sp - Ap) * Aq,
    -(Sq * (Sp - Ap)), -((Sq - Aq) * Ap)] : Fin 4 → ℂ) i = 0
  simp [Fin.sum_univ_succ]
  linear_combination deningerMixedDefect_bianchi Sp Sq Ap Aq

/-- Every nonzero Deninger square channel has a distinct nonzero companion. -/
theorem deningerMixedDefectBianchiProfile_exists_other_nonzero_channel
    (Sp Sq Ap Aq : ℂ) {i : Fin 4}
    (hi : deningerMixedDefectBianchiProfile Sp Sq Ap Aq i ≠ 0) :
    ∃ j : Fin 4, j ≠ i ∧ deningerMixedDefectBianchiProfile Sp Sq Ap Aq j ≠ 0 :=
  finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (deningerMixedDefectBianchiProfile Sp Sq Ap Aq)
    (deningerMixedDefectBianchiProfile_sum_eq_zero Sp Sq Ap Aq) hi

/-- A nonzero Deninger mixed-defect Bianchi profile occupies at least two channels. -/
theorem deningerMixedDefectBianchiProfile_two_le_support_card
    (Sp Sq Ap Aq : ℂ)
    (hne : deningerMixedDefectBianchiProfile Sp Sq Ap Aq ≠ 0) :
    2 ≤ (deningerMixedDefectBianchiProfile Sp Sq Ap Aq).support.card :=
  finsupp_two_le_support_card_of_sum_eq_zero
    (deningerMixedDefectBianchiProfile Sp Sq Ap Aq)
    (deningerMixedDefectBianchiProfile_sum_eq_zero Sp Sq Ap Aq) hne

end RHTower
