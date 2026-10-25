import GaloisForLFunctions.BezoutValuationIncidence.VaughanPacketsHaveAnExactResidualEnergyDensity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The admitted Vaughan coefficient space

At positive fixed cutoffs below half damping, two compensated small-leg directions are
always admitted. The original receiver supplies the only possible third direction.
Explicit independent frames give the exact subspace, quotient dimension, and unique
coordinates without assuming that the receiver itself is admitted.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false


/-- Actual packet admission is a linear subspace of the five-dimensional coefficient space. -/
def pmPronicVaughanAdmittedSubmodule (ε : ℝ) (U V : ℕ) : Submodule ℝ (Fin 5 → ℝ) where
  carrier := {w | pmPronicVaughanPacketAdmitted ε U V w}
  zero_mem' := by
    refine ⟨0, fun T => ?_⟩
    simp [pmPronicVaughanPacket, pronicNorm]
  add_mem' := by
    intro w z hw hz
    obtain ⟨B, hB⟩ := hw
    obtain ⟨C, hC⟩ := hz
    refine ⟨B + C, fun T => ?_⟩
    have heq : pmPronicVaughanPacket ε U V (w + z) =
        fun n => pmPronicVaughanPacket ε U V w n + pmPronicVaughanPacket ε U V z n := by
      funext n
      simp only [pmPronicVaughanPacket, Pi.add_apply, add_mul, sum_add_distrib]
    rw [heq]
    exact (pronicNorm_add_le _ _ T).trans (add_le_add (hB T) (hC T))
  smul_mem' := by
    intro a w hw
    obtain ⟨B, hB⟩ := hw
    refine ⟨|a| * B, fun T => ?_⟩
    have heq : pmPronicVaughanPacket ε U V (a • w) =
        fun n => a * pmPronicVaughanPacket ε U V w n := by
      funext n
      simp only [pmPronicVaughanPacket, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]
    rw [heq, pronicNorm_smul]
    exact mul_le_mul_of_nonneg_left (hB T) (abs_nonneg _)

/-- The two always-admitted coefficient directions. -/
def pmPronicVaughanPaidFrame (ε : ℝ) (U V : ℕ) : Fin 2 → Fin 5 → ℝ :=
  ![pmPronicVaughanFirstPaidCoefficients ε U, pmPronicVaughanSecondPaidCoefficients ε V]

/-- The paid directions together with the original receiver direction. -/
def pmPronicVaughanFullFrame (ε : ℝ) (U V : ℕ) : Fin 3 → Fin 5 → ℝ :=
  ![pmPronicVaughanFirstPaidCoefficients ε U, pmPronicVaughanSecondPaidCoefficients ε V,
    fun _ => 1]

theorem pmPronicVaughanPaidFrame_linearIndependent (ε : ℝ) (U V : ℕ) :
    LinearIndependent ℝ (pmPronicVaughanPaidFrame ε U V) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he (j : Fin 5) : (∑ k : Fin 2, c k * pmPronicVaughanPaidFrame ε U V k j) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      congrArg (fun w : Fin 5 → ℝ => w j) hc
  have h0 := he 0
  have h1 := he 1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h0 h1
  change c 0 * 1 + c 1 * 0 = 0 at h0
  change c 0 * 0 + c 1 * 1 = 0 at h1
  fin_cases i
  · change c 0 = 0
    linarith only [h0]
  · change c 1 = 0
    linarith only [h1]

theorem pmPronicVaughanFullFrame_linearIndependent (ε : ℝ) (U V : ℕ) :
    LinearIndependent ℝ (pmPronicVaughanFullFrame ε U V) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he (j : Fin 5) : (∑ k : Fin 3, c k * pmPronicVaughanFullFrame ε U V k j) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      congrArg (fun w : Fin 5 → ℝ => w j) hc
  have h0 := he 0
  have h1 := he 1
  have h3 := he 3
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h0 h1 h3
  change c 0 * 1 + (c 1 * 0 + c 2 * 1) = 0 at h0
  change c 0 * 0 + (c 1 * 1 + c 2 * 1) = 0 at h1
  change c 0 * 0 + (c 1 * 0 + c 2 * 1) = 0 at h3
  fin_cases i
  · change c 0 = 0
    linarith only [h0, h3]
  · change c 1 = 0
    linarith only [h1, h3]
  · change c 2 = 0
    linarith only [h3]

/-- If the receiver is unpaid, precisely the two compensated small-leg directions survive. -/
theorem pmPronicVaughanAdmittedSubmodule_eq_paid_span {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hI : ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) :
    pmPronicVaughanAdmittedSubmodule ε U V =
      Submodule.span ℝ (Set.range (pmPronicVaughanPaidFrame ε U V)) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨hlinear, hconv, hsource⟩ :=
      (pmPronicVaughanPacketAdmitted_iff_of_pos_cutoffs hε hε2 hU hV w).mp hw
    have h3 := hsource.resolve_right hI
    have heq : w = (w 0 - w 3) • pmPronicVaughanFirstPaidCoefficients ε U +
        (w 1 - w 3) • pmPronicVaughanSecondPaidCoefficients ε V := by
      funext i
      have h := pmPronicVaughan_coefficients_eq_paid_add_receiver hε U V w hconv hlinear i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h3, add_zero] using h
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(0 : Fin 2), rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(1 : Fin 2), rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact pmPronicVaughanPacketAdmitted_firstPaid hε U V
    · exact pmPronicVaughanPacketAdmitted_secondPaid hε U V

/-- If the receiver is admitted, its direction is the only additional coefficient freedom. -/
theorem pmPronicVaughanAdmittedSubmodule_eq_full_span {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hI : ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) :
    pmPronicVaughanAdmittedSubmodule ε U V =
      Submodule.span ℝ (Set.range (pmPronicVaughanFullFrame ε U V)) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨hlinear, hconv, _⟩ :=
      (pmPronicVaughanPacketAdmitted_iff_of_pos_cutoffs hε hε2 hU hV w).mp hw
    have heq : w = ((w 0 - w 3) • pmPronicVaughanFirstPaidCoefficients ε U +
        (w 1 - w 3) • pmPronicVaughanSecondPaidCoefficients ε V) + w 3 • (fun _ => 1) := by
      funext i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one] using
        pmPronicVaughan_coefficients_eq_paid_add_receiver hε U V w hconv hlinear i
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(0 : Fin 3), rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(1 : Fin 3), rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(2 : Fin 3), rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact pmPronicVaughanPacketAdmitted_firstPaid hε U V
    · exact pmPronicVaughanPacketAdmitted_secondPaid hε U V
    · obtain ⟨B, hB⟩ := hI
      refine ⟨B, fun T => ?_⟩
      change pronicNorm (pmPronicVaughanPacket ε U V (fun _ => 1)) T ≤ B
      rw [show pmPronicVaughanPacket ε U V (fun _ => 1) = pmBezoutInteriorPrefix ε from
        funext (pmPronicVaughanPacket_one ε U V)]
      exact hB T

theorem finrank_pmPronicVaughanAdmittedSubmodule_of_not_receiver {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hI : ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) :
    Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) = 2 := by
  rw [pmPronicVaughanAdmittedSubmodule_eq_paid_span hε hε2 hU hV hI,
    finrank_span_eq_card (pmPronicVaughanPaidFrame_linearIndependent ε U V), Fintype.card_fin]

theorem finrank_pmPronicVaughanAdmittedSubmodule_of_receiver {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hI : ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) :
    Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) = 3 := by
  rw [pmPronicVaughanAdmittedSubmodule_eq_full_span hε hε2 hU hV hI,
    finrank_span_eq_card (pmPronicVaughanFullFrame_linearIndependent ε U V), Fintype.card_fin]

/-- A third admitted coefficient direction is exactly admission of the original receiver. -/
theorem finrank_pmPronicVaughanAdmittedSubmodule_eq_three_iff {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) :
    Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) = 3 ↔
      ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B := by
  constructor
  · intro hdim
    by_contra hI
    have htwo := finrank_pmPronicVaughanAdmittedSubmodule_of_not_receiver hε hε2 hU hV hI
    omega
  · exact finrank_pmPronicVaughanAdmittedSubmodule_of_receiver hε hε2 hU hV

/-- The coefficient quotient has dimension two exactly when the original receiver is admitted. -/
theorem finrank_pmPronicVaughanAdmittedQuotient_eq_two_iff {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) :
    Module.finrank ℝ ((Fin 5 → ℝ) ⧸ pmPronicVaughanAdmittedSubmodule ε U V) = 2 ↔
      ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B := by
  have h := Submodule.finrank_quotient_add_finrank (pmPronicVaughanAdmittedSubmodule ε U V)
  have hdim : Module.finrank ℝ (Fin 5 → ℝ) = 5 := by simp
  rw [hdim] at h
  rw [← finrank_pmPronicVaughanAdmittedSubmodule_eq_three_iff hε hε2 hU hV]
  omega

/-- Every admitted packet has unique coordinates in the two paid directions and the receiver. -/
theorem pmPronicVaughanPacketAdmitted_existsUnique_coordinates {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    {w : Fin 5 → ℝ} (hw : pmPronicVaughanPacketAdmitted ε U V w) :
    ∃! c : Fin 3 → ℝ,
      w = ∑ i : Fin 3, c i • pmPronicVaughanFullFrame ε U V i ∧
        (c 2 = 0 ∨ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) := by
  obtain ⟨hlinear, hconv, hsource⟩ :=
    (pmPronicVaughanPacketAdmitted_iff_of_pos_cutoffs hε hε2 hU hV w).mp hw
  let c : Fin 3 → ℝ := ![w 0 - w 3, w 1 - w 3, w 3]
  refine ⟨c, ⟨?_, hsource⟩, ?_⟩
  · funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change w i = (w 0 - w 3) * pmPronicVaughanFirstPaidCoefficients ε U i +
      ((w 1 - w 3) * pmPronicVaughanSecondPaidCoefficients ε V i + w 3 * 1)
    have h := pmPronicVaughan_coefficients_eq_paid_add_receiver hε U V w hconv hlinear i
    simpa only [mul_one, add_assoc] using h
  · intro d hd
    have h0 := congrArg (fun z : Fin 5 → ℝ => z 0) hd.1
    have h1 := congrArg (fun z : Fin 5 → ℝ => z 1) hd.1
    have h3 := congrArg (fun z : Fin 5 → ℝ => z 3) hd.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h0 h1 h3
    change w 0 = d 0 * 1 + (d 1 * 0 + d 2 * 1) at h0
    change w 1 = d 0 * 0 + (d 1 * 1 + d 2 * 1) at h1
    change w 3 = d 0 * 0 + (d 1 * 0 + d 2 * 1) at h3
    funext i
    fin_cases i
    · change d 0 = w 0 - w 3
      linarith only [h0, h3]
    · change d 1 = w 1 - w 3
      linarith only [h1, h3]
    · change d 2 = w 3
      linarith only [h3]

end GaloisForLFunctions.BezoutValuationIncidence
