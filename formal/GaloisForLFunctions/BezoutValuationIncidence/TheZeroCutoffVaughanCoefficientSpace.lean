import GaloisForLFunctions.BezoutValuationIncidence.TheAdmittedVaughanCoefficientSpace
import GaloisForLFunctions.BezoutValuationIncidence.ZeroVaughanCutoffsRemoveTheSmoothObstruction
import GaloisForLFunctions.BezoutValuationIncidence.VaughanAdmissionAtHalfDamping

/-!
An empty Vaughan cutoff makes the small-small coefficient unused. Three paid
directions always remain, and receiver admission supplies exactly one more.
Explicit frames determine the admitted and quotient dimensions, including the
unconditional half-damping specialization.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The coefficient of the identically zero small-small piece at an empty cutoff. -/
def pmPronicVaughanUnusedCoefficients : Fin 5 → ℝ := ![0, 0, 1, 0, 0]

/-- Three always-admitted directions at an empty cutoff. -/
def pmPronicVaughanEmptyPaidFrame (ε : ℝ) (U V : ℕ) : Fin 3 → Fin 5 → ℝ :=
  ![pmPronicVaughanFirstPaidCoefficients ε U, pmPronicVaughanSecondPaidCoefficients ε V,
    pmPronicVaughanUnusedCoefficients]

/-- Those three directions together with the original receiver. -/
def pmPronicVaughanEmptyFullFrame (ε : ℝ) (U V : ℕ) : Fin 4 → Fin 5 → ℝ :=
  ![pmPronicVaughanFirstPaidCoefficients ε U, pmPronicVaughanSecondPaidCoefficients ε V,
    pmPronicVaughanUnusedCoefficients, fun _ => 1]

/-- The unused small-small coefficient represents the zero packet at an empty cutoff. -/
theorem pmPronicVaughanPacketAdmitted_unused (ε : ℝ) {U V : ℕ} (hUV : U = 0 ∨ V = 0) :
    pmPronicVaughanPacketAdmitted ε U V pmPronicVaughanUnusedCoefficients := by
  have heq : pmPronicVaughanPacket ε U V pmPronicVaughanUnusedCoefficients = fun _ => 0 := by
    funext n
    simp [pmPronicVaughanPacket, pmPronicVaughanUnusedCoefficients, Fin.sum_univ_succ,
      pmPronicVaughanPiece_smallSmall_eq_zero_of_zero_cutoff ε hUV n]
  refine ⟨0, fun T => ?_⟩
  rw [heq]
  simp [pronicNorm]

/-- Empty-cutoff centering leaves four uniquely readable coefficient directions. -/
theorem pmPronicVaughan_coefficients_eq_empty_frame {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ} (hUV : U = 0 ∨ V = 0) (w : Fin 5 → ℝ)
    (hL : pmPronicVaughanPacketLinearMean ε U V w = 0) (i : Fin 5) :
    w i = (w 0 - w 3) * pmPronicVaughanFirstPaidCoefficients ε U i +
      (w 1 - w 3) * pmPronicVaughanSecondPaidCoefficients ε V i +
      (w 2 - w 3) * pmPronicVaughanUnusedCoefficients i + w 3 := by
  let z : Fin 5 → ℝ := ![w 0, w 1, w 3, w 3, w 4]
  have hzL : pmPronicVaughanPacketLinearMean ε U V z = 0 :=
    (pmPronicVaughanPacket_replace_smallSmall_of_zero_cutoff ε hUV w).2.trans hL
  have hz := pmPronicVaughan_coefficients_eq_paid_add_receiver hε U V z rfl hzL i
  have heq : w i = z i + (w 2 - w 3) * pmPronicVaughanUnusedCoefficients i := by
    fin_cases i <;> simp [z, pmPronicVaughanUnusedCoefficients] <;> ring
  rw [heq, hz]
  change (w 0 - w 3) * pmPronicVaughanFirstPaidCoefficients ε U i +
    (w 1 - w 3) * pmPronicVaughanSecondPaidCoefficients ε V i + w 3 +
      (w 2 - w 3) * pmPronicVaughanUnusedCoefficients i = _
  ring

/-- The first three coordinates recover the three always-admitted frame coefficients. -/
theorem pmPronicVaughanEmptyPaidFrame_linearIndependent (ε : ℝ) (U V : ℕ) :
    LinearIndependent ℝ (pmPronicVaughanEmptyPaidFrame ε U V) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he (j : Fin 5) : (∑ k : Fin 3, c k * pmPronicVaughanEmptyPaidFrame ε U V k j) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      congrArg (fun w : Fin 5 → ℝ => w j) hc
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h0 h1 h2
  change c 0 * 1 + (c 1 * 0 + c 2 * 0) = 0 at h0
  change c 0 * 0 + (c 1 * 1 + c 2 * 0) = 0 at h1
  change c 0 * 0 + (c 1 * 0 + c 2 * 1) = 0 at h2
  fin_cases i
  · change c 0 = 0
    linarith only [h0]
  · change c 1 = 0
    linarith only [h1]
  · change c 2 = 0
    linarith only [h2]

/-- Reading the receiver coordinate first then recovers each of the other three coefficients. -/
theorem pmPronicVaughanEmptyFullFrame_linearIndependent (ε : ℝ) (U V : ℕ) :
    LinearIndependent ℝ (pmPronicVaughanEmptyFullFrame ε U V) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he (j : Fin 5) : (∑ k : Fin 4, c k * pmPronicVaughanEmptyFullFrame ε U V k j) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      congrArg (fun w : Fin 5 → ℝ => w j) hc
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h0 h1 h2 h3
  change c 0 * 1 + (c 1 * 0 + (c 2 * 0 + c 3 * 1)) = 0 at h0
  change c 0 * 0 + (c 1 * 1 + (c 2 * 0 + c 3 * 1)) = 0 at h1
  change c 0 * 0 + (c 1 * 0 + (c 2 * 1 + c 3 * 1)) = 0 at h2
  change c 0 * 0 + (c 1 * 0 + (c 2 * 0 + c 3 * 1)) = 0 at h3
  fin_cases i
  · change c 0 = 0
    linarith only [h0, h3]
  · change c 1 = 0
    linarith only [h1, h3]
  · change c 2 = 0
    linarith only [h2, h3]
  · change c 3 = 0
    linarith only [h3]

/-- Without receiver admission, precisely the three paid directions remain at an empty cutoff. -/
theorem pmPronicVaughanAdmittedSubmodule_eq_empty_paid_span {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ} (hUV : U = 0 ∨ V = 0)
    (hI : ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) :
    pmPronicVaughanAdmittedSubmodule ε U V =
      Submodule.span ℝ (Set.range (pmPronicVaughanEmptyPaidFrame ε U V)) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨hL, hsource⟩ := (pmPronicVaughanPacketAdmitted_iff_of_zero_cutoff hε hUV w).mp hw
    have h3 := hsource.resolve_right hI
    have heq : w = ((w 0 - w 3) • pmPronicVaughanFirstPaidCoefficients ε U +
        (w 1 - w 3) • pmPronicVaughanSecondPaidCoefficients ε V) +
          (w 2 - w 3) • pmPronicVaughanUnusedCoefficients := by
      funext i
      have h := pmPronicVaughan_coefficients_eq_empty_frame hε hUV w hL i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h3, add_zero] using h
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
    · exact pmPronicVaughanPacketAdmitted_unused ε hUV

/-- Receiver admission adds exactly the fourth direction at an empty cutoff. -/
theorem pmPronicVaughanAdmittedSubmodule_eq_empty_full_span {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ} (hUV : U = 0 ∨ V = 0)
    (hI : ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) :
    pmPronicVaughanAdmittedSubmodule ε U V =
      Submodule.span ℝ (Set.range (pmPronicVaughanEmptyFullFrame ε U V)) := by
  apply le_antisymm
  · intro w hw
    have hL := ((pmPronicVaughanPacketAdmitted_iff_of_zero_cutoff hε hUV w).mp hw).1
    have heq : w = (((w 0 - w 3) • pmPronicVaughanFirstPaidCoefficients ε U +
        (w 1 - w 3) • pmPronicVaughanSecondPaidCoefficients ε V) +
          (w 2 - w 3) • pmPronicVaughanUnusedCoefficients) + w 3 • (fun _ => 1) := by
      funext i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one] using
        pmPronicVaughan_coefficients_eq_empty_frame hε hUV w hL i
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(0 : Fin 4), rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(1 : Fin 4), rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(2 : Fin 4), rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(3 : Fin 4), rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact pmPronicVaughanPacketAdmitted_firstPaid hε U V
    · exact pmPronicVaughanPacketAdmitted_secondPaid hε U V
    · exact pmPronicVaughanPacketAdmitted_unused ε hUV
    · obtain ⟨B, hB⟩ := hI
      refine ⟨B, fun T => ?_⟩
      change pronicNorm (pmPronicVaughanPacket ε U V (fun _ => 1)) T ≤ B
      rw [show pmPronicVaughanPacket ε U V (fun _ => 1) = pmBezoutInteriorPrefix ε from
        funext (pmPronicVaughanPacket_one ε U V)]
      exact hB T

/-- Without receiver admission, the empty-cutoff admitted space has dimension three. -/
theorem finrank_pmPronicVaughanAdmittedSubmodule_empty_of_not_receiver {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ} (hUV : U = 0 ∨ V = 0)
    (hI : ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) :
    Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) = 3 := by
  rw [pmPronicVaughanAdmittedSubmodule_eq_empty_paid_span hε hUV hI,
    finrank_span_eq_card (pmPronicVaughanEmptyPaidFrame_linearIndependent ε U V), Fintype.card_fin]

/-- Receiver admission gives the empty-cutoff admitted space dimension four. -/
theorem finrank_pmPronicVaughanAdmittedSubmodule_empty_of_receiver {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ} (hUV : U = 0 ∨ V = 0)
    (hI : ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) :
    Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) = 4 := by
  rw [pmPronicVaughanAdmittedSubmodule_eq_empty_full_span hε hUV hI,
    finrank_span_eq_card (pmPronicVaughanEmptyFullFrame_linearIndependent ε U V), Fintype.card_fin]

/-- At an empty cutoff, the fourth admitted direction is equivalent to the actual receiver. -/
theorem finrank_pmPronicVaughanAdmittedSubmodule_empty_eq_four_iff {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ} (hUV : U = 0 ∨ V = 0) :
    Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) = 4 ↔
      ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B := by
  constructor
  · intro hdim
    by_contra hI
    have hthree := finrank_pmPronicVaughanAdmittedSubmodule_empty_of_not_receiver hε hUV hI
    omega
  · exact finrank_pmPronicVaughanAdmittedSubmodule_empty_of_receiver hε hUV

/-- The empty-cutoff coefficient quotient has dimension one exactly when the receiver is admitted. -/
theorem finrank_pmPronicVaughanAdmittedQuotient_empty_eq_one_iff {ε : ℝ} (hε : 0 < ε)
    {U V : ℕ} (hUV : U = 0 ∨ V = 0) :
    Module.finrank ℝ ((Fin 5 → ℝ) ⧸ pmPronicVaughanAdmittedSubmodule ε U V) = 1 ↔
      ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B := by
  have h := Submodule.finrank_quotient_add_finrank (pmPronicVaughanAdmittedSubmodule ε U V)
  have hdim : Module.finrank ℝ (Fin 5 → ℝ) = 5 := by simp
  rw [hdim] at h
  rw [← finrank_pmPronicVaughanAdmittedSubmodule_empty_eq_four_iff hε hUV]
  omega

/-- Without receiver admission, the empty-cutoff quotient has dimension two. -/
theorem finrank_pmPronicVaughanAdmittedQuotient_empty_of_not_receiver
    {ε : ℝ} (hε : 0 < ε) {U V : ℕ} (hUV : U = 0 ∨ V = 0)
    (hI : ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) :
    Module.finrank ℝ ((Fin 5 → ℝ) ⧸ pmPronicVaughanAdmittedSubmodule ε U V) = 2 := by
  have h := Submodule.finrank_quotient_add_finrank (pmPronicVaughanAdmittedSubmodule ε U V)
  rw [finrank_pmPronicVaughanAdmittedSubmodule_empty_of_not_receiver hε hUV hI] at h
  have hdim : Module.finrank ℝ (Fin 5 → ℝ) = 5 := by simp
  rw [hdim] at h
  omega

/-- Receiver admission leaves a one-dimensional empty-cutoff quotient. -/
theorem finrank_pmPronicVaughanAdmittedQuotient_empty_of_receiver
    {ε : ℝ} (hε : 0 < ε) {U V : ℕ} (hUV : U = 0 ∨ V = 0)
    (hI : ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B) :
    Module.finrank ℝ ((Fin 5 → ℝ) ⧸ pmPronicVaughanAdmittedSubmodule ε U V) = 1 :=
  (finrank_pmPronicVaughanAdmittedQuotient_empty_eq_one_iff hε hUV).mpr hI

/-- At half damping an empty cutoff leaves only the linear-mean obstruction. -/
theorem pmPronicVaughanPacketAdmitted_half_iff_of_zero_cutoff
    {U V : ℕ} (hUV : U = 0 ∨ V = 0) (w : Fin 5 → ℝ) :
    pmPronicVaughanPacketAdmitted (1 / 2) U V w ↔
      pmPronicVaughanPacketLinearMean (1 / 2) U V w = 0 := by
  rw [pmPronicVaughanPacketAdmitted_iff_of_zero_cutoff (by norm_num) hUV w]
  exact and_iff_left (Or.inr (exists_pronicNorm_pmBezoutInteriorPrefix_le_of_half_le le_rfl))

/-- An empty cutoff has four admitted coefficient directions at half damping. -/
theorem finrank_pmPronicVaughanAdmittedSubmodule_empty_half
    {U V : ℕ} (hUV : U = 0 ∨ V = 0) :
    Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule (1 / 2) U V) = 4 :=
  finrank_pmPronicVaughanAdmittedSubmodule_empty_of_receiver (by norm_num) hUV
    (exists_pronicNorm_pmBezoutInteriorPrefix_le_of_half_le le_rfl)

/-- The empty-cutoff quotient has dimension one at half damping. -/
theorem finrank_pmPronicVaughanAdmittedQuotient_empty_half
    {U V : ℕ} (hUV : U = 0 ∨ V = 0) :
    Module.finrank ℝ ((Fin 5 → ℝ) ⧸ pmPronicVaughanAdmittedSubmodule (1 / 2) U V) = 1 :=
  finrank_pmPronicVaughanAdmittedQuotient_empty_of_receiver (by norm_num) hUV
    (exists_pronicNorm_pmBezoutInteriorPrefix_le_of_half_le le_rfl)

#print axioms pmPronicVaughanAdmittedSubmodule_eq_empty_paid_span
#print axioms pmPronicVaughanAdmittedSubmodule_eq_empty_full_span
#print axioms finrank_pmPronicVaughanAdmittedSubmodule_empty_of_not_receiver
#print axioms finrank_pmPronicVaughanAdmittedSubmodule_empty_of_receiver
#print axioms finrank_pmPronicVaughanAdmittedSubmodule_empty_eq_four_iff
#print axioms finrank_pmPronicVaughanAdmittedQuotient_empty_eq_one_iff
#print axioms pmPronicVaughanPacketAdmitted_unused
#print axioms pmPronicVaughan_coefficients_eq_empty_frame
#print axioms pmPronicVaughanEmptyPaidFrame_linearIndependent
#print axioms pmPronicVaughanEmptyFullFrame_linearIndependent
#print axioms finrank_pmPronicVaughanAdmittedQuotient_empty_of_not_receiver
#print axioms finrank_pmPronicVaughanAdmittedQuotient_empty_of_receiver
#print axioms pmPronicVaughanPacketAdmitted_half_iff_of_zero_cutoff
#print axioms finrank_pmPronicVaughanAdmittedSubmodule_empty_half
#print axioms finrank_pmPronicVaughanAdmittedQuotient_empty_half
end GaloisForLFunctions.BezoutValuationIncidence
