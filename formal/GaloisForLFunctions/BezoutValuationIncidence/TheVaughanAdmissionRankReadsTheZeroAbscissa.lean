import GaloisForLFunctions.BezoutValuationIncidence.VaughanAdmissionAboveHalfDamping
import GaloisForLFunctions.BezoutValuationIncidence.TheZeroCutoffVaughanCoefficientSpace
import GaloisForLFunctions.BezoutValuationIncidence.TheReceiverAndTheColumnsOfTheDampingChain

/-! The extra admitted Vaughan direction recovers the receiver damping set and its zero-width index. -/
open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The directions admitted without the receiver; an empty convolution adds one unused coordinate. -/
def pmPronicVaughanBaselineRank (U V : ℕ) : ℕ := if U = 0 ∨ V = 0 then 3 else 2

/-- Dampings where the admitted coefficient space has an additional receiver direction. -/
def pmPronicVaughanRankDampings (U V : ℕ) : Set ℝ :=
  {ε | 0 < ε ∧ pmPronicVaughanBaselineRank U V + 1 ≤
    Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V)}

/-- At every positive damping, the extra rank is exactly admission of the original receiver. -/
theorem pmPronicVaughan_extra_rank_iff_receiver {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    pmPronicVaughanBaselineRank U V + 1 ≤
      Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) ↔
        ∃ B : ℝ, ∀ T : ℕ,
          GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm
            (pmBezoutInteriorPrefix ε) T ≤ B := by
  by_cases hUV : U = 0 ∨ V = 0
  · rw [pmPronicVaughanBaselineRank, if_pos hUV]
    by_cases hI : ∃ B : ℝ, ∀ T : ℕ,
        GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm
          (pmBezoutInteriorPrefix ε) T ≤ B
    · rw [finrank_pmPronicVaughanAdmittedSubmodule_empty_of_receiver hε hUV hI]
      exact iff_of_true (by norm_num) hI
    · rw [finrank_pmPronicVaughanAdmittedSubmodule_empty_of_not_receiver hε hUV hI]
      exact iff_of_false (by norm_num) hI
  · have hU : 1 ≤ U := by omega
    have hV : 1 ≤ V := by omega
    rw [pmPronicVaughanBaselineRank, if_neg hUV]
    by_cases hε2 : ε < 1 / 2
    · by_cases hI : ∃ B : ℝ, ∀ T : ℕ,
          GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm
            (pmBezoutInteriorPrefix ε) T ≤ B
      · rw [finrank_pmPronicVaughanAdmittedSubmodule_of_receiver hε hε2 hU hV hI]
        exact iff_of_true (by norm_num) hI
      · rw [finrank_pmPronicVaughanAdmittedSubmodule_of_not_receiver hε hε2 hU hV hI]
        exact iff_of_false (by norm_num) hI
    · have hI := exists_pronicNorm_pmBezoutInteriorPrefix_le_of_half_le (le_of_not_gt hε2)
      by_cases heq : ε = 1 / 2
      · subst ε
        rw [finrank_pmPronicVaughanAdmittedSubmodule_half hU hV]
        exact iff_of_true (by norm_num) hI
      · have hhalf : 1 / 2 < ε := by
          by_contra h
          exact heq (le_antisymm (not_lt.mp h) (le_of_not_gt hε2))
        rw [finrank_pmPronicVaughanAdmittedSubmodule_of_half_lt hhalf U V]
        exact iff_of_true (by norm_num) hI

/-- Uniform interior norm and energy bounds are equivalent, with no damping restriction. -/
theorem exists_pronicNorm_interior_bound_iff_energy_bound (ε : ℝ) :
    (∃ B : ℝ, ∀ T : ℕ,
      GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm
        (pmBezoutInteriorPrefix ε) T ≤ B) ↔
      ∃ B : ℝ, ∀ T : ℕ, pmBezoutInteriorPronicEnergy ε T ≤ B := by
  have hnorm (T : ℕ) :
      GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm
        (pmBezoutInteriorPrefix ε) T =
      Real.sqrt (pmBezoutInteriorPronicEnergy ε T) := by
    simp only [GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm,
      pmBezoutInteriorPronicEnergy, pronicSeq,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B ^ 2, fun T => ?_⟩
    have h := pow_le_pow_left₀
      (GaloisForLFunctions.TransHorizonIncidenceMechanics.pronicNorm_nonneg _ T) (hB T) 2
    simpa only [hnorm, Real.sq_sqrt (pmBezoutInteriorPronicEnergy_nonneg ε T)] using h
  · rintro ⟨B, hB⟩
    exact ⟨Real.sqrt B, fun T => by rw [hnorm]; exact Real.sqrt_le_sqrt (hB T)⟩

/-- The finite coefficient-space rank set is the actual interior receiver damping set. -/
theorem pmPronicVaughanRankDampings_eq_interiorReceiverDampings (U V : ℕ) :
    pmPronicVaughanRankDampings U V = interiorReceiverDampings := by
  ext ε
  simp only [pmPronicVaughanRankDampings, interiorReceiverDampings, Set.mem_setOf_eq]
  apply and_congr_right
  intro hε
  exact (pmPronicVaughan_extra_rank_iff_receiver hε U V).trans
    (exists_pronicNorm_interior_bound_iff_energy_bound ε)

theorem pmPronicVaughanRankDampings_eq_receiverDampings (U V : ℕ) :
    pmPronicVaughanRankDampings U V = receiverDampings := by
  rw [pmPronicVaughanRankDampings_eq_interiorReceiverDampings,
    interiorReceiverDampings_eq_receiverDampings]

/-- Different finite cutoff pairs recover the same rank-damping set. -/
theorem pmPronicVaughanRankDampings_eq (U V A B : ℕ) :
    pmPronicVaughanRankDampings U V = pmPronicVaughanRankDampings A B := by
  rw [pmPronicVaughanRankDampings_eq_receiverDampings,
    pmPronicVaughanRankDampings_eq_receiverDampings]

/-- The lower accumulation boundary of the admitted rank is the zeta zero width. -/
theorem sInf_derivedSet_pmPronicVaughanRankDampings (U V : ℕ) :
    sInf (derivedSet (pmPronicVaughanRankDampings U V)) = zetaZeroAbscissa - 1 / 2 := by
  rw [pmPronicVaughanRankDampings_eq_interiorReceiverDampings,
    sInf_derivedSet_interiorReceiverDampings_eq_zetaZeroAbscissa_sub_half]

/-- A fixed strip is exactly an admitted-rank accumulation boundary below half damping. -/
theorem zetaZeroAbscissa_lt_one_iff_vaughan_rank_boundary (U V : ℕ) :
    zetaZeroAbscissa < 1 ↔ sInf (derivedSet (pmPronicVaughanRankDampings U V)) < 1 / 2 := by
  rw [sInf_derivedSet_pmPronicVaughanRankDampings]
  constructor <;> intro h <;> linarith only [h]

/-- RH is accumulation at zero of dampings admitting the additional coefficient direction. -/
theorem riemannHypothesis_iff_accPt_zero_vaughan_rank (U V : ℕ) :
    RiemannHypothesis ↔ AccPt (0 : ℝ) (𝓟 (pmPronicVaughanRankDampings U V)) := by
  rw [pmPronicVaughanRankDampings_eq_receiverDampings]
  exact riemannHypothesis_iff_accPt_zero_receiverDampings

/-- The extra direction appearing cofinally near zero is an exact RH criterion. -/
theorem riemannHypothesis_iff_cofinal_vaughan_rank (U V : ℕ) :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      pmPronicVaughanBaselineRank U V + 1 ≤
        Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) := by
  rw [riemannHypothesis_iff_cofinal_budget]
  constructor
  · intro h δ hδ
    obtain ⟨ε, hε, hεδ, hE⟩ := h δ hδ
    have hm : ε ∈ receiverDampings := ⟨hε, hE⟩
    rw [← pmPronicVaughanRankDampings_eq_receiverDampings U V] at hm
    exact ⟨ε, hε, hεδ, hm.2⟩
  · intro h δ hδ
    obtain ⟨ε, hε, hεδ, hr⟩ := h δ hδ
    have hm : ε ∈ pmPronicVaughanRankDampings U V := ⟨hε, hr⟩
    rw [pmPronicVaughanRankDampings_eq_receiverDampings] at hm
    exact ⟨ε, hε, hεδ, hm.2⟩

/-- RH is also equivalent to the extra rank at every positive damping. -/
theorem riemannHypothesis_iff_forall_pos_vaughan_rank (U V : ℕ) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → pmPronicVaughanBaselineRank U V + 1 ≤
      Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) := by
  constructor
  · intro hRH ε hε
    have hm := Ioi_zero_subset_receiverDampings_of_riemannHypothesis hRH hε
    rw [← pmPronicVaughanRankDampings_eq_receiverDampings U V] at hm
    exact hm.2
  · intro h
    apply (riemannHypothesis_iff_cofinal_vaughan_rank U V).mpr
    intro δ hδ
    exact ⟨δ / 2, by linarith only [hδ], by linarith only [hδ],
      h (δ / 2) (by linarith only [hδ])⟩

/-- The extra Vaughan coefficient direction is square summability of the actual first damping column. -/
theorem pmPronicVaughan_extra_rank_iff_first_column_summable {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    pmPronicVaughanBaselineRank U V + 1 ≤
      Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) ↔
        Summable (fun n : ℕ => arithmeticDampingCenteredRow ε n 0 ^ 2) := by
  have h := mem_receiverDampings_iff_summable_first_column hε
  rw [← pmPronicVaughanRankDampings_eq_receiverDampings U V] at h
  simpa only [pmPronicVaughanRankDampings, Set.mem_setOf_eq, hε, true_and] using h

/-- The same finite rank condition pays every centered column of the arithmetic damping chain. -/
theorem pmPronicVaughan_extra_rank_iff_all_columns_summable {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    pmPronicVaughanBaselineRank U V + 1 ≤
      Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule ε U V) ↔
        ∀ k : ℕ, Summable (fun n : ℕ => arithmeticDampingCenteredRow ε n k ^ 2) := by
  have h := mem_receiverDampings_iff_forall_column_summable hε
  rw [← pmPronicVaughanRankDampings_eq_receiverDampings U V] at h
  simpa only [pmPronicVaughanRankDampings, Set.mem_setOf_eq, hε, true_and] using h

#print axioms pmPronicVaughan_extra_rank_iff_first_column_summable
#print axioms pmPronicVaughan_extra_rank_iff_all_columns_summable

#print axioms pmPronicVaughan_extra_rank_iff_receiver
#print axioms exists_pronicNorm_interior_bound_iff_energy_bound
#print axioms pmPronicVaughanRankDampings_eq_interiorReceiverDampings
#print axioms pmPronicVaughanRankDampings_eq_receiverDampings
#print axioms pmPronicVaughanRankDampings_eq
#print axioms sInf_derivedSet_pmPronicVaughanRankDampings
#print axioms zetaZeroAbscissa_lt_one_iff_vaughan_rank_boundary
#print axioms riemannHypothesis_iff_accPt_zero_vaughan_rank
#print axioms riemannHypothesis_iff_cofinal_vaughan_rank
#print axioms riemannHypothesis_iff_forall_pos_vaughan_rank
end GaloisForLFunctions.BezoutValuationIncidence
