import GaloisForLFunctions.RHTower.PaperPrimeCoShiftFiniteKernels
import GaloisForLFunctions.HTGeometry.TwoProjectionSupersymmetry

/-!
# Exact separation of distinct finite prime packets

The finite co-shift kernel projections remember their prime sets injectively. They commute, so
their differences are tripotents. Consequently distinct prime packets are exactly distance one
apart, even modulo compact operators. The paper compact-ideal cost of a difference vanishes
precisely when the prime packets agree.
-/

namespace RHTower.PrimeCoShift

noncomputable section

open GaloisForLFunctions.HTGeometry
open scoped Classical ENNReal

/-- Any two finite arithmetic kernel projections commute. -/
theorem paperCoShiftFiniteProjection_commute (s : PaperCoShiftParameter)
    (F G : Finset Nat.Primes) :
    Commute (paperCoShiftFiniteProjection s F) (paperCoShiftFiniteProjection s G) := by
  induction F using Finset.induction_on with
  | empty => rw [paperCoShiftFiniteProjection_empty]; exact Commute.one_left _
  | @insert p F _ ih =>
    rw [paperCoShiftFiniteProjection_insert]
    apply Commute.mul_left _ ih
    apply ContinuousLinearMap.ext
    intro x
    simpa only [paperCoShiftFiniteProjection, starProjection_rowKer_eq s.property,
      mul_apply_eq_comp, Function.comp_apply] using
      (starProjection_finsetInf_comm (rowKer s.1)
        (starProjection_rowKer_commute s.property) G p x).symm

private theorem subset_of_projection_eq (s : PaperCoShiftParameter)
    (F G : Finset Nat.Primes)
    (h : paperCoShiftFiniteProjection s F = paperCoShiftFiniteProjection s G) : F ⊆ G := by
  intro p hp
  by_contra hpG
  obtain ⟨x, hx, hrow, hrest⟩ := paperCoShiftFiniteKernel_witness s G
  have hxG : x ∈ G.inf (rowKer s.1) := by
    rw [Finset.inf_eq_iInf]
    exact (Submodule.mem_iInf _).mpr fun q => (Submodule.mem_iInf _).mpr fun hq => hrow q hq
  have hfix : paperCoShiftFiniteProjection s F x = x := by
    rw [h]
    exact Submodule.starProjection_eq_self_iff.mpr hxG
  have hxF : x ∈ F.inf (rowKer s.1) := Submodule.starProjection_eq_self_iff.mp hfix
  have hpx : rowOp s.1 p x = 0 := (Finset.inf_le hp : F.inf (rowKer s.1) ≤ rowKer s.1 p) hxF
  change primeCoShift (primePNat p) x - primeScalar s.1 p • x = 0 at hpx
  rw [hrest p hpG, zero_sub, neg_eq_zero] at hpx
  have ha : primeScalar s.1 p ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_primeScalar]
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.property.pos) _
  exact (smul_eq_zero.mp hpx).elim ha hx

/-- The finite-prime kernel projection retains the complete prime packet. -/
theorem paperCoShiftFiniteProjection_injective (s : PaperCoShiftParameter) :
    Function.Injective (paperCoShiftFiniteProjection s) := by
  intro F G h
  exact le_antisymm (subset_of_projection_eq s F G h) (subset_of_projection_eq s G F h.symm)

private theorem norm_nonzero_tripotent_ge_one (D : H →L[ℂ] H)
    (hD : D * D * D = D) (hne : D ≠ 0) : 1 ≤ ‖D‖ := by
  have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hne
  have hnorm : ‖D‖ ≤ ‖D‖ * ‖D‖ * ‖D‖ := by
    calc
      ‖D‖ = ‖D * D * D‖ := congrArg norm hD.symm
      _ ≤ ‖D * D‖ * ‖D‖ := norm_mul_le _ _
      _ ≤ ‖D‖ * ‖D‖ * ‖D‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) hpos.le
  by_contra h
  have hlt : ‖D‖ < 1 := lt_of_not_ge h
  have hsq : ‖D‖ * ‖D‖ < 1 := by simpa using mul_self_lt_mul_self hpos.le hlt
  have hc := mul_lt_mul_of_pos_right hsq hpos
  nlinarith

/-- Different finite prime packets are exactly operator-norm distance one apart. -/
theorem paperCoShiftFiniteProjection_norm_sub (s : PaperCoShiftParameter)
    (F G : Finset Nat.Primes) :
    ‖paperCoShiftFiniteProjection s F - paperCoShiftFiniteProjection s G‖ =
      if F = G then 0 else 1 := by
  by_cases hFG : F = G
  · subst G
    simp
  rw [if_neg hFG]
  let P := paperCoShiftFiniteProjection s F
  let Q := paperCoShiftFiniteProjection s G
  have hP : P * P = P := (F.inf (rowKer s.1)).isIdempotentElem_starProjection
  have hQ : Q * Q = Q := (G.inf (rowKer s.1)).isIdempotentElem_starProjection
  have hPQ : P * Q = Q * P := (paperCoShiftFiniteProjection_commute s F G).eq
  have hcube : (P - Q) * (P - Q) * (P - Q) = P - Q := by
    noncomm_ring [hP, hQ, hPQ]
    rw [← mul_assoc Q Q P, hQ]
    abel
  apply le_antisymm
  · apply HTGeometry.norm_twoProjection_difference_le_one P Q hP hQ
    · exact (isSelfAdjoint_starProjection (F.inf (rowKer s.1))).star_eq
    · exact (isSelfAdjoint_starProjection (G.inf (rowKer s.1))).star_eq
  · apply norm_nonzero_tripotent_ge_one _ hcube
    intro hz
    exact hFG (paperCoShiftFiniteProjection_injective s (sub_eq_zero.mp hz))

/-- Compact perturbations cannot blur distinct finite prime packets. -/
theorem paperCoShiftFiniteProjection_sub_compactIdealDistance (s : PaperCoShiftParameter)
    (F G : Finset Nat.Primes) :
    compactIdealDistance (paperCoShiftFiniteProjection s F - paperCoShiftFiniteProjection s G) =
      if F = G then 0 else 1 := by
  have hmem := sub_mem (paperCoShiftFiniteProjection_mem_algebra s F)
    (paperCoShiftFiniteProjection_mem_algebra s G)
  rw [paperPrimeCoShiftAlgebra_compactIdealDistance ⟨_, hmem⟩,
    paperCoShiftFiniteProjection_norm_sub]

theorem paperCoShiftFiniteProjection_sub_compact_iff (s : PaperCoShiftParameter)
    (F G : Finset Nat.Primes) :
    IsCompactOperator (paperCoShiftFiniteProjection s F - paperCoShiftFiniteProjection s G) ↔
      F = G := by
  rw [paperPrimeCoShiftAlgebra_compact_sub_iff_eq
    ⟨_, paperCoShiftFiniteProjection_mem_algebra s F⟩
    ⟨_, paperCoShiftFiniteProjection_mem_algebra s G⟩]
  exact ⟨fun h => paperCoShiftFiniteProjection_injective s (congrArg Subtype.val h),
    fun h => by subst G; rfl⟩

/-- The proven paper trace detects exact equality of finite prime packets. -/
theorem paperCoShiftFiniteProjection_sub_traceCost (s : PaperCoShiftParameter)
    (F G : Finset Nat.Primes) :
    compactOperatorTraceCost H
      (paperCoShiftFiniteProjection s F - paperCoShiftFiniteProjection s G) =
        if F = G then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperCoShiftFiniteProjection_sub_compact_iff]
  split_ifs <;> rfl

end

end RHTower.PrimeCoShift
