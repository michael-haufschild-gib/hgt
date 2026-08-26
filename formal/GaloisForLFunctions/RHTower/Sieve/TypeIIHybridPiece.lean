import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridVaughanScale

/-!
# Complete hybrid estimate for the Vaughan Type II piece

The unconditional block estimate is summed over the exact long-variable dyadic decomposition.
Only its explicit dyadic block count remains, as a logarithmic factor.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

def typeIIHybridPieceEnvelope (C T r : ℝ) (A B L U V : ℕ) : ℝ :=
  ((Nat.log 2 L : ℝ) + 1) *
    (Real.sqrt (8 * C * Real.log L * typeIIPolylogEnvelope B) *
      typeIIHybridVaughanRootEnvelope T r A B U V)

/-- Babu--Sankaranarayanan's hybrid Type II estimate, before elementary power rewriting. -/
theorem exists_norm_typeII_piece_le_hybrid_vaughan :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → B - 1 ≤ L →
      1 ≤ U → 1 ≤ V → 8 * r ≤ (A : ℝ) →
      ‖∑ n ∈ Finset.Ico A B,
          (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n‖
        ≤ typeIIHybridPieceEnvelope C T r A B L U V := by
  obtain ⟨C, hC0, hblock⟩ := exists_norm_maskedBlockSum_le_hybrid_vaughan
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V hT hr hA hB hL hBL hU hV h8
  have hstart := norm_typeII_piece_le_sum_blockSums hA hB hBL T r U V
  have hpoint : ∀ j ∈ Finset.range (Nat.log 2 L + 1),
      ‖maskedBlockSum T r A B L (2 ^ j) (min (2 ^ (j + 1)) (L + 1))
        (fun d => typeIILong U d) (fun m => typeIIShort V m)‖
      ≤ Real.sqrt (8 * C * Real.log L * typeIIPolylogEnvelope B) *
        typeIIHybridVaughanRootEnvelope T r A B U V := by
    intro j hj
    have hP : 1 ≤ 2 ^ j := one_le_pow₀ (by omega : 1 ≤ (2 : ℕ))
    have hpow2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    have hQ : 2 ≤ min (2 ^ (j + 1)) (L + 1) := by
      rw [le_min_iff]
      constructor
      · rw [hpow2]
        omega
      · omega
    have hQ2P : min (2 ^ (j + 1)) (L + 1) ≤ 2 * 2 ^ j := by
      exact le_trans (min_le_left _ _) (by rw [hpow2])
    have hQL : min (2 ^ (j + 1)) (L + 1) ≤ L + 1 := min_le_right _ _
    exact hblock hT hr hA hB hL hU hV hP hQ hQ2P hQL h8
  refine hstart.trans ?_
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [typeIIHybridPieceEnvelope, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl

end

end RHTower.Sieve
