import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.HTGeometry.ProjectiveSourceVisibilityParity
import GaloisForLFunctions.HTGeometry.SourceReversalNoSpectatorSelector
import GaloisForLFunctions.HTGeometry.TwoProjectionSupersymmetry

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Record polarity and paired composition form a unit-momentum supertranslation sector. -/
def sourceRecordPairD1N2 :
    SuperPoincare.D1N2 (Matrix (Fin 2) (Fin 2) ℝ) where
  supercharge0 := recordPolarityMatrix
  supercharge1 := pairRecordMatrix
  momentum := 1
  supercharge0_sq := recordPolarityMatrix_mul_self
  supercharge1_sq := pairRecordMatrix_mul_self
  mixed_anticommutator := by
    rw [recordPolarity_pair_anticommute]
    exact neg_add_cancel _

/-- Odd-degree binary-source polarity and exchange form a unit-momentum sector. -/
def oddBinaryFormSourceD1N2 (k : ℕ) :
    SuperPoincare.D1N2
      (Module.End ℝ (Fin ((2 * k + 1) + 1) → ℝ)) where
  supercharge0 := binaryFormSourcePolarity (K := ℝ) (2 * k + 1)
  supercharge1 := binaryFormSourceSwap (K := ℝ) (2 * k + 1)
  momentum := 1
  supercharge0_sq := by
    apply LinearMap.ext
    intro a
    funext i
    change (-1 : ℝ) ^ i.val * ((-1 : ℝ) ^ i.val * a i) = a i
    rw [← mul_assoc, ← pow_add,
      (show Even (i.val + i.val) from ⟨i.val, by omega⟩).neg_one_pow]
    simp
  supercharge1_sq := by
    apply LinearMap.ext
    intro a
    funext i
    simp [binaryFormSourceSwap]
  mixed_anticommutator := by
    have h := binaryFormSource_anticommute_of_odd
      (K := ℝ) (2 * k + 1) ⟨k, by omega⟩
    change
      (binaryFormSourcePolarity (K := ℝ) (2 * k + 1)).comp
          (binaryFormSourceSwap (K := ℝ) (2 * k + 1)) +
        (binaryFormSourceSwap (K := ℝ) (2 * k + 1)).comp
          (binaryFormSourcePolarity (K := ℝ) (2 * k + 1)) = 0
    rw [h]
    exact neg_add_cancel _

/-- The two noncommuting fixed-sector projections generate a split supertranslation sector. -/
def sourceFixedSectorProjectionD1N2Split :
    SuperPoincare.D1N2Split (Matrix (Fin 2) (Fin 2) ℝ) where
  supercharge0 := recordFixedSector - pairFixedSector
  supercharge1 := 1 - recordFixedSector - pairFixedSector
  mixed_anticommutator :=
    HTGeometry.twoProjection_difference_anticommutes_complement
      (show IsIdempotentElem recordFixedSector from recordFixedSector_idempotent)
      (show IsIdempotentElem pairFixedSector from pairFixedSector_idempotent)

/-- The two projection-generated momenta partition the identity. -/
theorem sourceFixedSectorProjection_momenta_add_eq_one :
    sourceFixedSectorProjectionD1N2Split.momentum0 +
        sourceFixedSectorProjectionD1N2Split.momentum1 = 1 := by
  exact HTGeometry.twoProjection_difference_sq_add_complement_sq
    (show IsIdempotentElem recordFixedSector from recordFixedSector_idempotent)
    (show IsIdempotentElem pairFixedSector from pairFixedSector_idempotent)

end GaloisForLFunctions.HTGeometry
