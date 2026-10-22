import GaloisForLFunctions.HTGeometry.FiniteMatrixSchurPositiveQuarticDivisorCharge
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAdmissibleStageSpectralNonselection

/-!
# Theta-source admissible Schur-quartic nonselection

The current four-field theta-source approximation property does not select real-divisor stages.
More sharply, at every requested accuracy its admissible fibre contains a stage whose every Schur
packet has strictly positive quartic charge.  Thus Hilbert--Schmidt proximity, finite support,
trace zero, and the current regularity condition cannot force the quartic charge to vanish; an
additional arithmetic selection law is necessary.

The theta block is indexed by a finite subtype.  We reindex it canonically by `Fin`; symmetric
reindexing preserves the ordinary determinant, so the generic Schur/divisor theorem applies
without changing the spectral assertion.
-/

open Complex Matrix

namespace RHTower.HedenmalmThetaSource

open HilbertSchmidt GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical `Fin`-indexed presentation of a theta-source finite block. -/
def thetaSourceReindexedBlockMatrix
    (SK : Finset thetaIndex × (thetaIndex × thetaIndex → ℂ)) :
    Matrix (Fin (Fintype.card ↑SK.1)) (Fin (Fintype.card ↑SK.1)) ℂ :=
  Matrix.reindex (Fintype.equivFin ↑SK.1) (Fintype.equivFin ↑SK.1)
    (blockMatrix SK.2 SK.1)

/-- At every accuracy the current admissible fibre contains a nonreal-divisor stage, and every
Schur packet of its canonically reindexed block has strictly positive quartic charge. -/
theorem exists_thetaSourceSignedApproximationProperty_schurQuarticPositive
    (k : ℕ) :
    ∃ (SK : Finset thetaIndex × (thetaIndex × thetaIndex → ℂ)) (z : ℂ),
      ThetaSourceSignedApproximationProperty k SK ∧
      ((1 : Matrix ↑SK.1 ↑SK.1 ℂ) - z • blockMatrix SK.2 SK.1).det = 0 ∧
      z.im ≠ 0 ∧
      ∀ S : FiniteMatrixSchurPacket (thetaSourceReindexedBlockMatrix SK),
        0 < finiteMatrixSchurPositiveQuarticCharge S := by
  obtain ⟨SK, z, hproperty, hdet, him⟩ :=
    exists_thetaSourceSignedApproximationProperty_nonrealDivisor k
  refine ⟨SK, z, hproperty, hdet, him, ?_⟩
  have hreindexDet :
      ((1 : Matrix (Fin (Fintype.card ↑SK.1)) (Fin (Fintype.card ↑SK.1)) ℂ) -
          z • thetaSourceReindexedBlockMatrix SK).det = 0 := by
    calc
      ((1 : Matrix (Fin (Fintype.card ↑SK.1)) (Fin (Fintype.card ↑SK.1)) ℂ) -
          z • thetaSourceReindexedBlockMatrix SK).det =
          (Matrix.reindex (Fintype.equivFin ↑SK.1) (Fintype.equivFin ↑SK.1)
            ((1 : Matrix ↑SK.1 ↑SK.1 ℂ) - z • blockMatrix SK.2 SK.1)).det := by
              congr 1
              ext i j
              simp [thetaSourceReindexedBlockMatrix, Matrix.reindex_apply, Matrix.one_apply]
      _ = ((1 : Matrix ↑SK.1 ↑SK.1 ℂ) - z • blockMatrix SK.2 SK.1).det :=
        Matrix.det_reindex_self (Fintype.equivFin ↑SK.1) _
      _ = 0 := hdet
  intro S
  exact finiteMatrixSchurPositiveQuarticCharge_pos_of_nonrealDivisor S hreindexDet him

/-- The current source approximation property cannot select zero quartic charge, even when zero
charge is required for every Schur presentation. -/
theorem thetaSourceSignedApproximationProperty_not_schurQuarticSelecting
    (k : ℕ) :
    ¬ ∀ SK : Finset thetaIndex × (thetaIndex × thetaIndex → ℂ),
      ThetaSourceSignedApproximationProperty k SK →
      ∀ S : FiniteMatrixSchurPacket (thetaSourceReindexedBlockMatrix SK),
        finiteMatrixSchurPositiveQuarticCharge S = 0 := by
  intro hselect
  obtain ⟨SK, z, hproperty, hdet, him, hpositive⟩ :=
    exists_thetaSourceSignedApproximationProperty_schurQuarticPositive k
  let S : FiniteMatrixSchurPacket (thetaSourceReindexedBlockMatrix SK) :=
    Classical.choice (nonempty_finiteMatrixSchurPacket (thetaSourceReindexedBlockMatrix SK))
  have hzero := hselect SK hproperty S
  have hpos := hpositive S
  linarith

/-- Uniform class-complete nonselection theorem across all approximation accuracies. -/
theorem thetaSourceSignedApproximationProperty_schurQuartic_nonselective :
    ∀ k : ℕ,
      (∃ (SK : Finset thetaIndex × (thetaIndex × thetaIndex → ℂ)) (z : ℂ),
        ThetaSourceSignedApproximationProperty k SK ∧
        ((1 : Matrix ↑SK.1 ↑SK.1 ℂ) - z • blockMatrix SK.2 SK.1).det = 0 ∧
        z.im ≠ 0 ∧
        ∀ S : FiniteMatrixSchurPacket (thetaSourceReindexedBlockMatrix SK),
          0 < finiteMatrixSchurPositiveQuarticCharge S) ∧
      ¬ ∀ SK : Finset thetaIndex × (thetaIndex × thetaIndex → ℂ),
        ThetaSourceSignedApproximationProperty k SK →
        ∀ S : FiniteMatrixSchurPacket (thetaSourceReindexedBlockMatrix SK),
          finiteMatrixSchurPositiveQuarticCharge S = 0 := by
  intro k
  exact ⟨exists_thetaSourceSignedApproximationProperty_schurQuarticPositive k,
    thetaSourceSignedApproximationProperty_not_schurQuarticSelecting k⟩

end

end RHTower.HedenmalmThetaSource
