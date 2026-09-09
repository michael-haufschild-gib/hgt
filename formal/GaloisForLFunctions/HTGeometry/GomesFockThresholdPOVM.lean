import GaloisForLFunctions.HTGeometry.GomesFockThresholdPartition
import GaloisForLFunctions.HTGeometry.FiniteBuresKrausDataProcessingLaw

/-! Finite spectral experiments from the countably additive Fock POVM. Arbitrary
finite threshold data produce a complete measurement in the corpus's existing
FiniteMatrixPOVM interface. Positivity, Borel measurability, disjointness and
normalization are all proved from the concrete construction, not supplied. This
is an application of the complete-observation-menu viewpoint of arXiv:2607.24901v1. -/

open scoped Matrix Classical ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- The effect associated to an entire Boolean threshold record. -/
def gomesFockThresholdEffect {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (bits : Fin n → Bool) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  gomesFockSpectralPOVM B (gomesFockThresholdCell cuts bits)

/-- Every finite record effect is the actual spectral-window matrix of its cell. -/
theorem gomesFockThresholdEffect_eq_window {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) (bits : Fin n → Bool) :
    gomesFockThresholdEffect B cuts bits = gomesFockWindowMatrix B (gomesFockThresholdCell cuts bits) := by
  simp [gomesFockThresholdEffect,gomesFockSpectralPOVM_apply,gomesFockThresholdCell_measurable]

/-- Every record effect is positive semidefinite. -/
theorem gomesFockThresholdEffect_posSemidef {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) (bits : Fin n → Bool) :
    (gomesFockThresholdEffect B cuts bits).PosSemidef :=
  gomesFockSpectralPOVM_posSemidef B _

/-- The complete finite menu sums exactly to identity. -/
theorem gomesFockThresholdEffect_sum {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) :
    ∑ bits : Fin n → Bool, gomesFockThresholdEffect B cuts bits = 1 := by
  have h := MeasureTheory.VectorMeasure.hasSum_of_disjoint_iUnion
    (v := gomesFockSpectralPOVM B) (gomesFockThresholdCell_measurable cuts)
    (gomesFockThresholdCell_pairwise cuts)
  simpa only [tsum_fintype,gomesFockThresholdCell_iUnion,gomesFockSpectralPOVM_univ,
    gomesFockThresholdEffect] using h.tsum_eq

/-- A canonical finite POVM, with Boolean records indexed by the existing Fin interface. -/
def gomesFockThresholdPOVM {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) :
    FiniteMatrixPOVM (d+1) (Fintype.card (Fin n → Bool)) where
  effect j := gomesFockThresholdEffect B cuts ((Fintype.equivFin (Fin n → Bool)).symm j)
  effect_posSemidef j := gomesFockThresholdEffect_posSemidef B cuts _
  completeness := by
    rw [(Fintype.equivFin (Fin n → Bool)).symm.sum_comp]
    exact gomesFockThresholdEffect_sum B cuts

/-- Reindexing into Fin preserves each labelled effect exactly. -/
theorem gomesFockThresholdPOVM_effect_record {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) (bits : Fin n → Bool) :
    (gomesFockThresholdPOVM B cuts).effect (Fintype.equivFin (Fin n → Bool) bits) =
      gomesFockThresholdEffect B cuts bits := by
  simp [gomesFockThresholdPOVM]

/-- The total scalar mass of the finite menu is exactly the original state mass. -/
theorem gomesFockThresholdMass_sum {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) (x : Fin (d+1) → ℂ) :
    ∑ bits : Fin n → Bool, gomesFockWindowMass B (gomesFockThresholdCell cuts bits) x =
      freeFockVectorMoment (gomesCompletedFockGenerators B) x 0 := by
  have h := MeasureTheory.VectorMeasure.hasSum_of_disjoint_iUnion
    (v := (gomesFockSpectralMeasure B x).toSignedMeasure)
    (gomesFockThresholdCell_measurable cuts) (gomesFockThresholdCell_pairwise cuts)
  simpa only [tsum_fintype,gomesFockThresholdCell_iUnion,Measure.toSignedMeasure_apply,
    gomesFockThresholdCell_measurable,MeasurableSet.univ,if_true,measureReal_def,
    gomesFockWindowMass,gomesFockSpectralMeasure_totalMass] using h.tsum_eq

end GaloisForLFunctions.HTGeometry
