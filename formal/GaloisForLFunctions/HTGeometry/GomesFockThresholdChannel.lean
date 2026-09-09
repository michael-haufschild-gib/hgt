import GaloisForLFunctions.HTGeometry.GomesFockThresholdPOVM

/-! Physical readout channels for the concrete spectral threshold experiments.
The abstract Kraus and Bures/Hellinger results already in the corpus now apply
to arbitrary Fock generator data and arbitrary Gram-state data. All channel and
positivity obligations are discharged by construction. This tests the information
retained by the observation menus inspired by arXiv:2607.24901v1. -/

open scoped Matrix Classical ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Canonical Kraus realization of a complete threshold measurement. -/
def gomesFockThresholdChannel {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) :
    FiniteRectangularKrausChannel (d+1) (Fintype.card (Fin n → Bool))
      (Fin (Fintype.card (Fin n → Bool)) × Fin (d+1)) :=
  (gomesFockThresholdPOVM B cuts).measurementChannel

/-- The Born intensity for one complete threshold record. -/
def gomesFockThresholdBornRecord {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (C : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (bits : Fin n → Bool) : ℝ :=
  (C*gomesFockThresholdEffect B cuts bits).trace.re

/-- The concrete threshold Kraus operators satisfy exact completeness. -/
theorem gomesFockThresholdChannel_complete {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) :
    ∑ a, ((gomesFockThresholdChannel B cuts).operator a)ᴴ *
      (gomesFockThresholdChannel B cuts).operator a = 1 :=
  (gomesFockThresholdChannel B cuts).completeness

/-- The output records exactly the spectral Born trace pairings on its diagonal. -/
theorem gomesFockThresholdChannel_output {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (C : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (gomesFockThresholdChannel B cuts).evolveMatrix C =
      Matrix.diagonal (fun j => (C*gomesFockThresholdEffect B cuts
        ((Fintype.equivFin (Fin n → Bool)).symm j)).trace) :=
  (gomesFockThresholdPOVM B cuts).measurementChannel_evolveMatrix_eq_diagonal C

/-- Arbitrary Gram inputs produce the nonnegative real Born record on the output diagonal. -/
theorem gomesFockThresholdChannel_gram_output {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (Y : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (gomesFockThresholdChannel B cuts).evolveMatrix (Yᴴ*Y) =
      Matrix.diagonal (fun j => (gomesFockThresholdBornRecord B cuts (Yᴴ*Y)
        ((Fintype.equivFin (Fin n → Bool)).symm j) : ℂ)) :=
  (gomesFockThresholdPOVM B cuts).measurementChannel_evolveMatrix_eq_diagonal_ofReal
    (Matrix.posSemidef_conjTranspose_mul_self Y)

/-- The actual readout channel preserves total matrix mass. -/
theorem gomesFockThresholdChannel_trace {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (C : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    ((gomesFockThresholdChannel B cuts).evolveMatrix C).trace = C.trace := by
  have h := (gomesFockThresholdChannel B cuts).trace_evolve_mul C 1
  simpa only [Matrix.mul_one,FiniteRectangularKrausChannel.pullbackMatrix_one] using h

/-- Every spectral record has nonnegative intensity for arbitrary Gram-state data. -/
theorem gomesFockThresholdBornRecord_gram_nonneg {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (Y : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (bits : Fin n → Bool) :
    0 ≤ gomesFockThresholdBornRecord B cuts (Yᴴ*Y) bits :=
  finiteMatrix_re_trace_mul_nonneg_of_posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self Y) (gomesFockThresholdEffect_posSemidef B cuts bits)

/-- The complete spectral readout cannot reduce root fidelity below its quantum value. -/
theorem gomesFockThresholdChannel_fidelity_dataProcessing {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (Y Z : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    finiteBuresRootFidelity (Yᴴ*Y) (Zᴴ*Z) ≤
      finiteHellingerAffinity
        (fun j => gomesFockThresholdBornRecord B cuts (Yᴴ*Y)
          ((Fintype.equivFin (Fin n → Bool)).symm j))
        (fun j => gomesFockThresholdBornRecord B cuts (Zᴴ*Z)
          ((Fintype.equivFin (Fin n → Bool)).symm j)) :=
  (gomesFockThresholdPOVM B cuts).finiteBuresRootFidelity_le_finiteHellingerAffinity
    (Matrix.posSemidef_conjTranspose_mul_self Y) (Matrix.posSemidef_conjTranspose_mul_self Z)

end GaloisForLFunctions.HTGeometry
