import GaloisForLFunctions.HTGeometry.NegSupportedDimension

/-!
# The chamber law: the negative index equals the sign-chamber grading

The corpus has no single `kappa_-` definition for a Hermitian matrix; `KreinLangerInertia` expresses
the index as a subspace-dimension bound and mathlib's `sigNeg` is used elsewhere for quadratic
forms.  So the citable form of "the negative index equals the chamber grading" is two-sided:
every negative definite subspace is at most that large, AND one of exactly that size exists.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

open scoped Classical ComplexOrder

/-- **The chamber law.**  For a Hermitian form presented as positive semidefinite corrected by one
rank-one term per negative coefficient, and negative definite on the negative coordinate subspace,
the negative index is exactly the chamber grading: no negative definite subspace exceeds it, and the
negative coordinate subspace attains it. -/
theorem chamberLaw_negIndex_eq_grading {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ)
    (c : Fin d → ℝ)
    (v : Fin (negCount c) → (Fin d → ℂ))
    (hPSD : (G + ∑ i, Matrix.of fun j l => v i j * star (v i l)).PosSemidef)
    (hneg : ∀ x ∈ negSupported c, x ≠ 0 → (star x ⬝ᵥ G.mulVec x).re < 0) :
    (∀ W : Submodule ℂ (Fin d → ℂ),
        (∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ G.mulVec x).re < 0) →
        Module.finrank ℂ W ≤ negCount c)
      ∧ (∀ x ∈ negSupported c, x ≠ 0 → (star x ⬝ᵥ G.mulVec x).re < 0)
      ∧ Module.finrank ℂ (negSupported c) = negCount c := by
  refine ⟨?_, hneg, finrank_negSupported c⟩
  intro W hW
  exact neg_inertia_le_negCount G c v hPSD W hW

/-- The same read through the Hamming distance, which is the card's phrasing of the grading. -/
theorem chamberLaw_negIndex_eq_hammingDist {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ)
    (c : Fin d → ℝ)
    (v : Fin (negCount c) → (Fin d → ℂ))
    (hPSD : (G + ∑ i, Matrix.of fun j l => v i j * star (v i l)).PosSemidef)
    (hneg : ∀ x ∈ negSupported c, x ≠ 0 → (star x ⬝ᵥ G.mulVec x).re < 0) :
    (∀ W : Submodule ℂ (Fin d → ℂ),
        (∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ G.mulVec x).re < 0) →
        Module.finrank ℂ W ≤ hammingDist (signPattern c) (positiveChamber d))
      ∧ Module.finrank ℂ (negSupported c)
          = hammingDist (signPattern c) (positiveChamber d) := by
  obtain ⟨hup, _, hdim⟩ := chamberLaw_negIndex_eq_grading G c v hPSD hneg
  rw [← negCount_eq_hammingDist]
  exact ⟨hup, hdim⟩

end

end GaloisForLFunctions.HTGeometry
