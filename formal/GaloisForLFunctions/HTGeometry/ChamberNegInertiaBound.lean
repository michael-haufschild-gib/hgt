import GaloisForLFunctions.HTGeometry.SignChamberHammingGrading
import GaloisForLFunctions.HTGeometry.KreinLangerInertia

/-!
# The chamber grading bounds the negative inertia

A Pick kernel with finitely many signed atoms inserted is a positive semidefinite kernel corrected by
one positive rank-one term for each atom, with the sign of the atom.  Moving the negative atoms to
the other side exhibits the kernel as `positive semidefinite minus one rank-one per negative atom`.

The negative inertia is therefore at most the number of negative atoms, which by the chamber grading
is the Hamming distance of the coefficient chamber from the positive chamber.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Matrix
open scoped Classical ComplexOrder

/-- The negative coordinates of a coefficient vector, as a finite index set. -/
def negIndices {d : ℕ} (c : Fin d → ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun j => c j < 0

@[simp]
theorem card_negIndices {d : ℕ} (c : Fin d → ℝ) :
    (negIndices c).card = negCount c := rfl

@[simp]
theorem mem_negIndices {d : ℕ} (c : Fin d → ℝ) (j : Fin d) :
    j ∈ negIndices c ↔ c j < 0 := by
  simp [negIndices]

/-- The negative coordinates enumerated by the chamber grading. -/
def negIndicesEquiv {d : ℕ} (c : Fin d → ℝ) :
    {j // j ∈ negIndices c} ≃ Fin (negCount c) :=
  (negIndices c).equivFin.trans (finCongr (card_negIndices c))

/-- **The chamber grading bounds the negative inertia.**  If correcting a Hermitian kernel by one
positive rank-one term for each negative coordinate makes it positive semidefinite, then every
subspace on which the kernel is negative definite has dimension at most the chamber grading. -/
theorem neg_inertia_le_negCount {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (c : Fin d → ℝ) (v : Fin (negCount c) → (Fin n → ℂ))
    (hPSD : (H + ∑ i, Matrix.of fun j l => v i j * star (v i l)).PosSemidef)
    (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ H.mulVec x).re < 0) :
    Module.finrank ℂ W ≤ negCount c :=
  neg_inertia_le_of_posSemidef H v hPSD W hW

/-- **The negative inertia is bounded by the Hamming distance from the positive chamber.**  The same
bound read through the chamber grading. -/
theorem neg_inertia_le_hammingDist {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (c : Fin d → ℝ) (v : Fin (negCount c) → (Fin n → ℂ))
    (hPSD : (H + ∑ i, Matrix.of fun j l => v i j * star (v i l)).PosSemidef)
    (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ H.mulVec x).re < 0) :
    Module.finrank ℂ W ≤ hammingDist (signPattern c) (positiveChamber d) := by
  rw [← negCount_eq_hammingDist]
  exact neg_inertia_le_negCount H c v hPSD W hW

/-- In the positive chamber the kernel admits no negative directions at all. -/
theorem no_neg_direction_of_mem_positiveChamber {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (c : Fin d → ℝ) (hc : ∀ j, 0 ≤ c j)
    (v : Fin (negCount c) → (Fin n → ℂ))
    (hPSD : (H + ∑ i, Matrix.of fun j l => v i j * star (v i l)).PosSemidef)
    (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ H.mulVec x).re < 0) :
    Module.finrank ℂ W = 0 := by
  have hzero : negCount c = 0 := (negCount_eq_zero_iff c).2 hc
  have hle := neg_inertia_le_negCount H c v hPSD W hW
  omega

end

end GaloisForLFunctions.HTGeometry
