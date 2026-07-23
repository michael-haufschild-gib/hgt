import GaloisForLFunctions.HTGeometry.CofaceBoundaryReconstruction
import GaloisForLFunctions.HTGeometry.SourceConstraintHeight
import GaloisForLFunctions.HTGeometry.SquarefreeVeronesePairDetection

/-!
# Coface-boundary determinantal tomography universality

The weighted coface boundary presents its constraint ideal through maximal minors.  Independently,
the squarefree Veronese description supplies exact pair-face detection and source height.  Passing
through the proved ideal identification gives a direct law for the determinantal boundary: its
maximal-minor constraints are detected by every coordinate pair and appear first at support width
equal to the boundary order.
-/

namespace GaloisForLFunctions.VeroneseIdeal

open MvPolynomial Finset Matrix

noncomputable section

variable {F : Type*} [Field F]

/-- Membership in the coface maximal-minor ideal is exactly pair-face support tomography. -/
theorem mem_cofaceBoundaryMaximalMinorIdeal_iff_every_pair_meets_support
    (r : ℕ) (P : MvPolynomial (Fin (r + 1)) F) :
    P ∈ cofaceBoundaryMaximalMinorIdeal (F := F) r ↔
      ∀ d : Fin (r + 1) →₀ ℕ, coeff d P ≠ 0 →
        ∀ L : Finset (Fin (r + 1)), L.card = 2 → ¬ Disjoint d.support L := by
  rw [cofaceBoundaryMaximalMinorIdeal_eq_veroneseIdeal]
  exact mem_veroneseIdeal_iff_every_pair_meets_support (by simp) P

/-- The ideal reconstructed from coface maximal minors has exact squarefree source height `r`. -/
theorem cofaceBoundaryMaximalMinorIdeal_hasExactSquarefreeConstraintHeight (r : ℕ) :
    GaloisForLFunctions.HTGeometry.HasExactSquarefreeConstraintHeight
      (cofaceBoundaryMaximalMinorIdeal (F := F) r) r := by
  rw [cofaceBoundaryMaximalMinorIdeal_eq_veroneseIdeal]
  exact GaloisForLFunctions.HTGeometry.veroneseIdeal_hasExactSquarefreeConstraintHeight r

/-- **Coface determinantal tomography law.**  At every order, maximal-minor boundary constraints
have exact source height and are completely detected by pair faces. -/
theorem cofaceBoundaryMaximalMinor_tomography_and_constraintHeight (r : ℕ) :
    GaloisForLFunctions.HTGeometry.HasExactSquarefreeConstraintHeight
        (cofaceBoundaryMaximalMinorIdeal (F := F) r) r ∧
      ∀ P : MvPolynomial (Fin (r + 1)) F,
        P ∈ cofaceBoundaryMaximalMinorIdeal (F := F) r ↔
          ∀ d : Fin (r + 1) →₀ ℕ, coeff d P ≠ 0 →
            ∀ L : Finset (Fin (r + 1)), L.card = 2 →
              ¬ Disjoint d.support L := by
  exact ⟨cofaceBoundaryMaximalMinorIdeal_hasExactSquarefreeConstraintHeight r,
    mem_cofaceBoundaryMaximalMinorIdeal_iff_every_pair_meets_support r⟩

end


end GaloisForLFunctions.VeroneseIdeal
