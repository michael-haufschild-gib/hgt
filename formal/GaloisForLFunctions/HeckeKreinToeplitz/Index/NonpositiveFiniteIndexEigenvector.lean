import GaloisForLFunctions.HeckeKreinToeplitz.Index.InvariantNegativeGraph
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Nonpositive eigenvectors of finite-index isometries

A maximal invariant nonpositive graph is finite-dimensional. A complex
eigenvector of its induced invertible map gives a nonzero nonpositive
eigenvector of the original isometry.
-/

noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m : ℕ} (T : (H × EuclideanSpace ℂ (Fin m)) ≃L[ℂ]
      (H × EuclideanSpace ℂ (Fin m)))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w)

include hT in
/-- A positive-dimensional negative factor forces a nonpositive eigenvector. -/
theorem exists_nonpositive_eigenvector (hm : 0 < m) :
    ∃ (w : H × EuclideanSpace ℂ (Fin m)) (a : ℂ),
      w ≠ 0 ∧ a ≠ 0 ∧ (pairing w w).re ≤ 0 ∧ T w = a • w := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨A, hA, D, hD⟩ := exists_invariant_contraction_graph T hT
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue D.toLinearMap
  obtain ⟨x, hx⟩ := ha.exists_hasEigenvector
  have hDx : D x = a • x := Module.End.mem_eigenspace_iff.mp hx.1
  have hw : (A x, x) ≠ (0 : H × EuclideanSpace ℂ (Fin m)) :=
    fun h => hx.2 (congrArg Prod.snd h)
  have ha0 : a ≠ 0 := by
    intro he
    rw [he, zero_smul] at hDx
    exact hx.2 (D.injective (hDx.trans (map_zero D).symm))
  refine ⟨(A x, x), a, hw, ha0, (pairing_self_nonpos_iff _).mpr (hA x), ?_⟩
  rw [hD, hDx, map_smul]
  rfl

#print axioms exists_nonpositive_eigenvector

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
