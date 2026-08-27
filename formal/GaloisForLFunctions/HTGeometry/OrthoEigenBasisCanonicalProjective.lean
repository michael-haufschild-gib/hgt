import GaloisForLFunctions.HTGeometry.LocalExtensionSliceProjectiveGenericity
import GaloisForLFunctions.HTGeometry.SpectralCollisionFunctional

/-!
# Canonical maximal projectivity from an explicit eigenbasis

An explicit orthonormal eigenbasis with a maximally projective real eigenvalue packet already
determines the characteristic-root multiset.  Consequently the canonical eigenvalue ordering of
the same Hermitian matrix is maximally projective as well.  This removes a bookkeeping gap between
constructive diagonalizations and physical evolution theorems phrased using canonical eigenvalues.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A maximally projective packet carried by any orthonormal eigenbasis transfers to the canonical
Hermitian eigenvalue packet. -/
theorem maximallyProjectiveEnergy_eigenvalues_of_orthoEigenBasis
    {H : Matrix I I ℂ} {e : I → I → ℂ} {energy : I → ℝ}
    (hH : H.IsHermitian)
    (heb : IsOrthoEigenBasis H e energy)
    (hmax : MaximallyProjectiveEnergy energy) :
    MaximallyProjectiveEnergy hH.eigenvalues := by
  apply maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket
    H hH energy hmax
  intro i
  change (Matrix.scalar I (energy i : ℂ) - H).det = 0
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨e i, ?_, ?_⟩
  · intro hei
    have hii := heb.orth i i
    rw [hei] at hii
    simp [finiteComplexInner] at hii
  · rw [Matrix.sub_mulVec, heb.eigen]
    simp

end


end GaloisForLFunctions.HTGeometry
