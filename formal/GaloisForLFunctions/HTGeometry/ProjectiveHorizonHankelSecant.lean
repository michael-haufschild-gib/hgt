import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Hankel secant form of the higher projective-horizon caustics

Reversing the hidden-coordinate columns turns every interior rectangular Schur--Toeplitz horizon
section into a consecutive square Hankel catalecticant.  Hence the complete corank filtration of
the horizon Jacobian is literally its Hankel rank filtration.  The final theorem identifies the
first caustic with the existence of a nonzero finite recurrence on the visible coefficient window.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- The square Hankel window on a consecutive coefficient packet. -/
def shiftedHorizonHankel {K : Type*}
    (h : ℕ → K) (s m : ℕ) : Matrix (Fin m) (Fin m) K :=
  fun r j => h (s + r + j)

/-- Reversing the hidden-coordinate order turns every interior rectangular horizon section into
its consecutive Hankel catalecticant. -/
theorem rectangularSchurToeplitz_reindex_rev_eq_shiftedHorizonHankel
    {K : Type*} [Zero K] (h : ℕ → K) (s m : ℕ) (hm : 0 < m) :
    Matrix.reindex (Equiv.refl (Fin m)) Fin.revPerm
        (rectangularSchurToeplitz h (s + m - 1) m) =
      shiftedHorizonHankel h s m := by
  ext r j
  change (if (Fin.rev j : ℕ) ≤ s + m - 1 + (r : ℕ) then
      h (s + m - 1 + (r : ℕ) - (Fin.rev j : ℕ)) else 0) =
    h (s + (r : ℕ) + (j : ℕ))
  rw [if_pos]
  · congr 1
    simp only [Fin.val_rev]
    omega
  · simp only [Fin.val_rev]
    omega

/-- The horizon Toeplitz section and its Hankel form have exactly the same rank. -/
theorem rectangularSchurToeplitz_rank_eq_shiftedHorizonHankel
    {K : Type*} [Field K] (h : ℕ → K) (s m : ℕ) (hm : 0 < m) :
    (rectangularSchurToeplitz h (s + m - 1) m).rank =
      (shiftedHorizonHankel h s m).rank := by
  rw [← rectangularSchurToeplitz_reindex_rev_eq_shiftedHorizonHankel h s m hm]
  exact (Matrix.rank_reindex (Equiv.refl (Fin m)) Fin.revPerm
    (rectangularSchurToeplitz h (s + m - 1) m)).symm

/-- Every higher loss-of-observability stratum is literally the corresponding Hankel rank
stratum after the canonical column reversal. -/
theorem rectangularSchurToeplitz_corank_ge_iff_hankel_corank_ge
    {K : Type*} [Field K] (h : ℕ → K) (s m k : ℕ) (hm : 0 < m) :
    k ≤ m - (rectangularSchurToeplitz h (s + m - 1) m).rank ↔
      k ≤ m - (shiftedHorizonHankel h s m).rank := by
  rw [rectangularSchurToeplitz_rank_eq_shiftedHorizonHankel h s m hm]

/-- A point of the first Hankel caustic is exactly a nonzero finite recurrence annihilating the
whole visible coefficient window.  This is the finite moment-recurrence form of an invisible
horizon mode. -/
theorem shiftedHorizonHankel_det_eq_zero_iff_exists_windowRecurrence
    {K : Type*} [CommRing K] [IsDomain K]
    (h : ℕ → K) (s m : ℕ) :
    (shiftedHorizonHankel h s m).det = 0 ↔
      ∃ c : Fin m → K, c ≠ 0 ∧
        ∀ r : Fin m, ∑ j : Fin m, h (s + (r : ℕ) + (j : ℕ)) * c j = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨c, hc, hzero⟩
    refine ⟨c, hc, ?_⟩
    intro r
    have hr := congrFun hzero r
    simpa [Matrix.mulVec, dotProduct, shiftedHorizonHankel] using hr
  · rintro ⟨c, hc, hrec⟩
    refine ⟨c, hc, ?_⟩
    funext r
    simpa [Matrix.mulVec, dotProduct, shiftedHorizonHankel] using hrec r

end GaloisForLFunctions.HTGeometry
