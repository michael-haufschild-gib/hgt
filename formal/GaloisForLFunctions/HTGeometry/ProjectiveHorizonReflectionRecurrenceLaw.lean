import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCausticReflection
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonHankelSecant

/-!
# Reflection-forced projective-horizon recurrences

Reflection-fixed horizon coefficients force every odd-area rectangular Schur--Toeplitz caustic to
vanish.  Canonical reversal of its hidden-coordinate columns is the consecutive shifted Hankel
window.  Since column reindexing changes determinant only by a unit sign, the Hankel window is
singular and therefore carries a nonzero annihilating recurrence.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Odd-area reflection recurrence law.**  Every reflection-fixed coefficient sequence has a
nonzero recurrence on each consecutive Hankel window whose corresponding projective-horizon
rectangle has odd area. -/
theorem exists_reflectionFixed_shiftedHorizon_windowRecurrence_of_odd_area
    {K : Type*} [Field K] [CharZero K]
    (h : ℕ → K) (s m : ℕ)
    (hfix : ∀ k, (-1 : K) ^ k * h k = h k)
    (hodd : Odd (m * (s + m - 1))) :
    ∃ c : Fin m → K, c ≠ 0 ∧
      ∀ r : Fin m, ∑ j : Fin m, h (s + (r : ℕ) + (j : ℕ)) * c j = 0 := by
  have hm : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hm
    subst m
    norm_num at hodd
  have htoeplitz :
      (rectangularSchurToeplitz h (s + m - 1) m).det = 0 :=
    rectangularSchurToeplitz_det_eq_zero_of_reflectionFixed
      h (s + m - 1) m hfix hodd
  have hreindex := congrArg Matrix.det
    (rectangularSchurToeplitz_reindex_rev_eq_shiftedHorizonHankel h s m hm)
  have hhankel : (shiftedHorizonHankel h s m).det = 0 := by
    rw [Matrix.det_reindex, htoeplitz, mul_zero] at hreindex
    exact hreindex.symm
  exact (shiftedHorizonHankel_det_eq_zero_iff_exists_windowRecurrence h s m).mp hhankel

/-- Odd window start and odd window size are the intrinsic Hankel form of the odd-area parity
condition. -/
theorem exists_reflectionFixed_shiftedHorizon_windowRecurrence_of_odd_start_size
    {K : Type*} [Field K] [CharZero K]
    (h : ℕ → K) (s m : ℕ)
    (hfix : ∀ k, (-1 : K) ^ k * h k = h k)
    (hs : Odd s) (hm : Odd m) :
    ∃ c : Fin m → K, c ≠ 0 ∧
      ∀ r : Fin m, ∑ j : Fin m, h (s + (r : ℕ) + (j : ℕ)) * c j = 0 := by
  apply exists_reflectionFixed_shiftedHorizon_windowRecurrence_of_odd_area h s m hfix
  rcases hs with ⟨a, ha⟩
  rcases hm with ⟨b, hb⟩
  have hwindow : s + m - 1 = 2 * (a + b) + 1 := by omega
  rw [hwindow, hb]
  use 2 * b * (a + b) + b + (a + b)
  ring

end GaloisForLFunctions.HTGeometry
