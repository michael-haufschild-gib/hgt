import GaloisForLFunctions.RHTower.CCM.CCMPublishedRestrictedWeilMatrix

/-!
# Principal-submatrix tower for the published CCM restricted-Weil matrices

The centered packet `{-M, ..., M}` embeds into `{-N, ..., N}` whenever `M ≤ N` by shifting
finite indices through `N - M`.  The centered mode, clock, physical frequency, source, and
diagonal are unchanged by this embedding.  Consequently every smaller published matrix is
exactly a principal submatrix of every larger one.

This is an unconditional structural fact.  It does not assert positivity, identify these matrices
with the abstract Laurent Galerkin compression, or import any numerical computation.
-/

open scoped BigOperators Matrix ComplexOrder
open MeasureTheory Set Matrix

noncomputable section

namespace RHTower

/-- Center-preserving inclusion of the packet `{-M, ..., M}` into `{-N, ..., N}`. -/
def ccmPublishedCenteredInclusion (M N : ℕ) (hMN : M ≤ N) :
    Fin (2 * M + 1) → Fin (2 * N + 1) :=
  fun i => ⟨i.val + (N - M), by omega⟩

/-- The center-preserving packet inclusion is injective. -/
theorem ccmPublishedCenteredInclusion_injective (M N : ℕ) (hMN : M ≤ N) :
    Function.Injective (ccmPublishedCenteredInclusion M N hMN) := by
  intro i j hij
  apply Fin.ext
  simpa [ccmPublishedCenteredInclusion] using congrArg Fin.val hij

/-- Centered integer modes are literally preserved by packet inclusion. -/
@[simp] theorem ccmPublishedCenteredMode_inclusion
    (M N : ℕ) (hMN : M ≤ N) (i : Fin (2 * M + 1)) :
    ccmPublishedCenteredMode N (ccmPublishedCenteredInclusion M N hMN i) =
      ccmPublishedCenteredMode M i := by
  simp only [ccmPublishedCenteredMode, ccmPublishedCenteredInclusion, Fin.val_mk]
  omega

/-- Centered clocks are preserved by packet inclusion. -/
@[simp] theorem ccmPublishedCenteredClock_inclusion
    (M N : ℕ) (hMN : M ≤ N) (i : Fin (2 * M + 1)) :
    ccmPublishedCenteredClock N (ccmPublishedCenteredInclusion M N hMN i) =
      ccmPublishedCenteredClock M i := by
  simp [ccmPublishedCenteredClock]

/-- Physical Fourier frequencies are preserved by packet inclusion. -/
@[simp] theorem ccmPublishedCenteredFrequency_inclusion
    (a : ℝ) (M N : ℕ) (hMN : M ≤ N) (i : Fin (2 * M + 1)) :
    ccmPublishedCenteredFrequency a N (ccmPublishedCenteredInclusion M N hMN i) =
      ccmPublishedCenteredFrequency a M i := by
  simp [ccmPublishedCenteredFrequency]

/-- Published source coordinates are preserved by packet inclusion. -/
@[simp] theorem ccmPublishedCenteredSource_inclusion
    (a : ℝ) (M N : ℕ) (hMN : M ≤ N) (i : Fin (2 * M + 1)) :
    ccmPublishedCenteredSource a N (ccmPublishedCenteredInclusion M N hMN i) =
      ccmPublishedCenteredSource a M i := by
  simp [ccmPublishedCenteredSource]

/-- Published diagonal coordinates are preserved by packet inclusion. -/
@[simp] theorem ccmPublishedCenteredDiagonal_inclusion
    (a : ℝ) (M N : ℕ) (hMN : M ≤ N) (i : Fin (2 * M + 1)) :
    ccmPublishedCenteredDiagonal a N (ccmPublishedCenteredInclusion M N hMN i) =
      ccmPublishedCenteredDiagonal a M i := by
  simp [ccmPublishedCenteredDiagonal]

/-- Every entry of the larger matrix restricts to the corresponding smaller-packet entry. -/
theorem ccmPublishedRestrictedWeilMatrix_apply_inclusion
    (a : ℝ) (M N : ℕ) (hMN : M ≤ N)
    (i j : Fin (2 * M + 1)) :
    ccmPublishedRestrictedWeilMatrix a N
        (ccmPublishedCenteredInclusion M N hMN i)
        (ccmPublishedCenteredInclusion M N hMN j) =
      ccmPublishedRestrictedWeilMatrix a M i j := by
  by_cases hij : i = j
  · subst j
    rw [ccmPublishedRestrictedWeilMatrix_apply_self,
      ccmPublishedRestrictedWeilMatrix_apply_self]
    exact ccmPublishedCenteredDiagonal_inclusion a M N hMN i
  · have hbig :
        ccmPublishedCenteredInclusion M N hMN i ≠
          ccmPublishedCenteredInclusion M N hMN j :=
      fun h => hij (ccmPublishedCenteredInclusion_injective M N hMN h)
    rw [ccmPublishedRestrictedWeilMatrix_apply_of_ne a N hbig,
      ccmPublishedRestrictedWeilMatrix_apply_of_ne a M hij]
    simp

/-- Exact principal-tower law: rank `M` is the centered principal submatrix of rank `N`. -/
theorem ccmPublishedRestrictedWeilMatrix_submatrix_inclusion
    (a : ℝ) (M N : ℕ) (hMN : M ≤ N) :
    (ccmPublishedRestrictedWeilMatrix a N).submatrix
        (ccmPublishedCenteredInclusion M N hMN)
        (ccmPublishedCenteredInclusion M N hMN) =
      ccmPublishedRestrictedWeilMatrix a M := by
  ext i j
  exact ccmPublishedRestrictedWeilMatrix_apply_inclusion a M N hMN i j

/-- Canonical center-preserving inclusion into the next odd-dimensional packet. -/
def ccmPublishedCenteredSuccInclusion (N : ℕ) :
    Fin (2 * N + 1) → Fin (2 * (N + 1) + 1) :=
  ccmPublishedCenteredInclusion N (N + 1) (Nat.le_succ N)

/-- Closed successor law: every published matrix is a principal submatrix of the next one. -/
theorem ccmPublishedRestrictedWeilMatrix_submatrix_succ (a : ℝ) (N : ℕ) :
    (ccmPublishedRestrictedWeilMatrix a (N + 1)).submatrix
        (ccmPublishedCenteredSuccInclusion N)
        (ccmPublishedCenteredSuccInclusion N) =
      ccmPublishedRestrictedWeilMatrix a N := by
  exact ccmPublishedRestrictedWeilMatrix_submatrix_inclusion
    a N (N + 1) (Nat.le_succ N)

end RHTower
