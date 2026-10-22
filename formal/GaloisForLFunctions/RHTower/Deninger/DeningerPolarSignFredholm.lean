import GaloisForLFunctions.RHTower.Deninger.DeningerPolarSignCFC
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Invertibility from a trivial kernel

If `S² - 1` is compact and `S` has trivial kernel, then `S` is invertible.  This is the card's
reduction of the invertibility hypothesis `(1)` to the kernel condition `(1a)`.

The Fredholm alternative applied to the compact operator `K = S² - 1` at `-1` gives the
dichotomy: either `-1` is an eigenvalue of `K`, which would produce a nonzero vector killed by
`S²` and hence by `S`, or `-1` lies in the resolvent set, which makes `S² = 1 + K` invertible.
An element whose square is a unit and which commutes with itself is a unit.

* `deningerIsUnit_of_ker_eq_bot` : the reduction.
-/

namespace RHTower

open Module

section FredholmReduction

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- **Invertibility from a trivial kernel.**  If `S² - 1` is compact and `S` is injective, then
`S` is invertible. -/
theorem deningerIsUnit_of_ker_eq_bot (S : X →L[𝕜] X)
    (hcompact : IsCompactOperator (⇑(S * S - (1 : X →L[𝕜] X))))
    (hker : ∀ x : X, S x = 0 → x = 0) : IsUnit S := by
  have hsq : IsUnit (S * S) := by
    have hno : ¬ End.HasEigenvalue ((S * S - (1 : X →L[𝕜] X)) : End 𝕜 X) (-1) := by
      intro hev
      obtain ⟨x, hmem, hne⟩ := hev.exists_hasEigenvector
      rw [End.mem_eigenspace_iff] at hmem
      have hzero : S (S x) = 0 := by
        have hcoe : ((S * S - (1 : X →L[𝕜] X)) : End 𝕜 X) x = S (S x) - x := rfl
        rw [hcoe] at hmem
        have : S (S x) - x = -x := by simpa using hmem
        have hx : S (S x) = x + (-x) := by
          rw [← this]
          abel
        simpa using hx
      exact hne (hker x (hker (S x) hzero))
    rcases hcompact.hasEigenvalue_or_mem_resolventSet (μ := (-1 : 𝕜)) (by simp) with h | h
    · exact absurd h hno
    · rw [resolventSet, Set.mem_setOf_eq] at h
      have hmap : (algebraMap 𝕜 (X →L[𝕜] X)) (-1) - (S * S - (1 : X →L[𝕜] X))
          = -(S * S) := by
        have h1 : (algebraMap 𝕜 (X →L[𝕜] X)) (-1) = -1 := by simp
        rw [h1]
        abel
      rw [hmap] at h
      exact (IsUnit.neg_iff _).mp h
  exact ((Commute.refl S).isUnit_mul_iff.mp hsq).1

end FredholmReduction

end RHTower
