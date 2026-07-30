import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Faithful split recovery kills Kadison defects

A positive Schwarz map with a positive Schwarz left inverse sends both of its Kadison defects into
the kernel of the recovery map.  If recovery is faithful on positive elements, both defects
vanish.  This is the abstract operator-algebraic bridge from split recovery to multiplicative
purity.

The hypotheses are stated explicitly because the current mathlib completely-positive-map API does
not yet expose Kadison--Schwarz as a theorem.  Every unital completely positive map satisfies the
two positivity and Schwarz hypotheses used below.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A B : Type*}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B]

/-- The right Kadison defect of a complex-linear map. -/
def rightKadisonDefect (φ : A →ₗ[ℂ] B) (a : A) : B :=
  φ (star a * a) - star (φ a) * φ a

/-- The left Kadison defect of a complex-linear map. -/
def leftKadisonDefect (φ : A →ₗ[ℂ] B) (a : A) : B :=
  φ (a * star a) - φ a * star (φ a)

/-- A Schwarz-positive split sends every right Kadison defect into the recovery kernel. -/
theorem map_rightKadisonDefect_eq_zero
    (φ : A →ₗ[ℂ] B) (ψ : B →ₗ[ℂ] A)
    (hsplit : ∀ x, ψ (φ x) = x)
    (hφ : ∀ x, 0 ≤ rightKadisonDefect φ x)
    (hψpos : ∀ y, 0 ≤ y → 0 ≤ ψ y)
    (hψSchwarz : ∀ y, star (ψ y) * ψ y ≤ ψ (star y * y))
    (a : A) :
    ψ (rightKadisonDefect φ a) = 0 := by
  apply le_antisymm
  · rw [rightKadisonDefect, map_sub, hsplit]
    exact sub_nonpos.mpr (by simpa [hsplit] using hψSchwarz (φ a))
  · exact hψpos _ (hφ a)

/-- A Schwarz-positive split sends every left Kadison defect into the recovery kernel. -/
theorem map_leftKadisonDefect_eq_zero
    (φ : A →ₗ[ℂ] B) (ψ : B →ₗ[ℂ] A)
    (hsplit : ∀ x, ψ (φ x) = x)
    (hφ : ∀ x, 0 ≤ leftKadisonDefect φ x)
    (hψpos : ∀ y, 0 ≤ y → 0 ≤ ψ y)
    (hψSchwarz : ∀ y, ψ y * star (ψ y) ≤ ψ (y * star y))
    (a : A) :
    ψ (leftKadisonDefect φ a) = 0 := by
  apply le_antisymm
  · rw [leftKadisonDefect, map_sub, hsplit]
    exact sub_nonpos.mpr (by simpa [hsplit] using hψSchwarz (φ a))
  · exact hψpos _ (hφ a)

/-- Faithfulness of recovery on positive elements kills the right Kadison defect. -/
theorem rightKadisonDefect_eq_zero_of_faithful
    (φ : A →ₗ[ℂ] B) (ψ : B →ₗ[ℂ] A)
    (hsplit : ∀ x, ψ (φ x) = x)
    (hφ : ∀ x, 0 ≤ rightKadisonDefect φ x)
    (hψpos : ∀ y, 0 ≤ y → 0 ≤ ψ y)
    (hψSchwarz : ∀ y, star (ψ y) * ψ y ≤ ψ (star y * y))
    (hfaithful : ∀ y, 0 ≤ y → ψ y = 0 → y = 0)
    (a : A) :
    rightKadisonDefect φ a = 0 :=
  hfaithful _ (hφ a)
    (map_rightKadisonDefect_eq_zero φ ψ hsplit hφ hψpos hψSchwarz a)

/-- Faithfulness of recovery on positive elements kills the left Kadison defect. -/
theorem leftKadisonDefect_eq_zero_of_faithful
    (φ : A →ₗ[ℂ] B) (ψ : B →ₗ[ℂ] A)
    (hsplit : ∀ x, ψ (φ x) = x)
    (hφ : ∀ x, 0 ≤ leftKadisonDefect φ x)
    (hψpos : ∀ y, 0 ≤ y → 0 ≤ ψ y)
    (hψSchwarz : ∀ y, ψ y * star (ψ y) ≤ ψ (y * star y))
    (hfaithful : ∀ y, 0 ≤ y → ψ y = 0 → y = 0)
    (a : A) :
    leftKadisonDefect φ a = 0 :=
  hfaithful _ (hφ a)
    (map_leftKadisonDefect_eq_zero φ ψ hsplit hφ hψpos hψSchwarz a)

end

end GaloisForLFunctions.HTGeometry
