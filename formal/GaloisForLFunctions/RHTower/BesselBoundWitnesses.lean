import GaloisForLFunctions.RHTower.DirichletHilbertRiggingBarrier
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Realizations of the uniform Bessel-bound interface

Bessel's inequality is exactly the statement that an orthonormal family has uniform Bessel bound
one, so the interface is realized by every orthonormal mode family, by the zero family, and it is
monotone in the bound.  The non-diagonal normality barrier therefore applies to orthonormal frames
with no interface premise: no Hilbert vector has unit response against every member of an infinite
orthonormal family.
-/

namespace GaloisForLFunctions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Realizations -/

/-- **Bessel's inequality realizes the interface.**  An orthonormal mode family has uniform Bessel
bound one. -/
theorem hasBesselBound_of_orthonormal {u : ℕ → E} (hu : Orthonormal ℂ u) :
    HasBesselBound u 1 := by
  intro s x
  rw [one_mul]
  exact hu.sum_inner_products_le x

theorem hasBesselBound_zero : HasBesselBound (0 : ℕ → E) 0 := by
  intro s x
  simp

theorem HasBesselBound.mono {u : ℕ → E} {B B' : ℝ} (h : HasBesselBound u B)
    (hle : B ≤ B') : HasBesselBound u B' := by
  intro s x
  refine le_trans (h s x) ?_
  exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)

/-! ## The barrier with no interface premise -/

/-- **Orthonormal normality barrier.**  No Hilbert vector has unit response against every member of
an infinite orthonormal mode family. -/
theorem no_orthonormal_family_with_unit_response {u : ℕ → E} (hu : Orthonormal ℂ u) :
    ¬ ∃ y : E, ∀ i, inner ℂ (u i) y = 1 :=
  no_bessel_family_with_unit_response u 1 (hasBesselBound_of_orthonormal hu)

/-- Quantitative form: an orthonormal family can have unit response against one vector on at most
`‖y‖ ^ (2 : ℕ)` many modes. -/
theorem card_le_of_orthonormal_unit_response {u : ℕ → E} (hu : Orthonormal ℂ u)
    (s : Finset ℕ) (y : E) (hy : ∀ i ∈ s, inner ℂ (u i) y = 1) :
    (s.card : ℝ) ≤ ‖y‖ ^ (2 : ℕ) := by
  have h := card_le_of_bessel_unit_response u 1 (hasBesselBound_of_orthonormal hu) s y hy
  simpa using h

end GaloisForLFunctions
