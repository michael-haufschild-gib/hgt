import GaloisForLFunctions.RHTower.ArithmeticXiStokesCentralRankPort

/-!
# Coefficient equality patterns are a nontrivial invariant

Two finite Puiseux families occupy the same formal contact stratum when their coefficient equality
patterns agree at every exponent.  The relation is an equivalence, and it is genuinely coarser than
equality: rescaling every coefficient by one nonzero complex number changes the family but not a
single equality among its coefficients.  So the contact-numerator invariance theorem identifies
families that are not equal.
-/

namespace GaloisForLFunctions.IrregularStokes

open GaloisForLFunctions.HTGeometry

/-- Rescaling of a finite Puiseux family by a nonzero complex number. -/
noncomputable def scaleFinitePuiseuxFamily {m K N : ℕ} (c : ℂ) (hc : c ≠ 0)
    (p : FinitePuiseuxFamily m K N) : FinitePuiseuxFamily m K N where
  coeff i e := c * p.coeff i e
  coverDegree_pos := p.coverDegree_pos
  constant_zero i := by rw [p.constant_zero i, mul_zero]
  coeff_injective := by
    intro i j hij
    refine p.coeff_injective ?_
    funext e
    have h := congrFun hij e
    exact mul_left_cancel₀ hc h

/-- The pattern relation is reflexive. -/
theorem sameCoefficientEqualityPattern_refl {m K N : ℕ} (p : FinitePuiseuxFamily m K N) :
    SameCoefficientEqualityPattern p p := fun _ _ _ => Iff.rfl

/-- The pattern relation is symmetric. -/
theorem SameCoefficientEqualityPattern.symm {m K N : ℕ} {p q : FinitePuiseuxFamily m K N}
    (h : SameCoefficientEqualityPattern p q) : SameCoefficientEqualityPattern q p :=
  fun i j e => (h i j e).symm

/-- The pattern relation is transitive. -/
theorem SameCoefficientEqualityPattern.trans {m K N : ℕ} {p q r : FinitePuiseuxFamily m K N}
    (h : SameCoefficientEqualityPattern p q) (h' : SameCoefficientEqualityPattern q r) :
    SameCoefficientEqualityPattern p r := fun i j e => (h i j e).trans (h' i j e)

/-- **Rescaling preserves the coefficient equality pattern.**  So the contact stratum is blind to
one global nonzero scale. -/
theorem sameCoefficientEqualityPattern_scale {m K N : ℕ} (c : ℂ) (hc : c ≠ 0)
    (p : FinitePuiseuxFamily m K N) :
    SameCoefficientEqualityPattern p (scaleFinitePuiseuxFamily c hc p) := by
  intro i j e
  constructor
  · intro h
    show c * p.coeff i e = c * p.coeff j e
    rw [h]
  · intro h
    exact mul_left_cancel₀ hc h

/-- The contact numerators of a family and of any of its rescalings agree. -/
theorem contactNumerator_scale {m K N : ℕ} (c : ℂ) (hc : c ≠ 0)
    (p : FinitePuiseuxFamily m K N) (i j : Fin m) :
    p.contactNumerator i j = (scaleFinitePuiseuxFamily c hc p).contactNumerator i j :=
  contactNumerator_eq_of_sameCoefficientEqualityPattern
    (sameCoefficientEqualityPattern_scale c hc p) i j

end GaloisForLFunctions.IrregularStokes
