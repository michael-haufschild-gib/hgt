import GaloisForLFunctions.RHTower.JointAncestryLevelOneCapstones
import GaloisForLFunctions.RHTower.AsymptoticAbscissaLawProducers
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw

/-!
# Level-one positivity and the abscissa laws

Positivity on the characters of all sufficiently large primes at level one implies RH by
the diagonal Bochner bound. Thus it gives the asymptotic abscissa law and the implication
from a strict half-plane to RH. The alternative RH or zero abscissa one follows in its
stronger first branch: no edge exception is needed.
-/

namespace GaloisForLFunctions.SelectiveArithmetic

open RHTower

/-- Level-one large-prime positivity gives AAL, the strict-half-plane implication, and the
RH-or-edge alternative; in fact its zero abscissa is exactly one half. -/
theorem levelOne_abscissa_laws :
    (∃ X : ℕ, JasDressedPSDAbove X 1) →
      AsymptoticAbscissaLaw ∧
      (zetaZeroAbscissa < 1 → RiemannHypothesis) ∧
      (RiemannHypothesis ∨ zetaZeroAbscissa = 1) ∧
      zetaZeroAbscissa = 1 / 2 := by
  intro h
  have hRH := riemannHypothesis_iff_exists_jasDressedPSDAbove_one.mpr h
  exact ⟨asymptoticAbscissaLaw_of_riemannHypothesis hRH, fun _ => hRH, Or.inl hRH,
    zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr hRH⟩

#print axioms levelOne_abscissa_laws

end GaloisForLFunctions.SelectiveArithmetic
