import GaloisForLFunctions.HTGeometry.DifferentialPolynomial
import GaloisForLFunctions.HTGeometry.PrimeValuationVeroneseDifferentialBasis

/-!
# Finite zeta valuation windows have no differential relations

The zeta Euler source has the constant unit coefficient in every prime-power valuation layer.
This module specializes the prime-valuation differential-basis theorem to that source.  Every
positive finite valuation window has one coordinate in each layer and has trivial differential
relation ideal over the intrinsic finite-prime rational coefficient field.

Consequently no nonzero differential polynomial involving only finitely many zeta valuation
layers can supply a reflection law over that base.  Any reflection mechanism not already present
in the coefficient field must therefore enter through a genuinely completed, infinite-support
operation rather than through a finite differential or prime-power window.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open scoped Differential

noncomputable section

/-- One coordinate in every layer of a finite zeta valuation window. -/
abbrev ZetaPrimeValuationFiniteIndex (d : ℕ) :=
  Σ _r : Fin d, Unit × Unit

/-- The constant unit coefficient column of the zeta Euler source. -/
def zetaPrimeValuationCoefficient (_r : Fin d) (_u : Unit)
    (_p : Nat.Primes) : ℂ :=
  1

/-- The unshifted valuation palette used by the zeta Euler logarithm. -/
def zetaPrimeValuationShift (_r : Fin d) (_u : Unit) : ℂ :=
  0

/-- The formal arithmetic coordinate in the positive prime-power layer `r + 1`. -/
def zetaPrimeValuationGhost (x : ZetaPrimeValuationFiniteIndex d) :
    arithmeticFunctionRationalCoordinateField :=
  primePowerCoefficientShiftCarrier x.1
    (zetaPrimeValuationCoefficient x.1 x.2.1)
    (zetaPrimeValuationShift x.1 x.2.2)

/-- The unit coefficient column has nonzero tail class, hence supplies exactly one independent
coordinate in every valuation layer. -/
theorem zetaPrimeValuationCoefficient_tailIndependent (r : Fin d) :
    TailCoefficientIndependent (zetaPrimeValuationCoefficient r) := by
  change TailCoefficientIndependent
    (fun _ : Unit => fun _p : Nat.Primes => (1 : ℂ))
  rw [tailCoefficientIndependent_unit_iff]
  unfold PrimeCoefficientTailZero
  simpa using (Set.infinite_univ : (Set.univ : Set Nat.Primes).Infinite)

/-- The one-point coefficient pattern in each zeta valuation layer has finite range. -/
theorem zetaPrimeValuationCoefficient_patternRangeFinite (r : Fin d) :
    (Set.range (coefficientPattern (zetaPrimeValuationCoefficient r))).Finite := by
  apply (Set.finite_singleton (fun _ : Unit => (1 : ℂ))).subset
  intro y hy
  obtain ⟨p, rfl⟩ := hy
  funext u
  cases u
  rfl

/-- **Finite zeta valuation freeness.**  Every positive finite collection of zeta prime-power
ghost layers is jointly differentially independent over the intrinsic finite-prime field. -/
theorem zetaPrimeValuationGhost_differentialIndependent
    {d : ℕ} (hd : 0 < d) :
    GaloisForLFunctions.DifferentialIndependent
      finitePrimeRationalCoefficientField
      (zetaPrimeValuationGhost (d := d)) := by
  letI : Nonempty (ZetaPrimeValuationFiniteIndex d) :=
    ⟨⟨⟨0, hd⟩, (), ()⟩⟩
  exact primePowerCoefficientShiftPalettes_differentialIndependent
    (d := d) (fun _r => Unit) (fun _r => Unit)
    zetaPrimeValuationCoefficient zetaPrimeValuationShift
    (fun _r _a _b _h => Subsingleton.elim _ _)
    zetaPrimeValuationCoefficient_patternRangeFinite
    zetaPrimeValuationCoefficient_tailIndependent

/-- **Finite-window reflection no-go.**  The complete differential relation ideal of every
positive finite zeta valuation window is trivial. -/
theorem zetaPrimeValuationGhost_relationIdeal_eq_bot
    {d : ℕ} (hd : 0 < d) :
    GaloisForLFunctions.differentialRelationIdeal
        (C := finitePrimeRationalCoefficientField)
        (zetaPrimeValuationGhost (d := d)) = ⊥ := by
  exact (GaloisForLFunctions.differentialIndependent_iff_relationIdeal_eq_bot
    (zetaPrimeValuationGhost (d := d))).mp
      (zetaPrimeValuationGhost_differentialIndependent hd)

/-- Evaluation on a positive finite zeta valuation window is faithful: a differential polynomial
vanishes on the window exactly when it is the zero polynomial. -/
theorem differentialPolynomialEval_zetaPrimeValuationGhost_eq_zero_iff
    {d : ℕ} (hd : 0 < d)
    (P : GaloisForLFunctions.DifferentialPolynomial
      (ZetaPrimeValuationFiniteIndex d) finitePrimeRationalCoefficientField) :
    GaloisForLFunctions.differentialPolynomialEval
        (C := finitePrimeRationalCoefficientField)
        (zetaPrimeValuationGhost (d := d)) P = 0 ↔ P = 0 := by
  rw [← GaloisForLFunctions.mem_differentialRelationIdeal_iff,
    zetaPrimeValuationGhost_relationIdeal_eq_bot hd]
  simp

end

end GaloisForLFunctions.HTGeometry
