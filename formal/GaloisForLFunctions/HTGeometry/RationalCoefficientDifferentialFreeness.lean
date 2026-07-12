import GaloisForLFunctions.HTGeometry.PolynomialCoefficientDifferentialFreeness
import GaloisForLFunctions.HTGeometry.RationalCoefficientClearing
import GaloisForLFunctions.HTGeometry.CountableShiftPalette

/-!
# Rational-coefficient differential freeness on countable shift palettes

A rational-function coefficient relation is represented canonically by its cleared
`C[z]`-coefficient relation.  Exact simultaneous denominator clearing preserves nonzeroness.
Consequently every countable-shift polynomial-differentially free prime-log source is also free of
all rational-coefficient relations in the cleared functional sense.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A rational-coefficient differential relation holds when its canonical nonzero-denominator
clearing vanishes on the common upper domain.  This is the pole-free functional form of a
meromorphic `C(z)`-coefficient identity. -/
def RationalCoefficientDifferentialRelationHolds
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ)
    (shiftCode : Fin m → Γ) (orders : Fin m → ℕ)
    (u : PrimeLogBoundedGauge)
    (Q : MvPolynomial (Σ i, Fin (orders i)) (RatFunc ℂ)) : Prop :=
  PolynomialCoefficientDifferentialRelationHolds
    shiftValue shiftCode orders u (clearRatFuncCoefficients Q)

/-- **Rational-coefficient finite-translate freeness.** A polynomial-pattern-free prime-log source
admits no nonzero canonically cleared `C(z)`-coefficient differential relation on any finite
injective shift packet. -/
theorem rationalCoefficientDifferentialRelation_eq_zero
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ)
    (shiftCode : Fin m → Γ) (hshiftCode : Function.Injective shiftCode)
    (orders : Fin m → ℕ) (u : PrimeLogBoundedGauge)
    (hfree : CountableShiftPolynomialDifferentialFree shiftValue u)
    (Q : MvPolynomial (Σ i, Fin (orders i)) (RatFunc ℂ))
    (hrelation : RationalCoefficientDifferentialRelationHolds
      shiftValue shiftCode orders u Q) :
    Q = 0 := by
  have hclear := polynomialCoefficientDifferentialRelation_eq_zero
    shiftValue shiftCode hshiftCode orders u hfree
    (clearRatFuncCoefficients Q) hrelation
  by_contra hQ
  exact clearRatFuncCoefficients_ne_zero Q hQ hclear

/-- Rational-coefficient functional differential freeness on every finite rectangle cut from a
shift palette. -/
def CountableShiftRationalDifferentialFree
    {Γ : Type*} (shiftValue : Γ → ℂ) (u : PrimeLogBoundedGauge) : Prop :=
  ∀ (m : ℕ) (shiftCode : Fin m → Γ), Function.Injective shiftCode →
    ∀ (orders : Fin m → ℕ)
      (Q : MvPolynomial (Σ i, Fin (orders i)) (RatFunc ℂ)),
      RationalCoefficientDifferentialRelationHolds
        shiftValue shiftCode orders u Q → Q = 0

theorem countableShiftRationalDifferentialFree_of_polynomialFree
    {Γ : Type*} (shiftValue : Γ → ℂ) (u : PrimeLogBoundedGauge)
    (hfree : CountableShiftPolynomialDifferentialFree shiftValue u) :
    CountableShiftRationalDifferentialFree shiftValue u := by
  intro m shiftCode hshiftCode orders Q hrelation
  exact rationalCoefficientDifferentialRelation_eq_zero
    shiftValue shiftCode hshiftCode orders u hfree Q hrelation

/-- Rational-coefficient functional differential freeness is dense residual for every countable
injective shift palette. -/
theorem countableShiftRationalDifferentialFree_dense_residual
    {Γ : Type*} [Countable Γ] (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue) :
    Dense {u : PrimeLogBoundedGauge |
      CountableShiftRationalDifferentialFree shiftValue u} ∧
    {u : PrimeLogBoundedGauge |
      CountableShiftRationalDifferentialFree shiftValue u} ∈
        residual PrimeLogBoundedGauge := by
  let P : Set PrimeLogBoundedGauge := {u |
    CountableShiftPolynomialDifferentialFree shiftValue u}
  let R : Set PrimeLogBoundedGauge := {u |
    CountableShiftRationalDifferentialFree shiftValue u}
  have hPR : P ⊆ R := by
    intro u hu
    exact countableShiftRationalDifferentialFree_of_polynomialFree shiftValue u hu
  have hP := countableShiftPolynomialDifferentialFree_dense_residual
    shiftValue hshiftValue
  exact ⟨hP.1.mono hPR, Filter.mem_of_superset hP.2 hPR⟩

theorem exists_countableShiftRationalDifferentialFree
    {Γ : Type*} [Countable Γ] (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue) :
    ∃ u : PrimeLogBoundedGauge,
      CountableShiftRationalDifferentialFree shiftValue u :=
  (countableShiftRationalDifferentialFree_dense_residual
    shiftValue hshiftValue).1.nonempty

/-- The exact facet-sewn palette `Q(i)+∑_v Z ω_v` admits a bounded prime-log source free of
every canonically cleared rational-coefficient finite differential relation. -/
theorem exists_rationalLatticeShift_rationalDifferentialFree
    {V : Type*} [Fintype V] (omega : V → ℝ) :
    ∃ u : PrimeLogBoundedGauge,
      CountableShiftRationalDifferentialFree
        ((↑) : rationalLatticeShiftSet omega → ℂ) u :=
  exists_countableShiftRationalDifferentialFree
    ((↑) : rationalLatticeShiftSet omega → ℂ) Subtype.val_injective

end GaloisForLFunctions.HTGeometry
