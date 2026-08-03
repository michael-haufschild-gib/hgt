import GaloisForLFunctions.HTGeometry.BarnesFieldLadderOrderOne
import GaloisForLFunctions.HTGeometry.DiffTranslateOperatorAction

/-!
# The atomic theorem for the Barnes order-one source

The corrected order-one Barnes source solves the ladder equation with defect exactly the simple pole
`1/(z + ω_j)`, so the atomic theorem applies to it verbatim: its translates through shifts pairwise
distinct modulo `ω_j ℤ` are differentially algebraically independent over the coordinate field, and
a nonzero constant-coefficient differential-translation operator avoiding the direction `j` sends it
outside the differentially algebraic sector.

This is the card's atomic scaled-digamma theorem, attached to the genuine Barnes source rather than
to an abstract laddered element.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic zeroNomeScalarTower

variable {ι : Type} [Fintype ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
theorem barnes_period_ne_zero {ω : ι → ℂ} (hω : ∀ i, 0 < (ω i).im) (j : ι) : ω j ≠ 0 := by
  intro hcon
  have hj := hω j
  rw [hcon] at hj
  simp at hj

/-- **The atomic theorem for the Barnes order-one source.**  Translates through shifts pairwise
distinct modulo `ω_j ℤ` are differentially algebraically independent over the coordinate field. -/
theorem differentialIndependent_barnesLadderTranslate [DecidableEq ι]
    (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (hcard : Fintype.card ι = 1) (j : ι)
    {r : ℕ} (h : Fin r → ℂ)
    (hincong : ∀ i i' : Fin r, i ≠ i' → ∀ n : ℤ, h i - h i' ≠ (n : ℂ) * ω j) :
    DifferentialIndependent (RatFunc ℂ)
      fun i => addTranslationMeroEquiv (h i) (barnesLadderSolutionOne ω hω j) :=
  differentialIndependent_ladderTranslate (barnes_period_ne_zero hω j) (ω j) _
    (addTranslationMeroEquiv_barnesLadderSolutionOne ω hω hcard j) h hincong

/-- **The reverse-inclusion step for the Barnes order-one source.**  A nonzero constant-coefficient
differential-translation operator avoiding the direction `j` is hypertranscendental on it. -/
theorem hypertranscendentalOver_diffTranslateApply_barnesLadderSolutionOne [DecidableEq ι]
    {N : ℕ} (ωv : Fin N → ℂ)
    (hindep : ∀ n : Fin N → ℤ, ∑ k, (n k : ℂ) * ωv k = 0 → ∀ k, n k = 0)
    (jv : Fin N) (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (hcard : Fintype.card ι = 1) (j : ι)
    (hmatch : ωv jv = ω j)
    (P : MvPolynomial (Fin N) (Polynomial ℂ)) (hP : P ≠ 0)
    (havoid : ∀ n ∈ P.support, n jv = 0) :
    HypertranscendentalOver (RatFunc ℂ)
      (diffTranslateApply ωv P (barnesLadderSolutionOne ω hω j)) := by
  refine hypertranscendentalOver_diffTranslateApply_of_avoid ωv hindep jv (ω j) _ ?_ P hP havoid
  rw [hmatch]
  exact addTranslationMeroEquiv_barnesLadderSolutionOne ω hω hcard j

end

end GaloisForLFunctions.HTGeometry
