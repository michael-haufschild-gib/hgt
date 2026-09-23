import GaloisForLFunctions.HTGeometry.WeightPolynomialDependence
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryMagnitudeHypertranscendence

/-!
# Leading-symbol degeneracy versus magnitude survival

The class `(degree, order) = (4, 4)` contains a nonzero differential polynomial whose balanced
falling-factorial leading symbol vanishes identically.  Nevertheless it cannot annihilate any
entire function with eventually log-superlacunary Taylor magnitudes.  Minimal-valuation dominance
therefore detects relations that the balanced leading-symbol test provably cannot see.
-/

open Filter MvPolynomial PowerSeries Polynomial

namespace GaloisForLFunctions

noncomputable section

/-- The degenerate class-`(4,4)` balanced leading symbol. -/
def class44DegenerateWeightSymbol : Polynomial ℚ :=
  weightPolynomial (![3, 1, 0, 0] : Fin 4 → ℕ) -
    2 * weightPolynomial (![2, 2, 0, 0] : Fin 4 → ℕ) +
      weightPolynomial (![2, 1, 1, 0] : Fin 4 → ℕ)

/-- The corresponding nonzero differential polynomial in the value and first three derivative
slots. -/
def class44DegenerateDifferentialPolynomial : MvPolynomial (Fin 5) ℂ :=
  X 4 * X 2 * X 1 ^ (2 : ℕ) -
    MvPolynomial.C 2 * X 3 ^ (2 : ℕ) * X 1 ^ (2 : ℕ) +
      X 3 * X 2 ^ (2 : ℕ) * X 1

/-- Its balanced leading symbol vanishes exactly. -/
theorem class44DegenerateWeightSymbol_eq_zero :
    class44DegenerateWeightSymbol = 0 := by
  exact weightPolynomial_class44_dependence

/-- The differential polynomial itself is nonzero despite its vanishing balanced symbol. -/
theorem class44DegenerateDifferentialPolynomial_ne_zero :
    class44DegenerateDifferentialPolynomial ≠ 0 := by
  intro hzero
  let g : Fin 5 → ℂ := fun i => if i = 3 then 0 else 1
  have heval := congrArg (MvPolynomial.eval g) hzero
  have h13 : (1 : Fin 5) ≠ 3 := by decide
  have h23 : (2 : Fin 5) ≠ 3 := by decide
  have h43 : (4 : Fin 5) ≠ 3 := by decide
  simp [class44DegenerateDifferentialPolynomial, g, h13, h23, h43] at heval

/-- **Leading-symbol blindness/magnitude-survival law.**  The same explicit class-`(4,4)` relation
has zero balanced leading symbol but fails to annihilate every entire function with eventually
positive log-superlacunary Taylor magnitudes.  Hence balanced-symbol nondegeneracy is sufficient but
not necessary for magnitude survival. -/
theorem class44_leadingSymbolDegeneracy_magnitudeSurvivalUniversality
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) {b : ℕ → ℝ}
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hbpos : ∀ᶠ i in atTop, 0 < b i)
    (hratio : Tendsto (fun i => b (i + 1) / b i) atTop atTop) :
    class44DegenerateWeightSymbol = 0 ∧
      ¬ ∀ z : ℂ,
        MvPolynomial.eval
          (Fin.cons z (fun j : Fin 4 => iteratedDeriv (j : ℕ) f z))
          class44DegenerateDifferentialPolynomial = 0 := by
  refine ⟨class44DegenerateWeightSymbol_eq_zero, ?_⟩
  intro hannihilates
  have hht := hypertranscendental_of_eventually_logSuperlacunary hf hb hbpos hratio
  exact hht ⟨3, class44DegenerateDifferentialPolynomial,
    class44DegenerateDifferentialPolynomial_ne_zero, hannihilates⟩

end

end GaloisForLFunctions
