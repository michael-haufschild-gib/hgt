import GaloisForLFunctions.RHTower.CCMRectangularDominantFold
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion

/-!
# Fixed-width rectangular Weil completeness

One fixed positive-width rectangular two-edge family is already complete for
RH when sampled at logarithmic apertures.  Under false RH its Weil values are
cofinally unbounded below; under RH every value is nonnegative.  Thus both
cofinal lower boundedness and pointwise nonnegativity of this single family
are equivalent to RH.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- If the right Xi divisor is nonempty, one fixed positive-width rectangular
window has Weil values below every real level along arbitrarily late
logarithmic apertures. -/
theorem xiWeilPolarization_rectangular_logSample_cofinally_unbounded_below
    {L : ℝ} (hL : 0 < L) (hne : Nonempty XiRightZeroCopy) :
    ∀ B : ℝ, ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      (xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re < B := by
  intro B N0
  let K : ℝ := rectangularTwoEdgeRemainderBound L *
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt
    (max (N0 : ℝ) (Real.exp (2 * L)))
  have hN0 : N0 ≤ N := by
    exact_mod_cast (le_max_left (N0 : ℝ) (Real.exp (2 * L))).trans hN.le
  have hNexp : Real.exp (2 * L) < (N : ℝ) :=
    (le_max_right (N0 : ℝ) (Real.exp (2 * L))).trans_lt hN
  obtain ⟨n, hnN, hcoeff⟩ :=
    xiRectangularRightDirichletCoefficientReal_cofinally_unbounded_below
      hL hne (B - K) N
  have hn0 : N0 ≤ n := hN0.trans hnN
  have hnexp : Real.exp (2 * L) < (n : ℝ) := by
    exact hNexp.trans_le (by exact_mod_cast hnN)
  have hnpos : 0 < (n : ℝ) := (Real.exp_pos _).trans hnexp
  have hnNatPos : 0 < n := by exact_mod_cast hnpos
  have hn1 : 1 ≤ n := hnNatPos
  have hlog : 2 * L < Real.log n :=
    (Real.lt_log_iff_exp_lt hnpos).2 hnexp
  have hLa : L ≤ Real.log n / 2 := by linarith
  refine ⟨n, hn0, hLa, ?_⟩
  have hrem := norm_xiWeilPolarization_rectangular_sub_dominant_le hLa
  rw [tsum_xiRectangularTwoEdgeDominant_logSample_eq_ofReal_rightCoefficient
    L hn1 hLa] at hrem
  have hre := Complex.re_le_norm
    (xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2)) -
      (xiRectangularRightDirichletCoefficientReal L n : ℂ))
  change
    (xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re -
      xiRectangularRightDirichletCoefficientReal L n ≤
      ‖xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2)) -
        (xiRectangularRightDirichletCoefficientReal L n : ℂ)‖ at hre
  dsimp only [K] at hcoeff ⊢
  linarith

/-- False RH forces cofinal negative divergence on the single fixed-width
rectangular Weil family. -/
theorem not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below
    {L : ℝ} (hL : 0 < L) (hRH : ¬RiemannHypothesis) :
    ∀ B : ℝ, ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      (xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re < B := by
  exact xiWeilPolarization_rectangular_logSample_cofinally_unbounded_below
    hL (nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH)

/-- For every fixed positive width, pointwise Weil positivity of the one
logarithmically sampled rectangular family is exactly RH. -/
theorem riemannHypothesis_iff_rectangular_logSample_weil_nonneg
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∀ n : ℕ, 0 ≤
        (xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re := by
  constructor
  · intro hRH n
    exact (riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH)
      (xiRectangularTwoEdgeTransform L (Real.log n / 2))
      (xiRectangularTwoEdgeTransform_squareSummable L (Real.log n / 2))
  · intro hnonneg
    by_contra hRH
    obtain ⟨n, hn0, hLa, hneg⟩ :=
      not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below
        hL hRH 0 0
    exact (not_lt_of_ge (hnonneg n)) hneg

/-- More strongly, mere eventual lower boundedness of the same fixed-width
family is exactly RH. -/
theorem riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        L ≤ Real.log n / 2 →
        B ≤ (xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re := by
  constructor
  · intro hRH
    refine ⟨0, 0, ?_⟩
    intro n hn hLa
    exact (riemannHypothesis_iff_rectangular_logSample_weil_nonneg hL).mp hRH n
  · rintro ⟨B, N0, hlower⟩
    by_contra hRH
    obtain ⟨n, hn, hLa, hbelow⟩ :=
      not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below
        hL hRH B N0
    exact (not_lt_of_ge (hlower n hn hLa)) hbelow

end

end RHTower
