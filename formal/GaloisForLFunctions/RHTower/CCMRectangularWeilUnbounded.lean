import GaloisForLFunctions.RHTower.CCMRectangularDominantFold

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- If the right Xi divisor is nonempty, one fixed positive-width rectangular
window has Weil squares below every real level along arbitrarily late
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
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
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
  have hn1 : 1 ≤ n := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro hnzero
      subst n
      norm_num at hnpos)
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

/-- Exact one-window criterion: RH is equivalent to nonnegativity on the
single fixed-width rectangular family at its logarithmic apertures. -/
theorem riemannHypothesis_iff_rectangular_logSample_nonneg
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∀ n : ℕ, L ≤ Real.log n / 2 →
        0 ≤ (xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re := by
  constructor
  · intro hRH n hn
    exact xiWeilPolarization_diagonal_nonneg_of_riemannHypothesis hRH _
      (xiRectangularTwoEdgeTransform_squareSummable L (Real.log n / 2))
  · intro hpos
    by_contra hRH
    obtain ⟨n, hn0, hLa, hneg⟩ :=
      not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below
        hL hRH 0 1
    exact (not_lt_of_ge (hpos n hLa)) hneg

/-- Equivalent bounded-below form of the same one-window criterion. -/
theorem riemannHypothesis_iff_rectangular_logSample_bounded_below
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∀ n : ℕ, L ≤ Real.log n / 2 →
        B ≤ (xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re := by
  constructor
  · intro hRH
    refine ⟨0, ?_⟩
    exact (riemannHypothesis_iff_rectangular_logSample_nonneg hL).mp hRH
  · rintro ⟨B, hbound⟩
    by_contra hRH
    obtain ⟨n, hn0, hLa, hlt⟩ :=
      not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below
        hL hRH B 1
    exact (not_lt_of_ge (hbound n hLa)) hlt

end

end RHTower
