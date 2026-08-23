import GaloisForLFunctions.RHTower.CCMRectangularNegativePartSquareEnergyGate
import Mathlib.Data.PNat.Basic

/-!
# Square-summable coefficients and ordinary Dirichlet series

This file supplies the coefficient-space bridge needed by prime-window Hardy exclusions.
An unweighted square-summable complex coefficient sequence has an absolutely convergent ordinary
Dirichlet series at every `Re s > 1/2`, hence a holomorphic L-series on that half-plane.  Positive
indices are represented literally by `ℕ+`; the finite index-zero term is restored exactly.
-/

open Complex Filter LSeries

noncomputable section

namespace RHTower

/-- Square summability on positive indices is equivalent to square summability after restoring the
single index-zero term.  This direction is the one used by ordinary Dirichlet series. -/
theorem summable_norm_sq_nat_of_positive
    {a : ℕ → ℂ} (ha : Summable (fun n : ℕ+ => ‖a n‖ ^ 2)) :
    Summable (fun n : ℕ => ‖a n‖ ^ 2) := by
  have hshift : Summable (fun n : ℕ => ‖a n.succPNat‖ ^ 2) :=
    Equiv.pnatEquivNat.symm.summable_iff.mpr ha
  apply (summable_nat_add_iff 1).mp
  simpa [Nat.succPNat_coe, Nat.add_comm] using hshift

/-- Complex Cauchy--Schwarz for ordinary Dirichlet series: an unweighted square-summable
coefficient sequence converges absolutely at every real abscissa strictly above `1/2`. -/
theorem LSeriesSummable_of_squareSummable
    {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖ ^ 2))
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    LSeriesSummable a (sigma : ℂ) := by
  have hweighted : Summable
      (realDirichletWeightedTerm (fun n => ‖a n‖ ^ 2) 0) := by
    apply ha.congr_atTop
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    simp [realDirichletWeightedTerm, hn0]
  have hnorm : LSeriesSummable (fun n => ((‖a n‖ : ℝ) : ℂ)) (sigma : ℂ) :=
    LSeriesSummable_of_squareWeightedTerm_summable_at_lowerExponent
      (fun n => norm_nonneg (a n)) (by linarith) hweighted
  change Summable
    (LSeries.term (fun n => ((‖a n‖ : ℝ) : ℂ)) (sigma : ℂ)) at hnorm
  change Summable (LSeries.term a (sigma : ℂ))
  refine Summable.of_norm_bounded (f := LSeries.term a (sigma : ℂ))
    (g := fun n =>
      ‖LSeries.term (fun n => ((‖a n‖ : ℝ) : ℂ)) (sigma : ℂ) n‖)
    hnorm.norm ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [LSeries.term_zero]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    simp [LSeries.term_of_ne_zero hn0]

/-- Positive-index form of `LSeriesSummable_of_squareSummable`. -/
theorem LSeriesSummable_of_positive_squareSummable
    {a : ℕ → ℂ} (ha : Summable (fun n : ℕ+ => ‖a n‖ ^ 2))
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    LSeriesSummable a (sigma : ℂ) :=
  LSeriesSummable_of_squareSummable (summable_norm_sq_nat_of_positive ha) hsigma

/-- A convergent ordinary L-series is holomorphic on its open half-plane of convergence. -/
theorem differentiableOn_LSeries_rightHalf_of_summable
    {a : ℕ → ℂ} {sigma : ℝ}
    (hsum : LSeriesSummable a (sigma : ℂ)) :
    DifferentiableOn ℂ (LSeries a) {s : ℂ | sigma < s.re} := by
  intro s hs
  change sigma < s.re at hs
  have habs := hsum.abscissaOfAbsConv_le
  have habslt : LSeries.abscissaOfAbsConv a < s.re :=
    lt_of_le_of_lt habs (by exact_mod_cast hs)
  exact (LSeries_hasDerivAt habslt).differentiableAt.differentiableWithinAt

/-- A square-summable ordinary coefficient sequence has a holomorphic L-series on
`Re s > 1/2`. -/
theorem differentiableOn_LSeries_rightHalf_of_squareSummable
    {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖ ^ 2)) :
    DifferentiableOn ℂ (LSeries a) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  change 1 / 2 < s.re at hs
  let sigma : ℝ := (s.re + 1 / 2) / 2
  have hsigma : 1 / 2 < sigma := by
    dsimp only [sigma]
    linarith
  have hsigmaS : sigma < s.re := by
    dsimp only [sigma]
    linarith
  have hsum := LSeriesSummable_of_squareSummable ha hsigma
  have habs := hsum.abscissaOfAbsConv_le
  have habslt : LSeries.abscissaOfAbsConv a < s.re :=
    lt_of_le_of_lt habs (by exact_mod_cast hsigmaS)
  exact (LSeries_hasDerivAt habslt).differentiableAt.differentiableWithinAt

/-- Positive-index form of the square-summable Dirichlet--Hardy holomorphy theorem. -/
theorem differentiableOn_LSeries_rightHalf_of_positive_squareSummable
    {a : ℕ → ℂ} (ha : Summable (fun n : ℕ+ => ‖a n‖ ^ 2)) :
    DifferentiableOn ℂ (LSeries a) {s : ℂ | 1 / 2 < s.re} :=
  differentiableOn_LSeries_rightHalf_of_squareSummable
    (summable_norm_sq_nat_of_positive ha)

end RHTower
