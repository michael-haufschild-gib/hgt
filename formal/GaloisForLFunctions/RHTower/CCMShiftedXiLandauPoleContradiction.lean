import GaloisForLFunctions.RHTower.CCMShiftedXiGlobalOrder
import GaloisForLFunctions.RHTower.CCMShiftedXiLandauContinuation

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- Positive continuation theorem: if the source-defined nonnegative-tail
L-series converges at `sigma > 1`, every right Xi pole lies on or left of that
analytic boundary. -/
theorem xiRightShiftedPole_re_le_of_landau_summable
    {L : ℝ} (hL : 0 < L) (C : ℝ) (N : ℕ) {delta sigma : ℝ}
    (hsigma : 1 < sigma) (hdelta0 : 0 ≤ delta)
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    (hsum : LSeriesSummable
      (fun n => ((xiRectangularLandauCoefficient L C N n : ℝ) : ℂ))
      (sigma : ℂ))
    (q : XiRightZeroCopy) :
    (xiRightShiftedPole q).re ≤ sigma := by
  by_contra hnot
  have hpole : sigma < (xiRightShiftedPole q).re := lt_of_not_ge hnot
  let U : Set ℂ := {s : ℂ | sigma < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hpoleU : xiRightShiftedPole q ∈ U := hpole
  have heqOn := xiRectangularCancelledSeries_eq_xi_mul_landauContinuation
    L C N hsigma hdelta0 hupper hsum
  have hevent : xiRectangularCancelledSeries L =ᶠ[nhds (xiRightShiftedPole q)]
      fun s => xi (s - 1 / 2) *
        xiRectangularLandauAnalyticShiftedSeries L C N s := by
    filter_upwards [hU.mem_nhds hpoleU] with s hs
    exact heqOn hs
  have horders := analyticOrderAt_congr hevent
  have hlandauDiff := differentiableOn_xiRectangularLandauAnalyticShiftedSeries
    L C N hsigma hsum
  have hlandauAn : AnalyticAt ℂ
      (xiRectangularLandauAnalyticShiftedSeries L C N)
      (xiRightShiftedPole q) :=
    (hlandauDiff.analyticOnNhd hU) _ hpoleU
  have hxiAn : AnalyticAt ℂ (fun s : ℂ => xi (s - 1 / 2))
      (xiRightShiftedPole q) := by
    exact (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp
      (analyticAt_id.sub analyticAt_const)
  have hprod : (xiRightMultiplicity q : ℕ∞) ≤
      analyticOrderAt
        (fun s => xi (s - 1 / 2) *
          xiRectangularLandauAnalyticShiftedSeries L C N s)
        (xiRightShiftedPole q) := by
    rw [show (fun s => xi (s - 1 / 2) *
        xiRectangularLandauAnalyticShiftedSeries L C N s) =
      (fun s => xi (s - 1 / 2)) *
        xiRectangularLandauAnalyticShiftedSeries L C N by rfl,
      analyticOrderAt_mul hxiAn hlandauAn,
      xi_shifted_half_order]
    exact le_add_right le_rfl
  rw [xiRectangularCancelledSeries_order hL q] at horders
  rw [← horders] at hprod
  have hm : 0 < xiRightMultiplicity q := xiRightMultiplicity_pos q
  have hltNat : xiRightMultiplicity q - 1 < xiRightMultiplicity q :=
    Nat.sub_one_lt (Nat.ne_of_gt hm)
  have hlt : (xiRightMultiplicity q - 1 : ℕ∞) <
      (xiRightMultiplicity q : ℕ∞) := by exact_mod_cast hltNat
  exact (not_lt_of_ge hprod) hlt

/-- A positive lower bound on the Landau analytic boundary would bound the
entire right Xi divisor strictly below its own transverse supremum. -/
theorem no_eventual_lower_bound_xiRectangularRightDirichletCoefficientReal
    {L : ℝ} (hL : 0 < L) (hne : Nonempty XiRightZeroCopy) :
    ¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      0 ≤ xiRectangularRightDirichletCoefficientReal L n + C := by
  rintro ⟨C, N, hlower⟩
  obtain ⟨sigma, hsigma, hsigmaSup, hsum⟩ :=
    exists_xiRectangularLandauCoefficient_summable_left_of_boundary
      L C N hne hlower
  have hpoleBound : ∀ q : XiRightZeroCopy,
      (xiRightShiftedPole q).re ≤ sigma :=
    xiRightShiftedPole_re_le_of_landau_summable hL C N hsigma
      (xiRightTransverseSup_pos hne).le
      (fun q => xiRightCenteredZero_re_le_sup q) hsum
  have hcenterBound : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ sigma - 1 := by
    intro q
    have hq := hpoleBound q
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re] at hq
    linarith
  have hsupBound : xiRightTransverseSup ≤ sigma - 1 := by
    apply csSup_le (Set.range_nonempty _)
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    exact hcenterBound q
  linarith

/-- Positive dual of the pole-cancellation no-go: if a right Xi zero exists,
the logarithmically sampled rectangular coefficients fall below every real
level cofinally. -/
theorem xiRectangularRightDirichletCoefficientReal_cofinally_unbounded_below
    {L : ℝ} (hL : 0 < L) (hne : Nonempty XiRightZeroCopy) :
    ∀ B : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      xiRectangularRightDirichletCoefficientReal L n < B := by
  intro B N
  by_contra hnot
  push Not at hnot
  apply no_eventual_lower_bound_xiRectangularRightDirichletCoefficientReal hL hne
  refine ⟨-B, N, ?_⟩
  intro n hn
  have hBn := hnot n hn
  linarith

end

end RHTower
