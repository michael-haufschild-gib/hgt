import GaloisForLFunctions.RHTower.Sieve.MoebiusContourKappaTwo

/-!
# The saving at the width-`log^{-2}` rectangle

The left-edge term of the contour bound is `(N+H)^{c(K)}` with `c(K) = 1 - log^{-2}K`.  Written as
a saving,

    (N+H)^{c(K)} = (N+H) · exp( -log(N+H) / log²K ),

the term is the trivial size `N+H` times a genuine decay as soon as `log(N+H)/log²K` grows.  The
exponent-nine rectangle produced `exp(-c₉ log(N+H)/(16 log⁹K))` here; the whole difference between
the two contours is the power of `log K` in that denominator, and it is that power which fixes the
saving an optimisation over `K` can report.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

/-- The left-edge power, written as the trivial size times an explicit saving. -/
theorem rpow_leftAbscissaTwo {K : ℕ} {x : ℝ} (hx : 0 < x) :
    x ^ leftAbscissaTwo K = x * Real.exp (-(1 / (Real.log K) ^ 2) * Real.log x) := by
  rw [leftAbscissaTwo, Real.rpow_def_of_pos hx,
    show Real.log x * (1 - 1 / (Real.log K) ^ 2)
      = Real.log x + (-(1 / (Real.log K) ^ 2) * Real.log x) by ring,
    Real.exp_add, Real.exp_log hx]

/-- The width of the rectangle. -/
theorem rightAbscissaTwo_sub_leftAbscissaTwo (K : ℕ) :
    rightAbscissaTwo K - leftAbscissaTwo K = 2 / (Real.log K) ^ 2 := by
  rw [rightAbscissaTwo, leftAbscissaTwo]
  ring

/-- **The contour bound with the saving exposed.**  The left-edge term is the trivial size `N+H`
times `exp(-log(N+H)/log²K)`, and the horizontal edges carry the rectangle width `2 log^{-2}K`
explicitly. -/
theorem exists_norm_tsum_moebius_smoothWeight_le_saving_two {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    (j : ℕ) :
    ∃ (C C' Ms : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ Ms ∧ ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (invZetaRightBoundTwo K * (C * (N + H + 1) ^ rightAbscissaTwo K)) / truncHeight K
            + Ms * Real.log K ^ 2 * (C' * (N + H + 1) ^ rightAbscissaTwo K)
                / (truncHeight K) ^ (j + 1) * (2 / Real.log K ^ 2)
            + Ms * Real.log K ^ 2 * (C' * (N + H + 1) ^ rightAbscissaTwo K)
                / (truncHeight K) ^ (j + 1) * (2 / Real.log K ^ 2)
            + Ms * Real.log K ^ 2
                * (4 * ((N + H) * Real.exp (-(1 / Real.log K ^ 2) * Real.log (N + H)))
                    + 2 * (C * ((N + H + 1)
                        * Real.exp (-(1 / Real.log K ^ 2) * Real.log (N + H + 1))))) := by
  obtain ⟨C, C', Ms, K₁, hC, hC', hMs, hmain⟩ :=
    exists_norm_tsum_moebius_smoothWeight_le_kappa_two hN hH j
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.1 (hlog.eventually_ge_atTop 2)
  refine ⟨C, C', Ms, max K₁ K₂, hC, hC', hMs, fun K hKle => ?_⟩
  have hbase := hmain K (le_trans (le_max_left _ _) hKle)
  have hlogK : (2 : ℝ) ≤ Real.log K := hK₂ K (le_trans (le_max_right _ _) hKle)
  have hNH : (0 : ℝ) < N + H := by linarith
  have hNH1 : (0 : ℝ) < N + H + 1 := by linarith
  have hLsq : (4 : ℝ) ≤ Real.log K ^ 2 := by nlinarith
  have hinv : 1 / Real.log K ^ 2 ≤ 1 / 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLsq
  have hc0 : (0 : ℝ) < leftAbscissaTwo K := by rw [leftAbscissaTwo]; linarith
  have hcge : (3 : ℝ) / 4 ≤ leftAbscissaTwo K := by rw [leftAbscissaTwo]; linarith
  rw [rightAbscissaTwo_sub_leftAbscissaTwo, rpow_leftAbscissaTwo hNH,
    rpow_leftAbscissaTwo hNH1] at hbase
  set X : ℝ := (N + H) * Real.exp (-(1 / Real.log K ^ 2) * Real.log (N + H)) with hXdef
  set Y : ℝ := (N + H + 1) * Real.exp (-(1 / Real.log K ^ 2) * Real.log (N + H + 1)) with hYdef
  have hX0 : (0 : ℝ) ≤ X := by rw [hXdef]; positivity
  have hdiv : X / leftAbscissaTwo K ≤ 2 * X := by
    rw [div_le_iff₀ hc0]
    nlinarith [hX0, hcge]
  have hfac : (0 : ℝ) ≤ Ms * Real.log K ^ 2 := by positivity
  have hinner : 2 * (X / leftAbscissaTwo K) + 2 * (C * Y) ≤ 4 * X + 2 * (C * Y) := by
    linarith
  have hstep := mul_le_mul_of_nonneg_left hinner hfac
  linarith [hbase, hstep]

end RHTower.Sieve
