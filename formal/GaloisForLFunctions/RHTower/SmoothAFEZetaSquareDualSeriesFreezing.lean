import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualWeightDerivativeBound
import GaloisForLFunctions.RHTower.Sieve.InghamExponentialMellinInversion

/-!
# Absolute freezing of exact square-dual divisor-series weights

For the `n`-th reflected zeta-square term the dual smoothing scale is `(n+1)x`.
The square-carrier variation bound contributes `(1+T)/((n+1)x)` on a dyadic height block.
Critical amplitude contributes `(n+1)^{-1/2}`, leaving the summable divisor majorant
`d(n+1)(n+1)^{-3/2}`.  No oscillatory Dirichlet phase is frozen or discarded.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

theorem summable_card_divisors_div_natSucc_rpow_three_halves :
    Summable (fun n : ℕ =>
      ((n + 1).divisors.card : ℝ) /
        (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
  have hL : LSeriesSummable
      (fun n : ℕ => (n.divisors.card : ℂ)) (3 / 2 : ℂ) :=
    Sieve.LSeriesSummable_card_divisors (w := (3 / 2 : ℂ)) (by norm_num)
  have hnorm : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m : ℕ => (m.divisors.card : ℂ))
        (3 / 2 : ℂ) n‖) := summable_norm_iff.mpr hL
  have hshift := (summable_nat_add_iff 1).mpr hnorm
  refine hshift.congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  simp only [Complex.norm_natCast]
  norm_num

private theorem norm_natSucc_cpow_linePt_sub_one_square
    (n : ℕ) (tau : ℝ) :
    ‖(n + 1 : ℂ) ^ (linePt tau - 1)‖ =
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hcast : (n + 1 : ℂ) = (((n + 1 : ℝ) : ℝ) : ℂ) := by
    norm_num
  rw [hcast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  congr 1
  simp [linePt]
  ring

/-- Finite absolute mass controlling square-dual carrier freezing. -/
def smoothAFEZetaSquareDivisorMajorant : ℝ :=
  ∑' n : ℕ, ((n + 1).divisors.card : ℝ) /
    (n + 1 : ℝ) ^ (3 / 2 : ℝ)

/-- Freezing the exact square-dual weights in the complete reflected divisor
series costs an absolutely summable divisor-weighted `3/2` power.  Critical
Dirichlet phases remain untouched. -/
theorem exists_norm_smoothAFEZetaSquareDualSeriesWeightError_le_dyadic :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {T x tau u : ℝ}, 4 ≤ T → 0 < x →
        tau ∈ Set.Icc T (2 * T) → u ∈ Set.Icc T (2 * T) →
        ‖∑' n : ℕ, ((n + 1).divisors.card : ℂ) *
            (n + 1 : ℂ) ^ (linePt tau - 1) *
            (smoothAFEZetaSquareDualWeight tau ((n + 1 : ℝ) * x) -
              smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * x))‖ ≤
          (A * (1 + 2 * T) / x) * |tau - u| *
            smoothAFEZetaSquareDivisorMajorant := by
  obtain ⟨A, hA, hweight⟩ :=
    exists_norm_smoothAFEZetaSquareDualWeight_sub_le_dyadic
  refine ⟨A, hA, ?_⟩
  intro T x tau u hT hx htau hu
  let f : ℕ → ℂ := fun n => ((n + 1).divisors.card : ℂ) *
    (n + 1 : ℂ) ^ (linePt tau - 1) *
    (smoothAFEZetaSquareDualWeight tau ((n + 1 : ℝ) * x) -
      smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * x))
  let q : ℕ → ℝ := fun n =>
    (A * (1 + 2 * T) / x) * |tau - u| *
      (((n + 1).divisors.card : ℝ) /
        (n + 1 : ℝ) ^ (3 / 2 : ℝ))
  have hbase := summable_card_divisors_div_natSucc_rpow_three_halves
  have hq : Summable q :=
    hbase.mul_left ((A * (1 + 2 * T) / x) * |tau - u|)
  have hpoint : ∀ n : ℕ, ‖f n‖ ≤ q n := by
    intro n
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    have hY : 0 < (n + 1 : ℝ) * x := mul_pos hnpos hx
    have hw := hweight hT hY htau hu
    have hpow := norm_natSucc_cpow_linePt_sub_one_square n tau
    dsimp only [f, q]
    rw [norm_mul, norm_mul, Complex.norm_natCast, hpow]
    calc
      ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          ‖smoothAFEZetaSquareDualWeight tau ((n + 1 : ℝ) * x) -
            smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * x)‖
        ≤ ((n + 1).divisors.card : ℝ) *
            (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((A * (1 + 2 * T) / ((n + 1 : ℝ) * x)) *
              |tau - u|) := by gcongr
      _ = (A * (1 + 2 * T) / x) * |tau - u| *
            (((n + 1).divisors.card : ℝ) /
              (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
          have hp : (n + 1 : ℝ) ^ (3 / 2 : ℝ) =
              (n + 1 : ℝ) ^ (1 / 2 : ℝ) * (n + 1 : ℝ) := by
            rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
              Real.rpow_add hnpos, Real.rpow_one]
          rw [Real.rpow_neg hnpos.le, hp]
          field_simp [hnpos.ne', hx.ne']
  have hf : Summable f := Summable.of_norm
    (hq.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint)
  calc
    ‖∑' n : ℕ, ((n + 1).divisors.card : ℂ) *
          (n + 1 : ℂ) ^ (linePt tau - 1) *
          (smoothAFEZetaSquareDualWeight tau ((n + 1 : ℝ) * x) -
            smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * x))‖
      = ‖∑' n : ℕ, f n‖ := by rfl
    _ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : ℕ, q n := hf.norm.tsum_le_tsum hpoint hq
    _ = (A * (1 + 2 * T) / x) * |tau - u| *
          smoothAFEZetaSquareDivisorMajorant := by
      rw [tsum_mul_left]
      rfl

end RHTower
