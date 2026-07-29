import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.RCLike.Sqrt

/-!
# Even entire functions descend through the square map

An even entire complex function `f` has a canonical entire square factor `Q` satisfying
`Q (z ^ 2) = f z`.  The construction keeps the even coefficients of one infinite-radius Cauchy
series and halves their indices.  It therefore avoids choosing a discontinuous global square-root
branch.  This is the analytic descent needed by squared-coordinate Jensen arguments.
-/

open Complex Filter Set
open scoped ENNReal NNReal Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cauchy series at zero used for even square descent. -/
def evenEntireBaseSeries (f : ℂ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  cauchyPowerSeries f 0 (1 : NNReal)

/-- Keep only the even coefficients and halve their indices. -/
def evenEntireSquareFactorSeries (f : ℂ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => (evenEntireBaseSeries f).coeff (2 * n))

/-- Canonical square factor of a prospective even entire function. -/
def evenEntireSquareFactor (f : ℂ → ℂ) : ℂ → ℂ :=
  (evenEntireSquareFactorSeries f).sum

/-- The principal complex square root is a right inverse to squaring. -/
theorem complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  by_cases hz : z = 0
  · simp [hz]
  · calc
      Complex.sqrt z ^ 2 = Complex.exp (Complex.log z / 2) ^ 2 := by
        rw [sqrt_eq_exp hz]
      _ = Complex.exp (Complex.log z) := by
        rw [pow_two, ← Complex.exp_add]
        congr 1
        ring
      _ = z := Complex.exp_log hz

/-- Every odd origin jet of an even function vanishes. -/
theorem iteratedDeriv_zero_of_even_of_odd
    {f : ℂ → ℂ} (heven : Function.Even f) {n : ℕ} (hn : Odd n) :
    iteratedDeriv n f 0 = 0 := by
  have hfun : (fun z : ℂ => f (-z)) = f := funext heven
  have hcomp := iteratedDeriv_comp_neg n f 0
  rw [hfun, neg_zero, hn.neg_one_pow] at hcomp
  simp only [neg_one_smul] at hcomp
  have hsum : iteratedDeriv n f 0 + iteratedDeriv n f 0 = 0 :=
    eq_neg_iff_add_eq_zero.mp hcomp
  have htwo : (2 : ℂ) * iteratedDeriv n f 0 = 0 := by
    simpa only [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Odd Cauchy coefficients vanish for an even entire function. -/
theorem evenEntireBaseSeries_coeff_eq_zero_of_odd
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (heven : Function.Even f)
    {n : ℕ} (hn : Odd n) :
    (evenEntireBaseSeries f).coeff n = 0 := by
  have hp := hf.hasFPowerSeriesOnBall 0 (R := (1 : NNReal)) (by norm_num)
  have hfac := hp.factorial_smul 1 n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul,
    iteratedDeriv_zero_of_even_of_odd heven hn] at hfac
  have hnfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast n.factorial_ne_zero
  simpa only [evenEntireBaseSeries, FormalMultilinearSeries.coeff,
    nsmul_eq_mul, mul_eq_zero, hnfac, false_or] using hfac

theorem evenEntireBaseSeries_radius_eq_top
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    (evenEntireBaseSeries f).radius = ⊤ := by
  have hp := hf.hasFPowerSeriesOnBall 0 (R := (1 : NNReal)) (by norm_num)
  exact top_unique hp.r_le

/-- Halving the indices of the even coefficients preserves infinite convergence radius. -/
theorem evenEntireSquareFactorSeries_radius_eq_top
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    (evenEntireSquareFactorSeries f).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hp := (FormalMultilinearSeries.radius_eq_top_iff_summable_norm
    (evenEntireBaseSeries f)).mp
      (evenEntireBaseSeries_radius_eq_top hf) (NNReal.sqrt r)
  have hdouble : Function.Injective (fun n : ℕ => 2 * n) := by
    intro m n h
    exact Nat.mul_left_cancel (by omega) h
  have hsub := hp.comp_injective hdouble
  apply hsub.congr
  intro n
  rw [Function.comp_apply, evenEntireSquareFactorSeries,
    FormalMultilinearSeries.ofScalars_norm,
    FormalMultilinearSeries.norm_apply_eq_norm_coef]
  push_cast
  rw [pow_mul, Real.sq_sqrt (by positivity)]

/-- The square factor is entire whenever the original function is entire. -/
theorem differentiable_evenEntireSquareFactor
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (evenEntireSquareFactor f) := by
  let p := evenEntireSquareFactorSeries f
  have hr : p.radius = ⊤ := evenEntireSquareFactorSeries_radius_eq_top hf
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have ha : AnalyticOnNhd ℂ p.sum Set.univ := by
    simpa [hr] using hp.analyticOnNhd
  rw [← differentiableOn_univ]
  simpa only [evenEntireSquareFactor, p] using ha.differentiableOn

/-- **Even-entire square descent.**  The canonical factor recovers the original function after
composition with the square map. -/
theorem evenEntireSquareFactor_sq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (heven : Function.Even f) (z : ℂ) :
    evenEntireSquareFactor f (z ^ 2) = f z := by
  let p := evenEntireBaseSeries f
  have hp : HasFPowerSeriesOnBall f p 0 ⊤ := by
    simpa only [p, evenEntireBaseSeries] using
      hf.hasFPowerSeriesOnBall 0 (R := (1 : NNReal)) (by norm_num)
  have hsum : HasSum (fun n : ℕ => p.coeff n * z ^ n) (f z) := by
    have h := hp.hasSum (y := z) (by simp)
    simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      smul_eq_mul, mul_comm] using h
  have hdouble : Function.Injective (fun n : ℕ => 2 * n) := by
    intro m n h
    exact Nat.mul_left_cancel (by omega) h
  have hdoubleOne : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro m n h
    exact Nat.mul_left_cancel (by omega) (Nat.add_right_cancel h)
  have he : Summable (fun n : ℕ => p.coeff (2 * n) * z ^ (2 * n)) := by
    rw [show (fun n : ℕ => p.coeff (2 * n) * z ^ (2 * n)) =
        (fun n => p.coeff n * z ^ n) ∘ fun n => 2 * n by
      funext n
      rfl]
    exact hsum.summable.comp_injective hdouble
  have ho : Summable (fun n : ℕ => p.coeff (2 * n + 1) * z ^ (2 * n + 1)) := by
    rw [show (fun n : ℕ => p.coeff (2 * n + 1) * z ^ (2 * n + 1)) =
        (fun n => p.coeff n * z ^ n) ∘ fun n => 2 * n + 1 by
      funext n
      rfl]
    exact hsum.summable.comp_injective hdoubleOne
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (evenEntireBaseSeries f).coeff (2 * n)) (z ^ 2) = f z
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ, (evenEntireBaseSeries f).coeff (2 * n) * (z ^ 2) ^ n) =
        ∑' n : ℕ, p.coeff (2 * n) * z ^ (2 * n) := by
      apply tsum_congr
      intro n
      simp only [p]
      ring
    _ = ∑' n : ℕ, p.coeff n * z ^ n := by
      have hodd : (∑' n : ℕ, p.coeff (2 * n + 1) * z ^ (2 * n + 1)) = 0 := by
        calc
          (∑' n : ℕ, p.coeff (2 * n + 1) * z ^ (2 * n + 1)) =
              ∑' _n : ℕ, (0 : ℂ) := by
            apply tsum_congr
            intro n
            have hcoeff : p.coeff (2 * n + 1) = 0 := by
              simpa only [p] using evenEntireBaseSeries_coeff_eq_zero_of_odd
                hf heven (odd_two_mul_add_one n)
            rw [hcoeff, zero_mul]
          _ = 0 := tsum_zero
      have hsplit :
          (∑' n : ℕ, p.coeff (2 * n) * z ^ (2 * n)) +
              ∑' n : ℕ, p.coeff (2 * n + 1) * z ^ (2 * n + 1) =
            ∑' n : ℕ, p.coeff n * z ^ n :=
        tsum_even_add_odd (f := fun n : ℕ => p.coeff n * z ^ n) he ho
      calc
        (∑' n : ℕ, p.coeff (2 * n) * z ^ (2 * n)) =
            (∑' n : ℕ, p.coeff (2 * n) * z ^ (2 * n)) +
              ∑' n : ℕ, p.coeff (2 * n + 1) * z ^ (2 * n + 1) := by rw [hodd, add_zero]
        _ = ∑' n : ℕ, p.coeff n * z ^ n := hsplit
    _ = f z := hsum.tsum_eq

end

end GaloisForLFunctions.HTGeometry
