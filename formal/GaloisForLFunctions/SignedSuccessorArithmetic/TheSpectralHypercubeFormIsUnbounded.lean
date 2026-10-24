import GaloisForLFunctions.SignedSuccessorArithmetic.PartialEulerProductsDivergeInTheStrip
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Average

/-!
# The spectral hypercube form is unbounded for every integrable weight

Let `0 ≤ σ < 1` and let `w ≥ 0` be an integrable weight with positive mass on `(0, ∞)`. Then the
spectral hypercube form `∫ w(τ) ∏_{p ∈ S} |1 − p^{−σ+iτ}|² dτ` is unbounded over finite sets of
primes (`spectralHypercube_unbounded_of_integrable`). No regularity of `w` is used: the aligned
height intervals of `PartialEulerProductsDivergeInTheStrip` shrink at a rate comparable to their
distance from a fixed height `τ₀` (`eventually_aligned`), so the Lebesgue differentiation theorem
for non-centred balls gives `∫_{ball} w ≍ ρ · w(τ₀)` at almost every `τ₀`, while the Euler product
is at least `M/ρ` on the ball.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Real Finset Filter MeasureTheory Metric
open scoped Chebyshev Topology

/-- The window ratio `λ = exp(1/(10(τ₀+1)))` attached to a height `τ₀`. -/
noncomputable def alignLam (τ₀ : ℝ) : ℝ := exp (1 / (10 * (τ₀ + 1)))

/-- The aligned height `(2πj + π)/log x` just below `τ₀`. -/
noncomputable def alignedHeight (τ₀ x : ℝ) : ℝ :=
  (2 * π * ⌊(τ₀ * log x - π) / (2 * π)⌋ + π) / log x

/-- The radius `1/(10 log(λx))` on which the window stays aligned. -/
noncomputable def alignRadius (τ₀ x : ℝ) : ℝ := 1 / (10 * log (alignLam τ₀ * x))

theorem one_lt_alignLam {τ₀ : ℝ} (hτ₀ : 0 < τ₀) : 1 < alignLam τ₀ :=
  one_lt_exp_iff.mpr (by positivity)

theorem alignedHeight_spec {τ₀ x : ℝ} (hx : 1 < x) :
    alignedHeight τ₀ x * log x = 2 * π * ⌊(τ₀ * log x - π) / (2 * π)⌋ + π ∧
      alignedHeight τ₀ x ≤ τ₀ ∧ τ₀ - 2 * π / log x < alignedHeight τ₀ x := by
  have hlogx : 0 < log x := log_pos hx
  set j : ℤ := ⌊(τ₀ * log x - π) / (2 * π)⌋
  have hj1 : (j : ℝ) ≤ (τ₀ * log x - π) / (2 * π) := Int.floor_le _
  have hj2 : (τ₀ * log x - π) / (2 * π) < j + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ (by positivity)] at hj1
  rw [div_lt_iff₀ (by positivity)] at hj2
  refine ⟨by rw [alignedHeight]; field_simp; rfl, ?_, ?_⟩
  · rw [alignedHeight, div_le_iff₀ hlogx]; linarith only [hj1]
  · rw [alignedHeight, lt_div_iff₀ hlogx]
    have e : (τ₀ - 2 * π / log x) * log x = τ₀ * log x - 2 * π := by field_simp
    rw [e]
    linarith only [hj2]

/-- **Eventually aligned windows.** For large `x` the window of primes in `(x, λx]` makes
`ρ · ∏ |1 − p^{−σ+iτ}|² ≥ M` on the ball of radius `ρ = 1/(10 log λx)` around the aligned height,
and `τ₀` lies within `40π ρ` of that height. -/
theorem eventually_aligned {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (M : ℝ) :
    ∀ᶠ x in atTop, 0 < alignRadius τ₀ x ∧
      dist τ₀ (alignedHeight τ₀ x) ≤ 40 * π * alignRadius τ₀ x ∧
      ∀ τ ∈ closedBall (alignedHeight τ₀ x) (alignRadius τ₀ x),
        M ≤ alignRadius τ₀ x * eulerProductSq σ τ (primeWindow x (alignLam τ₀)) := by
  have hlam := one_lt_alignLam hτ₀
  have hloglam : log (alignLam τ₀) = 1 / (10 * (τ₀ + 1)) := log_exp _
  set c := (alignLam τ₀ - 1) / 2 * alignLam τ₀ ^ (-σ)
  have hc0 : 0 < c := by
    have := rpow_pos_of_pos (by linarith : (0 : ℝ) < alignLam τ₀) (-σ)
    have : 0 < (alignLam τ₀ - 1) / 2 := by linarith
    positivity
  filter_upwards [eventually_window_conditions hσ1 (M := M) hτ₀ hlam hc0] with x hx
  obtain ⟨hx1, hxlam, htheta, hspace, -, hgrowth⟩ := hx
  obtain ⟨hτ₁x, hτ₁le, hτ₁ge⟩ := alignedHeight_spec (τ₀ := τ₀) hx1
  have hlogx : 0 < log x := log_pos hx1
  have hloglamx : 0 < log (alignLam τ₀ * x) := log_pos (by nlinarith)
  have hlog2 : log (alignLam τ₀ * x) ≤ 2 * log x := by
    rw [log_mul (by linarith) (by linarith)]
    linarith only [log_le_log (by linarith) hxlam]
  have hρ0 : 0 < alignRadius τ₀ x := by rw [alignRadius]; positivity
  have hτ₁0 : 0 ≤ alignedHeight τ₀ x := by linarith only [hτ₁ge, hspace, hτ₀]
  have hτ₁lam : alignedHeight τ₀ x * log (alignLam τ₀) ≤ 1 / 10 := by
    rw [hloglam, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hτ₁le]
  refine ⟨hρ0, ?_, fun τ hτ => ?_⟩
  · rw [Real.dist_eq, abs_of_nonneg (by linarith only [hτ₁le])]
    have h1 : 2 * π / log x ≤ 40 * π * alignRadius τ₀ x := by
      rw [alignRadius, div_le_iff₀ hlogx]
      have : 40 * π * (1 / (10 * log (alignLam τ₀ * x))) * log x =
          4 * π * (log x / log (alignLam τ₀ * x)) := by field_simp; ring
      rw [this]
      have : 2 ≤ 4 * (log x / log (alignLam τ₀ * x)) := by
        rw [mul_div_assoc', le_div_iff₀ hloglamx]; linarith only [hlog2]
      nlinarith only [this, pi_pos]
    linarith only [h1, hτ₁ge]
  · have hτρ : |τ - alignedHeight τ₀ x| * log (alignLam τ₀ * x) ≤ 1 / 10 := by
      have : |τ - alignedHeight τ₀ x| ≤ alignRadius τ₀ x := by
        rwa [mem_closedBall, Real.dist_eq] at hτ
      calc |τ - alignedHeight τ₀ x| * log (alignLam τ₀ * x)
          ≤ alignRadius τ₀ x * log (alignLam τ₀ * x) :=
            mul_le_mul_of_nonneg_right this hloglamx.le
        _ = 1 / 10 := by rw [alignRadius]; field_simp
    have hmain := eulerProductSq_window_ge hσ0 hx1 hlam htheta hτ₁x hτ₁0 hτ₁lam hτρ
    exact (le_rho_mul_of_growth hloglamx hlog2 hgrowth).trans
      (mul_le_mul_of_nonneg_left hmain hρ0.le)

theorem tendsto_alignRadius {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    Tendsto (alignRadius τ₀) atTop (𝓝[>] 0) := by
  have hlam := one_lt_alignLam hτ₀
  have hlog : Tendsto (fun x : ℝ => 10 * log (alignLam τ₀ * x)) atTop atTop :=
    (tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by linarith))).const_mul_atTop
      (by norm_num)
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · show Tendsto (fun x => 1 / (10 * log (alignLam τ₀ * x))) atTop (𝓝 0)
    simp only [one_div]
    exact hlog.inv_tendsto_atTop
  · filter_upwards [hlog.eventually_gt_atTop 0] with x hx
    simp only [alignRadius, Set.mem_Ioi]
    positivity

/-- Against an integrable weight the squared Euler product of a set of primes is integrable. -/
theorem integrable_mul_eulerProductSq {σ : ℝ} (hσ0 : 0 ≤ σ) {w : ℝ → ℝ} (hwi : Integrable w)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) : Integrable fun τ => w τ * eulerProductSq σ τ S := by
  refine hwi.mul_bdd (continuous_eulerProductSq σ S).aestronglyMeasurable (c := 4 ^ S.card)
    (Eventually.of_forall fun τ => ?_)
  rw [norm_of_nonneg (eulerProductSq_nonneg σ τ S), eulerProductSq]
  calc ∏ p ∈ S, eulerFactorSq σ τ p ≤ ∏ _p ∈ S, (4 : ℝ) :=
        prod_le_prod (fun p _ => eulerFactorSq_nonneg σ τ p)
          fun p hp => eulerFactorSq_le_four hσ0 τ (hS p hp).one_lt.le
    _ = 4 ^ S.card := by simp

/-- **The spectral hypercube form diverges for every integrable weight.** For `0 ≤ σ < 1` and an
integrable `w ≥ 0` with `∫_{(0,∞)} w > 0`, `∫ w(τ) ∏_{p ∈ S} |1 − p^{−σ+iτ}|² dτ` is unbounded
over finite sets of primes. -/
theorem spectralHypercube_unbounded_of_integrable {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {w : ℝ → ℝ} (hwi : Integrable w) (hw0 : ∀ τ, 0 ≤ w τ) (hpos : 0 < ∫ τ in Set.Ioi 0, w τ)
    (M : ℝ) : ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ M ≤ ∫ τ, w τ * eulerProductSq σ τ S := by
  -- a point of density of `w` at a positive height with `w > 0`
  have hA : volume {τ : ℝ | 0 < τ ∧ 0 < w τ} ≠ 0 := by
    intro h0
    have hzero : ∀ᵐ τ ∂volume.restrict (Set.Ioi 0), w τ = 0 := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine (measure_eq_zero_iff_ae_notMem.mp h0).mono fun τ hτ hτpos => ?_
      by_contra hne
      exact hτ ⟨hτpos, lt_of_le_of_ne (hw0 τ) (Ne.symm hne)⟩
    rw [integral_congr_ae hzero, integral_zero] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨τ₀, ⟨hτ₀, hwτ₀⟩, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hA
    (ae_restrict_of_ae
      (IsUnifLocDoublingMeasure.ae_tendsto_average (μ := volume) hwi.locallyIntegrable (40 * π)))
  -- averages of `w` on the aligned balls tend to `w τ₀`
  have hav := hgood (alignedHeight τ₀) (alignRadius τ₀) (tendsto_alignRadius hτ₀)
    (by
      filter_upwards [eventually_aligned hσ0 hσ1 hτ₀ 0] with x hx
      rw [mem_closedBall]; exact hx.2.1)
  set M' := (|M| + 1) / w τ₀ with hM'
  have hev := ((eventually_aligned hσ0 hσ1 hτ₀ M').and
    ((tendsto_order.1 hav).1 (w τ₀ / 2) (half_lt_self hwτ₀))).and (eventually_gt_atTop 1)
  obtain ⟨x, ⟨⟨hρ0, -, hbig⟩, havg⟩, hx1⟩ := hev.exists
  set c := alignedHeight τ₀ x
  set ρ := alignRadius τ₀ x
  set S := primeWindow x (alignLam τ₀)
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (mem_primeWindow (by linarith) hp).2.2
  refine ⟨S, hSp, ?_⟩
  have hint := integrable_mul_eulerProductSq hσ0 hwi hSp
  -- `∫_{ball} w = 2ρ · ⨍_{ball} w`
  have hball : ∫ τ in closedBall c ρ, w τ = 2 * ρ * ⨍ τ in closedBall c ρ, w τ := by
    rw [setAverage_eq, volume_real_closedBall hρ0.le, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul]
  have hset : ∫ τ in closedBall c ρ, w τ * eulerProductSq σ τ S ≤ ∫ τ, w τ * eulerProductSq σ τ S :=
    setIntegral_le_integral hint
      (Eventually.of_forall fun τ => mul_nonneg (hw0 τ) (eulerProductSq_nonneg σ τ S))
  have hmono : ∫ τ in closedBall c ρ, w τ * (M' / ρ) ≤
      ∫ τ in closedBall c ρ, w τ * eulerProductSq σ τ S := by
    refine setIntegral_mono_on (hwi.integrableOn.mul_const _) hint.integrableOn
      measurableSet_closedBall fun τ hτ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hw0 τ)
    rw [div_le_iff₀ hρ0]
    exact (hbig τ hτ).trans_eq (mul_comm _ _)
  rw [integral_mul_const, hball] at hmono
  have hM'pos : 0 ≤ M' := by rw [hM']; positivity
  have hfinal : 2 * ρ * (w τ₀ / 2) * (M' / ρ) = |M| + 1 := by
    rw [hM']; field_simp
  have hlow : 2 * ρ * (w τ₀ / 2) * (M' / ρ) ≤
      2 * ρ * (⨍ τ in closedBall c ρ, w τ) * (M' / ρ) := by
    have := havg.le
    have : 0 ≤ M' / ρ := by positivity
    gcongr
  linarith only [hset, hmono, hfinal, hlow, le_abs_self M]

end GaloisForLFunctions.SignedSuccessorArithmetic
