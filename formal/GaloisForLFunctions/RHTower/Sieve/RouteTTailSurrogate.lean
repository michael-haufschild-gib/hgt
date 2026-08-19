import GaloisForLFunctions.RHTower.Sieve.RouteTTailRho
import GaloisForLFunctions.RHTower.Sieve.WidthEnvelopeBounds

/-!
# The tail regimes through explicit surrogates

The three regimes of `Sieve/RouteTTailRho.exists_abs_sum_cos_div_primesRange_le_regimes` still
mention `routeTWidthPolylogLower` and `routeTTwistHeightFactor`.  Both are replaced here by closed
expressions in `|τ|` alone — the width by a lower bound (which is the safe direction in the contour
regime, where a smaller width means a weaker saving) and the height factor by an upper bound.

The surrogate height is `2 log(6|τ| + 6) + 1`, which is *exactly* the corpus's
`routeTLogHeightEnvelope (4(3|τ|/2 + 1))`, so both substitutions are instances of
`Sieve/WidthEnvelopeBounds`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The closed height surrogate. -/
def routeTHeightSurrogate (τ : ℝ) : ℝ := 2 * Real.log (6 * |τ| + 6) + 1

/-- The closed reciprocal-width surrogate. -/
def routeTWidthReciprocalSurrogate (A τ : ℝ) : ℝ :=
  10 * routeTZeroFreeDeltaEnvelopeConstant A * (routeTHeightSurrogate τ) ^ ((9 : ℝ) / 10)
    * (1 + Real.log (routeTHeightSurrogate τ)) ^ 2

/-- The closed lower bound for the width. -/
def routeTWidthLowSurrogate (A τ : ℝ) : ℝ := 1 / routeTWidthReciprocalSurrogate A τ

/-- The closed upper bound for the height factor. -/
def routeTHeightFactorUpper (A τ : ℝ) : ℝ :=
  1 + Real.log (3 * |τ| / 2 + 3) * routeTWidthReciprocalSurrogate A τ

theorem routeTHeightSurrogate_eq (τ : ℝ) :
    routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) = routeTHeightSurrogate τ := by
  rw [routeTLogHeightEnvelope, routeTHeightSurrogate]
  congr 2
  ring_nf

theorem one_le_routeTHeightSurrogate (τ : ℝ) : 1 ≤ routeTHeightSurrogate τ := by
  have h : (0 : ℝ) ≤ Real.log (6 * |τ| + 6) := by
    refine Real.log_nonneg ?_
    have := abs_nonneg τ
    linarith
  rw [routeTHeightSurrogate]
  linarith

theorem routeTWidthReciprocalSurrogate_pos (A τ : ℝ) : 0 < routeTWidthReciprocalSurrogate A τ := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hZ := one_le_routeTHeightSurrogate τ
  have hpow : (0 : ℝ) < (routeTHeightSurrogate τ) ^ ((9 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hlog : (0 : ℝ) ≤ Real.log (routeTHeightSurrogate τ) := Real.log_nonneg hZ
  rw [routeTWidthReciprocalSurrogate]
  positivity

/-- **The width surrogate is a lower bound for the width.** -/
theorem routeTWidthLowSurrogate_le {A τ : ℝ} (hτ : 1 ≤ |τ|) :
    routeTWidthLowSurrogate A τ ≤ routeTWidthPolylogLower A τ := by
  have hZ := one_le_routeTHeightSurrogate τ
  have hbase := routeTWidthPolylogLower_ge (A := A) (τ := τ)
    (Z := routeTHeightSurrogate τ) hτ (le_of_eq (routeTHeightSurrogate_eq τ)) hZ
  rw [routeTWidthLowSurrogate, routeTWidthReciprocalSurrogate]
  exact hbase

/-- **The height factor is below its surrogate.** -/
theorem routeTTwistHeightFactor_le_surrogate {A τ : ℝ} (hτ : 16 * Real.pi / 3 ≤ |τ|) :
    routeTTwistHeightFactor A τ ≤ routeTHeightFactorUpper A τ := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hτ1 : (1 : ℝ) ≤ |τ| := by linarith
  have hZ := one_le_routeTHeightSurrogate τ
  have hbase := routeTTwistHeightFactor_le_explicit (A := A) hτ
  have hinv := inv_routeTWidthPolylogLower_le (A := A) (τ := τ)
    (Z := routeTHeightSurrogate τ) hτ1 (le_of_eq (routeTHeightSurrogate_eq τ)) hZ
  have hlogpos : (0 : ℝ) ≤ Real.log (3 * |τ| / 2 + 3) := by
    refine Real.log_nonneg ?_
    have := abs_nonneg τ
    linarith
  have hstep : Real.log (3 * |τ| / 2 + 3) / routeTWidthPolylogLower A τ
      ≤ Real.log (3 * |τ| / 2 + 3) * routeTWidthReciprocalSurrogate A τ := by
    have hdiv : Real.log (3 * |τ| / 2 + 3) / routeTWidthPolylogLower A τ
        = Real.log (3 * |τ| / 2 + 3) * (1 / routeTWidthPolylogLower A τ) := by ring
    rw [hdiv, routeTWidthReciprocalSurrogate]
    exact mul_le_mul_of_nonneg_left hinv hlogpos
  have hone : 1 / (1 + |τ|) ≤ 1 := by
    have := abs_nonneg τ
    rw [div_le_one (by linarith)]
    linarith
  rw [routeTHeightFactorUpper]
  linarith [hbase, hstep, hone]

/-- **The tail cosine sum through the closed surrogates.**  No corpus-internal quantity is left in
the three regimes: each is an explicit function of the block top and the frequency. -/
theorem exists_abs_sum_cos_div_primesRange_le_surrogate :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (y z : ℕ) (t ρ₀ : ℝ), 1 ≤ y → y ≤ z → 0 ≤ ρ₀ →
        16 * Real.pi / 3 ≤ |t| →
        14 * Real.exp 9 ≤ ρ₀ * (y : ℝ) →
        (∀ i : ℕ, y ≤ i → i ≤ z →
          9 * C * ((3 * (i : ℝ)) ^ (-(min delta (routeTWidthLowSurrogate A (-t)) / 6))
            * (routeTHeightFactorUpper A (-t) + Real.log (2 * (i : ℝ)))) ≤ ρ₀) →
        (∀ i : ℕ, y ≤ i → i ≤ z →
          9 * C * ((3 * (i : ℝ)) ^ (2 * (1 / (routeTWidthUpperConst
                * (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3)
            * (1 + (Real.log (i : ℝ)) ^ 2 + routeTHeightFactorUpper A (-t)))
            / (1 + |t|) ≤ ρ₀) →
        (∀ i : ℕ, y ≤ i → i ≤ z → 6 * Real.log (i : ℝ) / Real.sqrt (i : ℝ) ≤ ρ₀) →
        |∑ p ∈ primesRange y z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)|
          ≤ 9 * ρ₀ * (2 + Real.log (z : ℝ)) := by
  obtain ⟨A, delta, C, hdelta, hC, hbound⟩ := exists_abs_sum_cos_div_primesRange_le_regimes
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro y z t ρ₀ hy hyz hρ₀ hτ he9 h1 h2 h3
  have habs : |(-t : ℝ)| = |t| := abs_neg t
  have hτ' : 16 * Real.pi / 3 ≤ |(-t : ℝ)| := by rw [habs]; exact hτ
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hτ1 : (1 : ℝ) ≤ |(-t : ℝ)| := by rw [habs]; linarith
  have hwid := routeTWidthLowSurrogate_le (A := A) (τ := -t) hτ1
  have hHF := routeTTwistHeightFactor_le_surrogate (A := A) (τ := -t) hτ'
  refine hbound y z t ρ₀ hy hyz hρ₀ hτ he9 ?_ ?_ h3
  · intro i hyi hiz
    refine le_trans ?_ (h1 i hyi hiz)
    have hi1 : 1 ≤ i := le_trans hy hyi
    have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
    have h3i : (1 : ℝ) ≤ 3 * (i : ℝ) := by linarith
    have hmin : min delta (routeTWidthLowSurrogate A (-t))
        ≤ min delta (routeTWidthPolylogLower A (-t)) := by
      exact le_min (min_le_left _ _) (le_trans (min_le_right _ _) hwid)
    have hexp : (3 * (i : ℝ)) ^ (-(min delta (routeTWidthPolylogLower A (-t)) / 6))
        ≤ (3 * (i : ℝ)) ^ (-(min delta (routeTWidthLowSurrogate A (-t)) / 6)) :=
      Real.rpow_le_rpow_of_exponent_le h3i (by linarith)
    have hlog2i : (0 : ℝ) ≤ Real.log (2 * (i : ℝ)) := Real.log_nonneg (by linarith)
    have hHF0 : (0 : ℝ) ≤ routeTTwistHeightFactor A (-t) := routeTTwistHeightFactor_nonneg A (-t)
    have hfac : routeTTwistHeightFactor A (-t) + Real.log (2 * (i : ℝ))
        ≤ routeTHeightFactorUpper A (-t) + Real.log (2 * (i : ℝ)) := by linarith
    have hexp0 : (0 : ℝ) ≤ (3 * (i : ℝ)) ^ (-(min delta (routeTWidthPolylogLower A (-t)) / 6)) :=
      Real.rpow_nonneg (by linarith) _
    have hfac0 : (0 : ℝ) ≤ routeTTwistHeightFactor A (-t) + Real.log (2 * (i : ℝ)) := by linarith
    have hmul := mul_le_mul hexp hfac hfac0 (Real.rpow_nonneg (by linarith) _)
    nlinarith [hmul, hC.le]
  · intro i hyi hiz
    refine le_trans ?_ (h2 i hyi hiz)
    have hi1 : 1 ≤ i := le_trans hy hyi
    have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
    have hτ0 : (0 : ℝ) < 1 + |t| := by have := abs_nonneg t; linarith
    have hfac : 1 + (Real.log (i : ℝ)) ^ 2 + routeTTwistHeightFactor A (-t)
        ≤ 1 + (Real.log (i : ℝ)) ^ 2 + routeTHeightFactorUpper A (-t) := by linarith
    have hexp0 : (0 : ℝ) ≤ (3 * (i : ℝ)) ^ (2 * (1 / (routeTWidthUpperConst
        * (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3) :=
      Real.rpow_nonneg (by linarith) _
    have hmul : (3 * (i : ℝ)) ^ (2 * (1 / (routeTWidthUpperConst
          * (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3)
          * (1 + (Real.log (i : ℝ)) ^ 2 + routeTTwistHeightFactor A (-t))
        ≤ (3 * (i : ℝ)) ^ (2 * (1 / (routeTWidthUpperConst
          * (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3)
          * (1 + (Real.log (i : ℝ)) ^ 2 + routeTHeightFactorUpper A (-t)) :=
      mul_le_mul_of_nonneg_left hfac hexp0
    have hCmul := mul_le_mul_of_nonneg_left hmul (by positivity : (0:ℝ) ≤ 9 * C)
    exact div_le_div_of_nonneg_right hCmul hτ0.le

end

end RHTower.Sieve
