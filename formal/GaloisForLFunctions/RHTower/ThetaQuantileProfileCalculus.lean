import GaloisForLFunctions.RHTower.ThetaQuantileFourierQuotient
import GaloisForLFunctions.RHTower.HedenmalmQuantileRootMode

/-!
# Calculus of the theta quantile profile

With `Q` the quantile of the theta density `k`, `M = ∫ k`, `H = k'/k` the hazard and
`q = M/k(Q)` the quantile speed on `(0,1)`:

* `h = 1/q = k(Q)/M` has `h' = H(Q)`, strictly decreasing, so `h` is strictly concave on `(0,1)`;
* `q' = −H(Q) q²` and `q'' = q³ (2H(Q)² − H'(Q)) > 0`, where `H' = (k''k − k'²)/k² < 0`;
* at the left endpoint `t q(t) → 0` (the endpoint ratio `I/k → 0`), and `t² H(Q(t)) q(t) ≤ t`,
  so `t³ q(t) → 0` and `t⁴ q'(t) → 0`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

/-! ## The quantile -/

abbrev thetaQuantile (t : ℝ) : ℝ := thetaSource.quantileFun t

theorem thetaQuantileSpeed_eq (t : ℝ) :
    thetaQuantileSpeed t = thetaSource.mass / thetaCuspFullSource (thetaQuantile t) := rfl

theorem hasDerivAt_thetaQuantile {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt thetaQuantile (thetaQuantileSpeed t) t :=
  hasDerivAt_quantileFun thetaSource ht

theorem tendsto_thetaQuantile_nhdsGT_zero : Tendsto thetaQuantile (𝓝[>] 0) atBot := by
  rw [tendsto_atBot]
  intro b
  have hFb := thetaSource.cdfFun_mem_Ioo b
  filter_upwards [Ioo_mem_nhdsGT hFb.1] with t ht
  have ht1 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hFb.2⟩
  have h := thetaSource.strictMonoOn_quantileFun ht1 hFb ht.2
  rw [thetaSource.quantile_cdfFun] at h
  exact h.le

theorem cdfFun_thetaQuantile {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : thetaSource.cdfFun (thetaQuantile t) = t :=
  thetaSource.cdfFun_quantile ht

/-- `t q(t)` is the endpoint ratio `I/k` at `Q(t)`. -/
theorem mul_thetaQuantileSpeed_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    t * thetaQuantileSpeed t = thetaEndpointRatio (thetaQuantile t) := by
  rw [thetaEndpointRatio, thetaLeftMass_eq_mass_mul_cdf, cdfFun_thetaQuantile ht, thetaQuantileSpeed_eq]
  have hk := thetaCuspFullSource_pos (thetaQuantile t)
  field_simp

theorem tendsto_mul_thetaQuantileSpeed : Tendsto (fun t => t * thetaQuantileSpeed t) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_thetaEndpointRatio_atBot.comp tendsto_thetaQuantile_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact (mul_thetaQuantileSpeed_eq ht).symm

/-! ## The profile `h = 1/q` and the derivatives of `q` -/

theorem hasDerivAt_thetaCuspFullSource (x : ℝ) :
    HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource x) x :=
  (contDiff_thetaCuspFullSource.differentiable (by norm_num) x).hasDerivAt

theorem hasDerivAt_iteratedDeriv_one_thetaCuspFullSource (x : ℝ) :
    HasDerivAt (iteratedDeriv 1 thetaCuspFullSource) (iteratedDeriv 2 thetaCuspFullSource x) x := by
  have h := hasDerivAt_thetaCuspFullDerivative 1 x
  rw [← iteratedDeriv_thetaCuspFullSource 1, ← iteratedDeriv_thetaCuspFullSource 2] at h
  simpa using h

/-- `H' = (k''k − k'²)/k²`. -/
theorem hasDerivAt_thetaLogHazard (x : ℝ) :
    HasDerivAt thetaLogHazard (thetaCuspLogConcavityNumerator x / thetaCuspFullSource x ^ 2) x := by
  have hquot := (hasDerivAt_iteratedDeriv_one_thetaCuspFullSource x).div
    (hasDerivAt_thetaCuspFullSource_iterate_zero x) (thetaCuspFullSource_pos_all x).ne'
  have hfun : thetaLogHazard = iteratedDeriv 1 thetaCuspFullSource / thetaCuspFullSource := by
    funext y; simp [thetaLogHazard, iteratedDeriv_one]
  rw [hfun]
  refine hquot.congr_deriv ?_
  unfold thetaCuspLogConcavityNumerator
  ring

theorem thetaLogHazardDeriv_neg (x : ℝ) :
    thetaCuspLogConcavityNumerator x / thetaCuspFullSource x ^ 2 < 0 :=
  div_neg_of_neg_of_pos (thetaCuspLogConcavityNumerator_neg_all x)
    (sq_pos_of_pos (thetaCuspFullSource_pos_all x))

/-- `q' = −H(Q) q²`. -/
theorem hasDerivAt_thetaQuantileSpeed {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt thetaQuantileSpeed (-(thetaLogHazard (thetaQuantile t) * thetaQuantileSpeed t ^ 2)) t := by
  have hk := thetaCuspFullSource_pos (thetaQuantile t)
  have hcomp := (hasDerivAt_thetaCuspFullSource (thetaQuantile t)).comp t (hasDerivAt_thetaQuantile ht)
  have h := (hasDerivAt_const t thetaSource.mass).div hcomp hk.ne'
  refine h.congr_deriv ?_
  simp only [thetaLogHazard, thetaQuantileSpeed_eq, Function.comp_apply]
  field_simp
  ring

/-- `q'' = q³ (2H(Q)² − H'(Q))`. -/
theorem hasDerivAt_thetaQuantileSpeedDeriv {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => -(thetaLogHazard (thetaQuantile s) * thetaQuantileSpeed s ^ 2))
      (thetaQuantileSpeed t ^ 3 * (2 * thetaLogHazard (thetaQuantile t) ^ 2 -
        thetaCuspLogConcavityNumerator (thetaQuantile t) / thetaCuspFullSource (thetaQuantile t) ^ 2)) t := by
  have h1 := (hasDerivAt_thetaLogHazard (thetaQuantile t)).comp t (hasDerivAt_thetaQuantile ht)
  have h2 := (hasDerivAt_thetaQuantileSpeed ht).pow 2
  have h := (h1.mul h2).neg
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, Pi.pow_apply]
  push_cast
  ring

theorem thetaQuantileSpeedDeriv2_pos (t : ℝ) :
    0 < thetaQuantileSpeed t ^ 3 * (2 * thetaLogHazard (thetaQuantile t) ^ 2 -
      thetaCuspLogConcavityNumerator (thetaQuantile t) / thetaCuspFullSource (thetaQuantile t) ^ 2) := by
  have hq := thetaQuantileSpeed_pos t
  have hH := thetaLogHazardDeriv_neg (thetaQuantile t)
  have : 0 < 2 * thetaLogHazard (thetaQuantile t) ^ 2 -
      thetaCuspLogConcavityNumerator (thetaQuantile t) / thetaCuspFullSource (thetaQuantile t) ^ 2 := by
    nlinarith [sq_nonneg (thetaLogHazard (thetaQuantile t))]
  positivity

/-- The profile `h = 1/q = k(Q)/M`. -/
def thetaQuantileProfile (t : ℝ) : ℝ := (thetaQuantileSpeed t)⁻¹

theorem thetaQuantileProfile_pos (t : ℝ) : 0 < thetaQuantileProfile t :=
  inv_pos.2 (thetaQuantileSpeed_pos t)

/-- `h' = H(Q)`. -/
theorem hasDerivAt_thetaQuantileProfile {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt thetaQuantileProfile (thetaLogHazard (thetaQuantile t)) t := by
  have h := (hasDerivAt_thetaQuantileSpeed ht).inv (thetaQuantileSpeed_pos t).ne'
  refine h.congr_deriv ?_
  have hq := (thetaQuantileSpeed_pos t).ne'
  rw [neg_neg, mul_div_assoc, div_self (pow_ne_zero 2 hq), mul_one]

theorem strictAntiOn_thetaLogHazard_thetaQuantile :
    StrictAntiOn (fun t => thetaLogHazard (thetaQuantile t)) (Ioo (0 : ℝ) 1) :=
  fun _ ha _ hb hab => strictAnti_thetaLogHazard (thetaSource.strictMonoOn_quantileFun ha hb hab)

theorem strictConcaveOn_thetaQuantileProfile : StrictConcaveOn ℝ (Ioo (0 : ℝ) 1) thetaQuantileProfile := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioo 0 1)
    (fun t ht => (hasDerivAt_thetaQuantileProfile ht).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioo]
  intro a ha b hb hab
  rw [(hasDerivAt_thetaQuantileProfile ha).deriv, (hasDerivAt_thetaQuantileProfile hb).deriv]
  exact strictAntiOn_thetaLogHazard_thetaQuantile ha hb hab

/-! ## Endpoint control -/

theorem thetaLogHazard_thetaQuantile_nonneg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht2 : t ≤ 1 / 2) :
    0 ≤ thetaLogHazard (thetaQuantile t) := by
  apply thetaLogHazard_nonneg_of_nonpos
  have h := thetaSource.strictMonoOn_quantileFun.monotoneOn ht ⟨by norm_num, by norm_num⟩ ht2
  have h0 : thetaQuantile (1 / 2) = 0 := by
    have := quantileFun_one_sub (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by constructor <;> norm_num)
    norm_num at this
    linarith
  rw [← h0]; exact h

/-- `t² · H(Q(t)) · q(t) ≤ t`, from `(I/k)·H ≤ 1`. -/
theorem sq_mul_thetaLogHazard_mul_le {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    t ^ 2 * (thetaLogHazard (thetaQuantile t) * thetaQuantileSpeed t) ≤ t := by
  have h := thetaEndpointRatio_mul_hazard_le (thetaQuantile t)
  rw [← mul_thetaQuantileSpeed_eq ht] at h
  nlinarith [ht.1]

theorem tendsto_cube_mul_thetaQuantileSpeed :
    Tendsto (fun t => t ^ 3 * thetaQuantileSpeed t) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have h := h1.mul tendsto_mul_thetaQuantileSpeed
  rw [mul_zero] at h
  exact h.congr fun t => by ring

/-- `t⁴ q'(t) → 0` at the left endpoint. -/
theorem tendsto_pow_four_mul_thetaQuantileSpeedDeriv :
    Tendsto (fun t => t ^ 4 * (-(thetaLogHazard (thetaQuantile t) * thetaQuantileSpeed t ^ 2)))
      (𝓝[>] 0) (𝓝 0) := by
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      |t ^ 4 * (-(thetaLogHazard (thetaQuantile t) * thetaQuantileSpeed t ^ 2))| ≤
        t ^ 2 * (t * thetaQuantileSpeed t) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
    have ht1 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans (by norm_num)⟩
    have hH := thetaLogHazard_thetaQuantile_nonneg ht1 ht.2.le
    have hq := thetaQuantileSpeed_pos t
    have hb := sq_mul_thetaLogHazard_mul_le ht1
    have ht0 : 0 ≤ t := ht.1.le
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 4),
      abs_of_nonneg (mul_nonneg hH (sq_nonneg _))]
    have : t ^ 4 * (thetaLogHazard (thetaQuantile t) * thetaQuantileSpeed t ^ 2) =
        (t * thetaQuantileSpeed t) * (t ^ 2 * (thetaLogHazard (thetaQuantile t) * thetaQuantileSpeed t)) * t := by
      ring
    rw [this]
    have htq : 0 ≤ t * thetaQuantileSpeed t := by positivity
    calc (t * thetaQuantileSpeed t) * (t ^ 2 * (thetaLogHazard (thetaQuantile t) * thetaQuantileSpeed t)) * t
        ≤ (t * thetaQuantileSpeed t) * t * t := by gcongr
      _ = t ^ 2 * (t * thetaQuantileSpeed t) := by ring
  have h1 : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have h2 := h1.mul tendsto_mul_thetaQuantileSpeed
  rw [mul_zero] at h2
  exact squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hbound) h2

end

end RHTower
