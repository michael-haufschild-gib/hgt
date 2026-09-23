import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import GaloisForLFunctions.HTGeometry.NonstationaryPhaseLowerBound

/-!
# Cell cancellation for the twisted Hardy phase

The phase of the `n`-th term of the approximate functional equation for Hardy's function is
`θ(τ) − τ log n`, whose velocity is `θ'(τ) − log n = ½ log(τ/2π) − log n + O(1/τ)`.  Below the
conductor `√(τ/2π)` this velocity is bounded away from zero, so the tree's first-derivative test
applies verbatim and every cell integral of such a term is `O(1/δ)` plus a curvature term
controlled by `|θ''| ≤ 1/τ² + π/(4τ)`.

This is the atomic cancellation estimate of the superlinear real-Xi density programme
(`docs/drafts/pipeline/1-in-progress/selberg-superlinear-xi-density-programme.md`).
-/

open Set MeasureTheory Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## Continuity of the exact Hardy phase curvature -/

theorem continuousAt_deriv_digamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt (deriv Complex.digamma) z :=
  (digamma_analyticOnNhd_re_pos z hz).deriv.continuousAt

theorem continuous_deriv_gammaHardyPhaseRate : Continuous (deriv gammaHardyPhaseRate) := by
  have hfun : deriv gammaHardyPhaseRate
      = fun t : ℝ => -(deriv Complex.digamma (linePt t / 2)).im / 4 :=
    funext deriv_gammaHardyPhaseRate
  rw [hfun]
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have harg : ContinuousAt (fun u : ℝ => linePt u / 2) t :=
    ((hasDerivAt_linePt t).continuousAt).div_const 2
  have hre : (0 : ℝ) < (linePt t / 2).re := by
    rw [re_div_two, linePt_re]
    norm_num
  have hcomp : ContinuousAt (fun u : ℝ => deriv Complex.digamma (linePt u / 2)) t := by
    have h : ContinuousAt
        ((fun z : ℂ => deriv Complex.digamma z) ∘ (fun u : ℝ => linePt u / 2)) t :=
      ContinuousAt.comp (g := fun z : ℂ => deriv Complex.digamma z)
        (f := fun u : ℝ => linePt u / 2) (continuousAt_deriv_digamma_of_re_pos hre) harg
    simpa [Function.comp_def] using h
  have him : ContinuousAt (fun u : ℝ => (deriv Complex.digamma (linePt u / 2)).im) t := by
    have h : ContinuousAt
        (Complex.im ∘ (fun u : ℝ => deriv Complex.digamma (linePt u / 2))) t :=
      ContinuousAt.comp (g := Complex.im)
        (f := fun u : ℝ => deriv Complex.digamma (linePt u / 2))
        Complex.continuous_im.continuousAt hcomp
    simpa [Function.comp_def] using h
  exact (him.neg).div_const 4

/-! ## The twisted Hardy phase -/

/-- The phase `θ(τ) − τ L` of a twisted Hardy term. -/
def hardyTwistPhase (L τ : ℝ) : ℝ := gammaHardyTheta τ - τ * L

theorem hasDerivAt_hardyTwistPhase (L τ : ℝ) :
    HasDerivAt (hardyTwistPhase L) (gammaHardyPhaseRate τ - L) τ := by
  have hlin : HasDerivAt (fun s : ℝ => s * L) L τ := by
    simpa using (hasDerivAt_id τ).mul_const L
  exact (hasDerivAt_gammaHardyTheta τ).sub hlin

theorem hasDerivAt_hardyTwistRate (L τ : ℝ) :
    HasDerivAt (fun s : ℝ => gammaHardyPhaseRate s - L) (deriv gammaHardyPhaseRate τ) τ :=
  ((hasDerivAt_gammaHardyPhaseRate τ).sub_const L).congr_deriv
    (deriv_gammaHardyPhaseRate τ).symm

/-! ## The cell estimate -/

/-- **Cell cancellation for a twisted Hardy phase.**  A weight with an integrable derivative
against a nonstationary Hardy phase gives the first-derivative test with the exact Hardy
curvature. -/
theorem abs_integral_mul_cos_hardyTwistPhase_le {u v L φ m : ℝ} (huv : u ≤ v) (hm : 0 < m)
    {g g' : ℝ → ℝ} (hg : ∀ τ ∈ Icc u v, HasDerivAt g (g' τ) τ)
    (hgc : ContinuousOn g (Icc u v)) (hg'c : ContinuousOn g' (Icc u v))
    (hlow : ∀ τ ∈ Icc u v, m ≤ |gammaHardyPhaseRate τ - L|) :
    |∫ τ in u..v, g τ * Real.cos (hardyTwistPhase L τ + φ)|
      ≤ |g u| / m + |g v| / m
        + ∫ τ in u..v, (|g' τ| / m
            + |g τ| * |deriv gammaHardyPhaseRate τ| / m ^ (2 : ℕ)) := by
  have h := abs_integral_mul_cos_phase_le_on (a := u) (b := v) (c := 1) (φ := φ) (m := m)
    (g := g) (g' := g') (ξ := hardyTwistPhase L)
    (ξ' := fun τ => gammaHardyPhaseRate τ - L) (ξ'' := deriv gammaHardyPhaseRate)
    huv one_pos hm hg hgc hg'c
    (fun τ _ => hasDerivAt_hardyTwistPhase L τ)
    (continuous_gammaHardyPhaseRate.sub continuous_const).continuousOn
    (fun τ _ => hasDerivAt_hardyTwistRate L τ)
    continuous_deriv_gammaHardyPhaseRate.continuousOn hlow
  simpa using h

/-! ## Nonstationarity below the conductor -/

/-- **Nonstationarity below the conductor.**  If `L` sits below `½ log(T/2π)` by `2δ` and the
explicit phase-rate error at height `T` is at most `δ`, then the twisted Hardy phase has velocity at
least `δ` throughout `[T, ∞)`. -/
theorem le_abs_gammaHardyPhaseRate_sub_of_le_conductor
    {δ T τ L : ℝ} (hT : 0 < T) (hτ : T ≤ τ)
    (herr : 33 / (16 * T ^ (2 : ℕ)) + Real.pi / (2 * T) ≤ δ)
    (hL : L ≤ Real.log (T / (2 * Real.pi)) / 2 - 2 * δ) :
    δ ≤ |gammaHardyPhaseRate τ - L| := by
  have hτ0 : 0 < τ := lt_of_lt_of_le hT hτ
  have hbound := gammaHardyPhaseRate_sub_log_conductor_bound hτ0
  have hlow : Real.log (τ / (2 * Real.pi)) / 2 - (33 / (16 * τ ^ (2 : ℕ)) + Real.pi / (2 * τ))
      ≤ gammaHardyPhaseRate τ := by
    have := abs_le.mp hbound
    linarith [this.1]
  have hlog : Real.log (T / (2 * Real.pi)) / 2 ≤ Real.log (τ / (2 * Real.pi)) / 2 := by
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have h1 : T / (2 * Real.pi) ≤ τ / (2 * Real.pi) := by gcongr
    have h2 : (0 : ℝ) < T / (2 * Real.pi) := by positivity
    have := Real.log_le_log h2 h1
    linarith
  have herrmono : 33 / (16 * τ ^ (2 : ℕ)) + Real.pi / (2 * τ)
      ≤ 33 / (16 * T ^ (2 : ℕ)) + Real.pi / (2 * T) := by
    have hsq : 16 * T ^ (2 : ℕ) ≤ 16 * τ ^ (2 : ℕ) := by nlinarith [hT.le, hτ]
    have h1 : 33 / (16 * τ ^ (2 : ℕ)) ≤ 33 / (16 * T ^ (2 : ℕ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    have h2 : Real.pi / (2 * τ) ≤ Real.pi / (2 * T) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)
    linarith
  refine le_trans ?_ (le_abs_self _)
  linarith

/-! ## The bare cell integral -/

theorem intervalIntegrable_abs_deriv_gammaHardyPhaseRate (u v : ℝ) :
    IntervalIntegrable (fun τ => |deriv gammaHardyPhaseRate τ|) volume u v :=
  (continuous_deriv_gammaHardyPhaseRate.abs).intervalIntegrable u v

/-- **The bare twisted Hardy cell integral is `O(1/δ)`.**  With unit weight the first-derivative
test and the curvature bound `|θ''| ≤ 1/τ² + π/(4τ)` give an explicit bound with no arithmetic
input. -/
theorem abs_integral_cos_hardyTwistPhase_le {u v L φ δ T : ℝ} (huv : u ≤ v) (hδ : 0 < δ)
    (hT : 0 < T) (hu : T ≤ u)
    (herr : 33 / (16 * T ^ (2 : ℕ)) + Real.pi / (2 * T) ≤ δ)
    (hL : L ≤ Real.log (T / (2 * Real.pi)) / 2 - 2 * δ) :
    |∫ τ in u..v, Real.cos (hardyTwistPhase L τ + φ)|
      ≤ 2 / δ + (v - u) * (1 / T ^ (2 : ℕ) + Real.pi / (4 * T)) / δ ^ (2 : ℕ) := by
  have hlow : ∀ τ ∈ Icc u v, δ ≤ |gammaHardyPhaseRate τ - L| := fun τ hτ =>
    le_abs_gammaHardyPhaseRate_sub_of_le_conductor hT (le_trans hu hτ.1) herr hL
  have hmain := abs_integral_mul_cos_hardyTwistPhase_le (u := u) (v := v) (L := L) (φ := φ)
    (m := δ) (g := fun _ => (1 : ℝ)) (g' := fun _ => (0 : ℝ)) huv hδ
    (fun τ _ => hasDerivAt_const τ (1 : ℝ)) continuousOn_const continuousOn_const hlow
  have hcurv : ∀ τ ∈ Icc u v,
      (|(0 : ℝ)| / δ + |(1 : ℝ)| * |deriv gammaHardyPhaseRate τ| / δ ^ (2 : ℕ))
        ≤ (1 / T ^ (2 : ℕ) + Real.pi / (4 * T)) / δ ^ (2 : ℕ) := by
    intro τ hτ
    have hτ0 : 0 < τ := lt_of_lt_of_le hT (le_trans hu hτ.1)
    have hb := abs_deriv_gammaHardyPhaseRate_le hτ0
    have hmono : 1 / τ ^ (2 : ℕ) + Real.pi / (4 * τ) ≤ 1 / T ^ (2 : ℕ) + Real.pi / (4 * T) := by
      have hτT : T ≤ τ := le_trans hu hτ.1
      have hsq : T ^ (2 : ℕ) ≤ τ ^ (2 : ℕ) := by nlinarith [hT.le]
      have h1 : 1 / τ ^ (2 : ℕ) ≤ 1 / T ^ (2 : ℕ) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
      have h2 : Real.pi / (4 * τ) ≤ Real.pi / (4 * T) :=
        div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)
      linarith
    have hδ2 : (0 : ℝ) < δ ^ (2 : ℕ) := by positivity
    have : |deriv gammaHardyPhaseRate τ| ≤ 1 / T ^ (2 : ℕ) + Real.pi / (4 * T) :=
      le_trans hb hmono
    rw [abs_zero, abs_one, one_mul, zero_div, zero_add]
    exact div_le_div_of_nonneg_right this hδ2.le
  have hint : IntervalIntegrable
      (fun τ => |(0 : ℝ)| / δ + |(1 : ℝ)| * |deriv gammaHardyPhaseRate τ| / δ ^ (2 : ℕ)) volume u v := by
    simpa using ((intervalIntegrable_abs_deriv_gammaHardyPhaseRate u v).div_const (δ ^ (2 : ℕ)))
  have hbound : (∫ τ in u..v,
      (|(0 : ℝ)| / δ + |(1 : ℝ)| * |deriv gammaHardyPhaseRate τ| / δ ^ (2 : ℕ)))
      ≤ (v - u) * ((1 / T ^ (2 : ℕ) + Real.pi / (4 * T)) / δ ^ (2 : ℕ)) := by
    have h := intervalIntegral.integral_mono_on huv hint intervalIntegrable_const hcurv
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h
  have hleft : |(1 : ℝ)| / δ + |(1 : ℝ)| / δ = 2 / δ := by
    rw [abs_one]
    ring
  calc |∫ τ in u..v, Real.cos (hardyTwistPhase L τ + φ)|
      = |∫ τ in u..v, (fun _ => (1 : ℝ)) τ * Real.cos (hardyTwistPhase L τ + φ)| := by
        simp
    _ ≤ |(1 : ℝ)| / δ + |(1 : ℝ)| / δ
        + ∫ τ in u..v, (|(0 : ℝ)| / δ + |(1 : ℝ)| * |deriv gammaHardyPhaseRate τ| / δ ^ (2 : ℕ)) :=
        hmain
    _ ≤ 2 / δ + (v - u) * ((1 / T ^ (2 : ℕ) + Real.pi / (4 * T)) / δ ^ (2 : ℕ)) := by
        rw [hleft]; linarith
    _ = 2 / δ + (v - u) * (1 / T ^ (2 : ℕ) + Real.pi / (4 * T)) / δ ^ (2 : ℕ) := by ring

end RHTower

end
