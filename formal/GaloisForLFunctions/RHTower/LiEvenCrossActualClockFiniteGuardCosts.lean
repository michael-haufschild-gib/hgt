import GaloisForLFunctions.RHTower.LiEvenCrossActualClockFiniteGuardKernels
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockLogHistoryAnalytic
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockSourceCorrelationEnvelope

/-!
# Finite guarded-clock source costs

For a history `D ≥ 0` on `[0,t]`, the gap convolution splits as `P⋆G = A_G - N_G` with the
positive part `A_G = ∫₀ᵗ D[H_G]_+ > 0` and the whole negative part `N_G = ∫₀^{t/4} D[-H_G]_+`
(the kernel `H_G` is nonnegative on `[t/4, t]`), with
`N_G ≤ A G(t)t³e^{t/1200}/768`, `A = ∑_q |w_q|²` the spectral mass.  For `0 ≤ x ≤ t`,
`∫₀ˣ P(s)g(t-s) ds = xD(x)g(t-x) + A_g - L_g` with nonnegative costs and
`L_g ≤ ∫₀ˣ D g(t-·) ≤ A g(t)x³e^{x/300}/12`.  At a guarded zero the outer cost integral is
exactly `I_U = W + 8C₁ + 16(N_G + L_g(ℓ)) - 16(A_G + A_g(ℓ))`, hence
`I_U < W + 8C₁ + 16(N_G + L_g(ℓ)) ≤ W + 8C₁ + (A/48)G(t)t³e^{t/1200} + (4A/3)g(t)ℓ³e^{ℓ/300}`,
and `W ≤ (A/4)∫_ℓ^t s²e^{s/300}(16t - 15s)T(t-s) ds`.
-/

open MeasureTheory Set Filter Topology
open scoped Interval
namespace RHTower
noncomputable section
local notation "P" => liEvenCrossActualClockPrimitive
local notation "D" => liEvenCrossActualClockLogHistory
local notation "Dens" => liEvenCrossActualClockLogHistoryDensity
local notation "M" => liEvenCrossActualClockBorelPrimitive
local notation "G" => liEvenCrossActualClockPrimitiveScoreGap
local notation "Tc" => liClockThetaSmoothedBorelProfile
local notation "g" => liEvenCrossActualClockReciprocalPrimitive
local notation "HG" => liEvenCrossActualClockPrimitiveGapHistoryKernel
local notation "ell" => liEvenCrossActualClockHistoryScale
local notation "IU" => liEvenCrossActualClockScoreCostIntegral
local notation "Amass" => xiShiftAbsoluteMass 0

/-- The whole negative part of the gap history, `N_G(t) = ∫₀^{t/4} D[-H_G]_+`. -/
def liEvenCrossActualClockGapNegativeHistoryCost (t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..(t/4), D s*max (-HG t s) 0

/-- The positive part of the gap history, `A_G(t) = ∫₀ᵗ D[H_G]_+`. -/
def liEvenCrossActualClockGapPositiveHistoryCost (t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..t, D s*max (HG t s) 0

/-- The early negative reciprocal cost `L_g(t,x) = ∫₀ˣ D[g(t-s) - sg'(t-s)]_+`. -/
def liEvenCrossActualClockReciprocalEarlyNegativeCost (t x : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..x, D s*max (g (t-s) - s*deriv g (t-s)) 0

/-- The early positive reciprocal cost `A_g(t,x) = ∫₀ˣ D[sg'(t-s) - g(t-s)]_+`. -/
def liEvenCrossActualClockReciprocalEarlyPositiveCost (t x : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..x, D s*max (s*deriv g (t-s) - g (t-s)) 0

/-- The outer weight cost `W(t) = ∫_ℓ^t D(s)(16t - 15s)T(t-s) ds`. -/
def liEvenCrossActualClockFiniteGuardWeightCost (t : ℝ) : ℝ :=
  ∫ s in ell t..t, D s*(16*t-15*s)*(Tc ((t-s):ℂ)).re

local notation "NG" => liEvenCrossActualClockGapNegativeHistoryCost
local notation "AG" => liEvenCrossActualClockGapPositiveHistoryCost
local notation "Lg" => liEvenCrossActualClockReciprocalEarlyNegativeCost
local notation "Ag" => liEvenCrossActualClockReciprocalEarlyPositiveCost
local notation "W" => liEvenCrossActualClockFiniteGuardWeightCost

private theorem fc_D_cont : Continuous D :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_liEvenCrossActualClockLogHistory s).continuousAt
private theorem fc_P_cont : Continuous P := contDiff_liEvenCrossActualClockPrimitive.continuous
private theorem fc_G_deriv_cont : Continuous (deriv G) :=
  contDiff_liEvenCrossActualClockPrimitiveScoreGap.continuous_deriv (by exact_mod_cast le_top)
private theorem fc_g_deriv_cont : Continuous (deriv g) :=
  contDiff_liEvenCrossActualClockReciprocalPrimitive.continuous_deriv (by exact_mod_cast le_top)
private theorem fc_HG_cont (t : ℝ) : Continuous (fun s => HG t s) := by
  unfold liEvenCrossActualClockPrimitiveGapHistoryKernel
  exact (continuous_id.mul (fc_G_deriv_cont.comp (continuous_const.sub continuous_id))).sub
    (contDiff_liEvenCrossActualClockPrimitiveScoreGap.continuous.comp (continuous_const.sub continuous_id))
private theorem fc_g_lag_cont (t : ℝ) : Continuous (fun s => g (t-s)) :=
  contDiff_liEvenCrossActualClockReciprocalPrimitive.continuous.comp (continuous_const.sub continuous_id)
private theorem fc_gd_lag_cont (t : ℝ) : Continuous (fun s => deriv g (t-s)) :=
  fc_g_deriv_cont.comp (continuous_const.sub continuous_id)
private theorem fc_mul_density (s : ℝ) : s*Dens s = P s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [liEvenCrossActualClockPrimitive_origin_even.1]
  · rw [liEvenCrossActualClockLogHistoryDensity]; field_simp

private theorem fc_D_env {s : ℝ} (hs : 0 ≤ s) : D s ≤ Amass*s^2/4*Real.exp (s/300) := by
  have h := abs_liEvenCrossActualClockLogHistory_le_source_envelope (γ := 1/300) le_rfl hs
  rw [show (1/300:ℝ)*s = s/300 by ring] at h
  exact (le_abs_self _).trans h

private theorem fc_G_mono : MonotoneOn G (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    contDiff_liEvenCrossActualClockPrimitiveScoreGap.continuous.continuousOn
    (contDiff_liEvenCrossActualClockPrimitiveScoreGap.differentiable (by simp)).differentiableOn
    fun x hx => ?_
  rw [interior_Ici] at hx
  exact (liEvenCrossActualClockPrimitiveScoreGap_degree.2 x (le_of_lt hx)).1

private theorem fc_g_mono : MonotoneOn g (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    contDiff_liEvenCrossActualClockReciprocalPrimitive.continuous.continuousOn
    (contDiff_liEvenCrossActualClockReciprocalPrimitive.differentiable (by simp)).differentiableOn
    fun x hx => ?_
  rw [interior_Ici] at hx
  exact (liEvenCrossActualClockReciprocalPrimitive_origin_nonneg.2.2.2 x (le_of_lt hx)).2.1

private theorem fc_G_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ G r := by
  have h := liEvenCrossActualClockPrimitiveScoreGap_lower hr
  have := thetaCuspNormalizedEvenMoment_pos 1
  exact le_trans (by positivity) h

private theorem fc_poly_integral (c x : ℝ) : (∫ s in (0:ℝ)..x, c*s^2) = c*x^3/3 := by
  rw [intervalIntegral.integral_const_mul, integral_pow]; ring

/-- **(F9)**  For `t > 0` and `D ≥ 0` on `[0,t]`: `P⋆G = ∫₀ᵗ D H_G`; the whole negative part
lives on `[0, t/4]`; `P⋆G = A_G - N_G` with `N_G ≥ 0` and `A_G > 0`, so `P⋆G > -N_G`. -/
theorem liEvenCrossActualClockGapHistoryCost_decomposition {t : ℝ} (ht : 0 < t)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    (∫ s in (0:ℝ)..t, P s*G (t-s)) = (∫ s in (0:ℝ)..t, D s*HG t s) ∧
      (∫ s in (0:ℝ)..t, D s*max (-HG t s) 0) = NG t ∧
      (∫ s in (0:ℝ)..t, P s*G (t-s)) = AG t - NG t ∧
      0 ≤ NG t ∧ 0 < AG t ∧ -NG t < ∫ s in (0:ℝ)..t, P s*G (t-s) := by
  obtain ⟨-, -, hsign⟩ := liEvenCrossActualClockPrimitiveGapHistoryKernel_sign ht
  have hHGt := (liEvenCrossActualClockPrimitiveGapHistoryKernel_sign ht).1
  have hcN : Continuous (fun s => D s*max (-HG t s) 0) :=
    fc_D_cont.mul ((fc_HG_cont t).neg.max continuous_const)
  have hcA : Continuous (fun s => D s*max (HG t s) 0) :=
    fc_D_cont.mul ((fc_HG_cont t).max continuous_const)
  have h1 : (∫ s in (0:ℝ)..t, P s*G (t-s)) = (∫ s in (0:ℝ)..t, D s*HG t s) :=
    liEvenCrossActualClockLogHistory_score_gap_balance t
  have h2 : (∫ s in (0:ℝ)..t, D s*max (-HG t s) 0) = NG t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := t/4)
      (hcN.intervalIntegrable _ _) (hcN.intervalIntegrable _ _)]
    have hz : (∫ s in (t/4)..t, D s*max (-HG t s) 0) = 0 := by
      have heq : EqOn (fun s => D s*max (-HG t s) 0) (fun _ => (0:ℝ)) (uIcc (t/4) t) := by
        intro s hs
        rw [uIcc_of_le (by linarith)] at hs
        have hnn : 0 ≤ HG t s := by
          rcases hs.2.lt_or_eq with h | h
          · exact (hsign s hs.1 h).le
          · rw [h, hHGt]
        simp only [max_eq_right (neg_nonpos.2 hnn), mul_zero]
      rw [intervalIntegral.integral_congr heq]
      simp
    rw [hz, add_zero]
    rfl
  have h3 : (∫ s in (0:ℝ)..t, P s*G (t-s)) = AG t - NG t := by
    rw [h1, ← h2, liEvenCrossActualClockGapPositiveHistoryCost, ← intervalIntegral.integral_sub
      (hcA.intervalIntegrable _ _) (hcN.intervalIntegrable _ _)]
    congr 1; funext s; rw [← mul_sub, max_zero_sub_max_neg_zero_eq_self]
  have hN : 0 ≤ NG t := intervalIntegral.integral_nonneg (by linarith) fun s hs =>
    mul_nonneg (hHist s ⟨hs.1, by linarith [hs.2]⟩) (le_max_right _ _)
  have hA : 0 < AG t := by
    have hfin := finite_liEvenCrossActualClockLogHistory_zeros (t/4) t
    obtain ⟨s0, hs0, hz0⟩ := ((Set.Ioo_infinite (show t/4 < t by linarith)).sdiff hfin).nonempty
    have hD0 : 0 < D s0 := lt_of_le_of_ne (hHist s0 ⟨by linarith [hs0.1], hs0.2.le⟩)
      fun h => hz0 ⟨Ioo_subset_Icc_self hs0, h.symm⟩
    have hf0 : 0 < D s0*max (HG t s0) 0 :=
      mul_pos hD0 (lt_max_of_lt_left (hsign s0 hs0.1.le hs0.2))
    obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (hcA.continuousAt.eventually (lt_mem_nhds hf0))
    set δ' := min δ (min (s0 - t/4) (t - s0)) with hδ'
    have hδ'0 : 0 < δ' := lt_min hδ (lt_min (by linarith [hs0.1]) (by linarith [hs0.2]))
    have hδ1 : δ' ≤ δ := min_le_left _ _
    have hδ2 : δ' ≤ s0 - t/4 := (min_le_right _ _).trans (min_le_left _ _)
    have hδ3 : δ' ≤ t - s0 := (min_le_right _ _).trans (min_le_right _ _)
    have hnn : ∀ s ∈ Icc (0:ℝ) t, 0 ≤ D s*max (HG t s) 0 := fun s hs =>
      mul_nonneg (hHist s hs) (le_max_right _ _)
    have hmid : 0 < ∫ s in (s0-δ'/2)..(s0+δ'/2), D s*max (HG t s) 0 :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hcA.intervalIntegrable _ _)
        (fun s hs => hδP (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]))
        (by linarith)
    have hleft : 0 ≤ ∫ s in (0:ℝ)..(s0-δ'/2), D s*max (HG t s) 0 :=
      intervalIntegral.integral_nonneg (by linarith [hs0.1]) fun s hs =>
        hnn s ⟨hs.1, by linarith [hs.2, hs0.2]⟩
    have hright : 0 ≤ ∫ s in (s0+δ'/2)..t, D s*max (HG t s) 0 :=
      intervalIntegral.integral_nonneg (by linarith) fun s hs =>
        hnn s ⟨by linarith [hs.1, hs0.1], hs.2⟩
    unfold liEvenCrossActualClockGapPositiveHistoryCost
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := s0-δ'/2)
      (hcA.intervalIntegrable _ _) (hcA.intervalIntegrable _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (a := s0-δ'/2) (b := s0+δ'/2)
      (hcA.intervalIntegrable _ _) (hcA.intervalIntegrable _ _)]
    linarith
  exact ⟨h1, h2, h3, hN, hA, by rw [h3]; linarith⟩

/-- **(F10b)**  For `t > 0` and `D ≥ 0` on `[0,t]`: `0 ≤ N_G(t) ≤ A G(t)t³e^{t/1200}/768`. -/
theorem liEvenCrossActualClockGapNegativeHistoryCost_bound {t : ℝ} (ht : 0 < t)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    0 ≤ NG t ∧ NG t ≤ Amass*G t*t^3*Real.exp (t/1200)/768 := by
  refine ⟨(liEvenCrossActualClockGapHistoryCost_decomposition ht hHist).2.2.2.1, ?_⟩
  have hA := xiShiftAbsoluteMass_pos 0
  have hGt := fc_G_nonneg ht.le
  have hcN : Continuous (fun s => D s*max (-HG t s) 0) :=
    fc_D_cont.mul ((fc_HG_cont t).neg.max continuous_const)
  have hbound : ∀ s ∈ Icc (0:ℝ) (t/4),
      D s*max (-HG t s) 0 ≤ (Amass*Real.exp (t/1200)/4*G t)*s^2 := by
    intro s hs
    have hst : 0 ≤ t - s := by linarith [hs.2]
    have hD := hHist s ⟨hs.1, by linarith [hs.2]⟩
    have hmax : max (-HG t s) 0 ≤ G t := by
      refine max_le ?_ hGt
      unfold liEvenCrossActualClockPrimitiveGapHistoryKernel
      have hG' := (liEvenCrossActualClockPrimitiveScoreGap_degree.2 (t-s) hst).1
      have hmono : G (t-s) ≤ G t := fc_G_mono hst ht.le (by linarith [hs.1])
      nlinarith [mul_nonneg hs.1 hG']
    have henv : D s ≤ Amass*s^2/4*Real.exp (t/1200) :=
      (fc_D_env hs.1).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hs.2]))
        (by positivity))
    calc D s*max (-HG t s) 0 ≤ (Amass*s^2/4*Real.exp (t/1200))*G t :=
          mul_le_mul henv hmax (le_max_right _ _) (by positivity)
      _ = (Amass*Real.exp (t/1200)/4*G t)*s^2 := by ring
  have hi : IntervalIntegrable (fun s : ℝ => (Amass*Real.exp (t/1200)/4*G t)*s^2) volume 0 (t/4) :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (by linarith) (hcN.intervalIntegrable (μ := volume) _ _)
    hi hbound
  rw [fc_poly_integral] at h
  unfold liEvenCrossActualClockGapNegativeHistoryCost
  calc _ ≤ _ := h
    _ = Amass*G t*t^3*Real.exp (t/1200)/768 := by ring

/-- **(F10c)**  For `t > 0`, `0 ≤ x ≤ t` and `D ≥ 0` on `[0,t]`:
`∫₀ˣ P(s)g(t-s) ds = xD(x)g(t-x) + A_g - L_g`, `A_g, L_g ≥ 0`,
`L_g ≤ ∫₀ˣ D(s)g(t-s) ds ≤ A g(t)x³e^{x/300}/12`. -/
theorem liEvenCrossActualClockReciprocalEarlyCost_balance {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x)
    (hxt : x ≤ t) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    (∫ s in (0:ℝ)..x, P s*g (t-s)) = x*D x*g (t-x) + Ag t x - Lg t x ∧
      0 ≤ Ag t x ∧ 0 ≤ Lg t x ∧ Lg t x ≤ (∫ s in (0:ℝ)..x, D s*g (t-s)) ∧
      (∫ s in (0:ℝ)..x, D s*g (t-s)) ≤ Amass*g t*x^3*Real.exp (x/300)/12 := by
  have hA := xiShiftAbsoluteMass_pos 0
  obtain ⟨-, -, -, hg⟩ := liEvenCrossActualClockReciprocalPrimitive_origin_nonneg
  have hgt := (hg t ht.le).1
  have hk : Continuous (fun s => s*deriv g (t-s) - g (t-s)) :=
    (continuous_id.mul (fc_gd_lag_cont t)).sub (fc_g_lag_cont t)
  have hcA : Continuous (fun s => D s*max (s*deriv g (t-s) - g (t-s)) 0) :=
    fc_D_cont.mul (hk.max continuous_const)
  have hcL : Continuous (fun s => D s*max (g (t-s) - s*deriv g (t-s)) 0) :=
    fc_D_cont.mul (((fc_g_lag_cont t).sub (continuous_id.mul (fc_gd_lag_cont t))).max continuous_const)
  have hHx : ∀ s ∈ Icc (0:ℝ) x, 0 ≤ D s := fun s hs => hHist s ⟨hs.1, hs.2.trans hxt⟩
  -- integration by parts
  have hu : ∀ s, HasDerivAt (fun s => s*D s) (D s + P s) s := by
    intro s
    have h := (hasDerivAt_id s).mul (hasDerivAt_liEvenCrossActualClockLogHistory s)
    simp only [id, one_mul, fc_mul_density] at h
    exact h
  have hv : ∀ s, HasDerivAt (fun s => g (t-s)) (-deriv g (t-s)) s := fun s =>
    ((contDiff_liEvenCrossActualClockReciprocalPrimitive.differentiable (by simp) (t-s)).hasDerivAt).comp_const_sub t s
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := x) (u := fun s => s*D s) (v := fun s => g (t-s))
    (u' := fun s => D s + P s) (v' := fun s => -deriv g (t-s))
    ((continuous_id.mul fc_D_cont).continuousOn) (fc_g_lag_cont t).continuousOn
    (fun s _ => hu s) (fun s _ => hv s)
    ((fc_D_cont.add fc_P_cont).intervalIntegrable _ _) ((fc_gd_lag_cont t).neg.intervalIntegrable _ _)
  beta_reduce at hIBP
  simp only [zero_mul, sub_zero] at hIBP
  have i1 : IntervalIntegrable (fun s => D s*g (t-s)) volume 0 x :=
    (fc_D_cont.mul (fc_g_lag_cont t)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s => P s*g (t-s)) volume 0 x :=
    (fc_P_cont.mul (fc_g_lag_cont t)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun s => s*D s*deriv g (t-s)) volume 0 x :=
    ((continuous_id.mul fc_D_cont).mul (fc_gd_lag_cont t)).intervalIntegrable _ _
  have e1 : (∫ s in (0:ℝ)..x, (D s + P s)*g (t-s)) =
      (∫ s in (0:ℝ)..x, D s*g (t-s)) + ∫ s in (0:ℝ)..x, P s*g (t-s) := by
    rw [← intervalIntegral.integral_add i1 i2]; congr 1; funext s; ring
  have e2 : (∫ s in (0:ℝ)..x, s*D s*-deriv g (t-s)) = -∫ s in (0:ℝ)..x, s*D s*deriv g (t-s) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext s; ring
  have e3 : Ag t x - Lg t x = (∫ s in (0:ℝ)..x, s*D s*deriv g (t-s)) - ∫ s in (0:ℝ)..x, D s*g (t-s) := by
    unfold liEvenCrossActualClockReciprocalEarlyPositiveCost liEvenCrossActualClockReciprocalEarlyNegativeCost
    rw [← intervalIntegral.integral_sub (hcA.intervalIntegrable _ _) (hcL.intervalIntegrable _ _),
      ← intervalIntegral.integral_sub i3 i1]
    congr 1; funext s
    rw [← mul_sub, show g (t-s) - s*deriv g (t-s) = -(s*deriv g (t-s) - g (t-s)) by ring,
      max_zero_sub_max_neg_zero_eq_self]
    ring
  rw [e1, e2] at hIBP
  have hAg : 0 ≤ Ag t x := intervalIntegral.integral_nonneg hx fun s hs =>
    mul_nonneg (hHx s hs) (le_max_right _ _)
  have hLg : 0 ≤ Lg t x := intervalIntegral.integral_nonneg hx fun s hs =>
    mul_nonneg (hHx s hs) (le_max_right _ _)
  have hLle : Lg t x ≤ ∫ s in (0:ℝ)..x, D s*g (t-s) := by
    refine intervalIntegral.integral_mono_on hx (hcL.intervalIntegrable _ _) i1 fun s hs => ?_
    have hr : 0 ≤ t - s := by linarith [hs.2]
    obtain ⟨hg0, hg', -⟩ := hg (t-s) hr
    exact mul_le_mul_of_nonneg_left (max_le (by nlinarith [mul_nonneg hs.1 hg']) hg0) (hHx s hs)
  have hDg : (∫ s in (0:ℝ)..x, D s*g (t-s)) ≤ Amass*g t*x^3*Real.exp (x/300)/12 := by
    have hb : ∀ s ∈ Icc (0:ℝ) x, D s*g (t-s) ≤ (Amass*Real.exp (x/300)/4*g t)*s^2 := by
      intro s hs
      have hr : 0 ≤ t - s := by linarith [hs.2]
      have hg0 := (hg (t-s) hr).1
      have hmono : g (t-s) ≤ g t := fc_g_mono hr ht.le (by linarith [hs.1])
      have henv : D s ≤ Amass*s^2/4*Real.exp (x/300) :=
        (fc_D_env hs.1).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hs.2]))
          (by positivity))
      calc D s*g (t-s) ≤ (Amass*s^2/4*Real.exp (x/300))*g t :=
            mul_le_mul henv hmono hg0 (by positivity)
        _ = _ := by ring
    have hi : IntervalIntegrable (fun s : ℝ => (Amass*Real.exp (x/300)/4*g t)*s^2) volume 0 x :=
      (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
    have h := intervalIntegral.integral_mono_on hx i1 hi hb
    rw [fc_poly_integral] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  refine ⟨by linarith [e3, hIBP], hAg, hLg, hLle, hDg⟩

/-- **(F11a)**  At a guarded zero, `I_U = W + 8C₁ + 16(N_G + L_g(ℓ)) - 16(A_G + A_g(ℓ))`,
`C₁ = tM_1(t) - 2M_2(t)`, and `W ≥ 0`. -/
theorem liEvenCrossActualClockFiniteGuardSourceCost_decomposition {t : ℝ} (ht : 20 < t)
    (hz : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    IU t = W t + 8*(t*M 1 t - 2*M 2 t) + 16*(NG t + Lg t (ell t)) - 16*(AG t + Ag t (ell t)) ∧
      0 ≤ W t := by
  have ht0 : 0 < t := by linarith
  have hgeo := liEvenCrossActualClockHistory_geometry ht0
  have hl0 : 0 ≤ ell t := hgeo.2.2.1.le
  have hlt : ell t ≤ t := by linarith [hgeo.2.2.2]
  have hdec := liEvenCrossActualClockScoreHistory_primitive_gap_decomposition ht hz hHist
  have hW := (liEvenCrossActualClockScoreHistory_signed_decomposition ht hz hHist).2.2
  have hG := (liEvenCrossActualClockGapHistoryCost_decomposition ht0 hHist).2.2.1
  have hE := (liEvenCrossActualClockReciprocalEarlyCost_balance ht0 hl0 hlt hHist).1
  have hgT : ∀ s : ℝ, (t-s)*(Tc ((t-s):ℂ)).re = g (t-s) := fun s => by
    rw [liEvenCrossActualClockReciprocalPrimitive, Complex.ofReal_sub]
  simp only [hgT] at hdec
  refine ⟨?_, hW⟩
  have hb : 16*ell t*D (ell t)*(t-ell t)*(Tc ((t-ell t):ℂ)).re = 16*ell t*D (ell t)*g (t-ell t) := by
    rw [← hgT (ell t)]; ring
  rw [hdec, hb, hG, hE]
  unfold liEvenCrossActualClockFiniteGuardWeightCost
  ring

/-- **(F11b–c)**  At a guarded zero, the strict actual upper bound
`I_U < W + 8C₁ + 16(N_G + L_g(ℓ)) ≤ W + 8C₁ + (A/48)G(t)t³e^{t/1200} + (4A/3)g(t)ℓ³e^{ℓ/300}`. -/
theorem liEvenCrossActualClockFiniteGuardSourceCost_upper {t : ℝ} (ht : 20 < t) (hz : D t = 0)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    IU t < W t + 8*(t*M 1 t - 2*M 2 t) + 16*(NG t + Lg t (ell t)) ∧
      W t + 8*(t*M 1 t - 2*M 2 t) + 16*(NG t + Lg t (ell t)) ≤
        W t + 8*(t*M 1 t - 2*M 2 t) + (Amass/48)*G t*t^3*Real.exp (t/1200) +
          (4*Amass/3)*g t*(ell t)^3*Real.exp (ell t/300) := by
  have ht0 : 0 < t := by linarith
  have hgeo := liEvenCrossActualClockHistory_geometry ht0
  have hl0 : 0 ≤ ell t := hgeo.2.2.1.le
  have hlt : ell t ≤ t := by linarith [hgeo.2.2.2]
  obtain ⟨hdec, -⟩ := liEvenCrossActualClockFiniteGuardSourceCost_decomposition ht hz hHist
  obtain ⟨-, -, -, -, hAG, -⟩ := liEvenCrossActualClockGapHistoryCost_decomposition ht0 hHist
  obtain ⟨-, hAg, -, hL1, hL2⟩ := liEvenCrossActualClockReciprocalEarlyCost_balance ht0 hl0 hlt hHist
  have hN := (liEvenCrossActualClockGapNegativeHistoryCost_bound ht0 hHist).2
  refine ⟨by rw [hdec]; linarith, ?_⟩
  nlinarith

/-- **(F11)**  At every positive clock, `W ≤ (A/4)∫_ℓ^t s²e^{s/300}(16t - 15s)T(t-s) ds`. -/
theorem liEvenCrossActualClockFiniteGuardWeightCost_bound {t : ℝ} (ht0 : 0 < t) :
    W t ≤ (Amass/4)*(∫ s in ell t..t, s^2*Real.exp (s/300)*(16*t-15*s)*(Tc ((t-s):ℂ)).re) := by
  have hgeo := liEvenCrossActualClockHistory_geometry ht0
  have hl0 : 0 < ell t := hgeo.2.2.1
  have hlt : ell t ≤ t := by linarith [hgeo.2.2.2]
  have hTc : Continuous (fun s : ℝ => (Tc ((t-s):ℂ)).re) :=
    Complex.continuous_re.comp ((continuous_iff_continuousAt.mpr fun z =>
      (liClockThetaScoreProfiles_analyticAt z).2.2.1.continuousAt).comp
      ((continuous_const (y := (t:ℂ))).sub Complex.continuous_ofReal))
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hlt
    (((fc_D_cont.mul (continuous_const.sub (continuous_const.mul continuous_id))).mul hTc).intervalIntegrable _ _)
    ((continuous_const.mul ((((continuous_pow 2).mul (Real.continuous_exp.comp
      (continuous_id.div_const 300))).mul (continuous_const.sub (continuous_const.mul continuous_id))).mul
      hTc)).intervalIntegrable _ _) fun s hs => ?_
  have hs0 : 0 ≤ s := hl0.le.trans hs.1
  have hT : 0 < (Tc ((t-s):ℂ)).re := by
    obtain ⟨θ, -, -, -, hθ⟩ := liClockThetaScoreProfiles_uniform_reserve
    rw [← Complex.ofReal_sub]; exact (hθ (t-s)).1
  have hk : 0 ≤ (16*t-15*s)*(Tc ((t-s):ℂ)).re := mul_nonneg (by linarith [hs.2]) hT.le
  have henv := fc_D_env hs0
  calc D s*(16*t-15*s)*(Tc ((t-s):ℂ)).re = D s*((16*t-15*s)*(Tc ((t-s):ℂ)).re) := by ring
    _ ≤ (Amass*s^2/4*Real.exp (s/300))*((16*t-15*s)*(Tc ((t-s):ℂ)).re) :=
        mul_le_mul_of_nonneg_right henv hk
    _ = Amass/4*(s^2*Real.exp (s/300)*(16*t-15*s)*(Tc ((t-s):ℂ)).re) := by ring

end
end RHTower
