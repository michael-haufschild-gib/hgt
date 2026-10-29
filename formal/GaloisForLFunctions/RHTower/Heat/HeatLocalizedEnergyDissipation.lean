import GaloisForLFunctions.RHTower.Heat.HeatLocalizedEnergyEvolution
import GaloisForLFunctions.RHTower.Heat.HeatLocalizedZeroObservables
import GaloisForLFunctions.HTGeometry.ForwardRegularIntervalComparison
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Dissipation of localized heat-zero energy

The actual zero velocities, conjugate-pair dissipation and real-symmetric
exterior field give a flux bound with no inverse-gap loss. Continuous truncated
counts carry this estimate through collisions; bounded convergence recovers
the full nonreal count. The upper right slope retains that count even at the
unheated endpoint.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.DeBruijn

/-- Nonnegative cutoffs have zero derivative wherever the cutoff vanishes. -/
private theorem heat_cutoff_derivative_eq_zero {w v : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (v x) x) (hwn : ∀ x, 0 ≤ w x)
    {x : ℝ} (hx : w x = 0) : v x = 0 := by
  have hmin : IsLocalMin w x := Filter.Eventually.of_forall fun y => by
    rw [hx]
    exact hwn y
  exact hmin.hasDerivAt_eq_zero (hw x)

private theorem heatLocalizedVerticalEnergy_derivWithinAt_of_simple
    {t X : ℝ} (ht : 0 < t) {w v : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (v x) x)
    (hsupp : ∀ x, 1 ≤ |x| → w x = 0)
    {S : Finset ℂ}
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0) :
    HasDerivWithinAt (heatLocalizedVerticalEnergy X w)
      (∑ a ∈ S, (v (a.re - X) * a.im^2 *
          (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).re +
        2 * w (a.re - X) * a.im *
          (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im))
      (Ici t) t := by
  let D : ℝ := ∑ a ∈ S, (v (a.re - X) * a.im^2 *
      (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).re +
    2 * w (a.re - X) * a.im *
      (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im)
  have h := heatLocalizedVerticalEnergy_hasDerivWithinAt_of_simple ht hw hsupp hpacket hsimple
  have hg : HasDerivWithinAt (fun r : ℝ => r - t) 1 (Ici t) t :=
    ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
  have h' : HasDerivWithinAt (fun h => heatLocalizedVerticalEnergy X w (t + h))
      D (Ici 0) (t - t) := by simpa only [D, sub_self] using h
  have hc := h'.comp (h := fun r : ℝ => r - t) t hg (fun r hr => by
    change t ≤ r at hr
    change 0 ≤ r - t
    exact sub_nonneg.mpr hr)
  have hfun : (fun r => heatLocalizedVerticalEnergy X w (t + (r - t))) =
      heatLocalizedVerticalEnergy X w := by
    funext r
    congr 1
    ring
  change HasDerivWithinAt (fun r => heatLocalizedVerticalEnergy X w (t + (r - t)))
    (D * 1) (Ici t) t at hc
  rw [hfun, mul_one] at hc
  exact hc

/-- The actual simple-zero drift is the finite reciprocal-field work plus the
exterior-field work, with no unproved zero-velocity input. -/
private theorem heatLocalizedVerticalEnergy_deriv_eq_packet_drift
    {t X : ℝ} (ht : 0 < t) {w v : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (v x) x) (hwn : ∀ x, 0 ≤ w x)
    (hsupp : ∀ x, 1 ≤ |x| → w x = 0)
    {S : Finset ℂ} {Q : ℂ → ℂ}
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0)
    (hQ : ∀ z, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      AnalyticAt ℂ Q z ∧ (riemannHeat t z ≠ 0 →
        logDeriv (riemannHeat t) z =
          (∑ b ∈ S, (zeroMult (riemannHeat t) b : ℂ) / (z - b)) + Q z)) :
    (∑ a ∈ S, (v (a.re - X) * a.im^2 *
        (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).re +
      2 * w (a.re - X) * a.im *
        (deriv (deriv (riemannHeat t)) a / deriv (riemannHeat t) a).im)) =
    heatPacketPairDrift S (fun x => w (x - X)) (fun x => v (x - X)) +
      heatPacketExteriorDrift S (fun x => w (x - X)) (fun x => v (x - X))
        (fun z => if |z.re - X| < 1 then Q z else 0) := by
  classical
  rw [heatPacketPairDrift_eq_field, heatPacketExteriorDrift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  by_cases hr : |a.re - X| < 1
  · have hv := simple_heat_zero_velocity_eq_exterior ht hpacket hQ
      ((hpacket a).mp ha).1 (hsimple a ha) hr
    have hsum : (∑ b ∈ S.erase a, (zeroMult (riemannHeat t) b : ℂ) / (a - b)) =
        ∑ b ∈ S, (a - b)⁻¹ := by
      calc
        _ = ∑ b ∈ S.erase a, (a - b)⁻¹ := by
          refine Finset.sum_congr rfl fun b hb => ?_
          have hbS := (Finset.mem_erase.mp hb).2
          rw [zeroMult_riemannHeat_eq_one ht.le ((hpacket b).mp hbS).1 (hsimple b hbS),
            Nat.cast_one, one_div]
        _ = _ := by
          simpa only [sub_self, inv_zero, add_zero] using
            (Finset.sum_erase_add S (fun b : ℂ => (a - b)⁻¹) ha)
    rw [hsum] at hv
    simp only [hv, if_pos hr, Complex.mul_re, Complex.mul_im,
      show (2 : ℂ).re = (2 : ℝ) from rfl, show (2 : ℂ).im = (0 : ℝ) from rfl,
      zero_mul, sub_zero, add_zero, Complex.add_re, Complex.add_im]
    ring
  · have hw0 := hsupp _ (le_of_not_gt hr)
    have hv0 := heat_cutoff_derivative_eq_zero hw hwn hw0
    simp only [if_neg hr, hw0, hv0, zero_mul, mul_zero, zero_add]

/-- At a simple time the actual local energy obeys the uniform flux estimate.
All packet and field inputs are the outputs of the heat cofactor theorem. -/
private theorem heatLocalizedVerticalEnergy_simple_drift_le
    {t X M V W K : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hW : 0 ≤ W) (hK : 0 ≤ K) {w v : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (v x) x)
    (hwn : ∀ x, 0 ≤ w x) (hwW : ∀ x, w x ≤ W)
    (hvV : ∀ x, |v x| ≤ V)
    (hv : ∀ x x', |v x - v x'| ≤ M * |x - x'|)
    (hsupp : ∀ x, 1 ≤ |x| → w x = 0)
    {S : Finset ℂ} {Q : ℂ → ℂ}
    (hpacket : ∀ a, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2)
    (hcount : ((∑ a ∈ S, zeroMult (riemannHeat t) a : ℕ) : ℝ) ≤ K)
    (hsimple : ∀ a ∈ S, deriv (riemannHeat t) a ≠ 0)
    (hQ : ∀ z, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
      AnalyticAt ℂ Q z ∧ ‖Q z‖ ≤ K ∧
        |(Q z).im| ≤ K * |z.im| ∧
        (riemannHeat t z ≠ 0 → logDeriv (riemannHeat t) z =
          (∑ a ∈ S, (zeroMult (riemannHeat t) a : ℂ) / (z - a)) + Q z)) :
    ∃ D : ℝ, HasDerivWithinAt (heatLocalizedVerticalEnergy X w) D (Ici t) t ∧
      D ≤ -2 * heatLocalizedNonrealCount X w t +
        (2 * M + 2 * V + 4 * W) * K * heatLocalizedVerticalEnergy X heatOuterCutoff t := by
  classical
  refine ⟨_, heatLocalizedVerticalEnergy_derivWithinAt_of_simple ht hw hsupp hpacket hsimple, ?_⟩
  let ws := fun x => w (x - X)
  let vs := fun x => v (x - X)
  let Qs := fun z : ℂ => if |z.re - X| < 1 then Q z else 0
  have hws (x : ℝ) : HasDerivAt ws (vs x) x := by
    simpa only [ws, vs, Function.comp_def, mul_one] using
      (hw (x - X)).comp (h := fun r : ℝ => r - X) x ((hasDerivAt_id x).sub_const X)
  have hvs (x x' : ℝ) : |vs x - vs x'| ≤ M * |x - x'| := by
    simpa only [vs, sub_sub_sub_cancel_right] using hv (x - X) (x' - X)
  have hconj : ∀ a ∈ S, starRingEnd ℂ a ∈ S := by
    intro a ha
    obtain ⟨hz, hr⟩ := (hpacket a).mp ha
    apply (hpacket (starRingEnd ℂ a)).mpr
    refine ⟨?_, by simpa only [Complex.conj_re] using hr⟩
    rw [riemannHeat_conj ht.le, hz, map_zero]
  have hQr (a : ℂ) (ha : a ∈ S) : |(Qs a).re| ≤ K := by
    by_cases hr : |a.re - X| < 1
    · simpa only [Qs, if_pos hr] using (Complex.abs_re_le_norm (Q a)).trans
        (hQ a hr.le (abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg ht.le
          ((hpacket a).mp ha).1)).2.1
    · simpa only [Qs, if_neg hr, Complex.zero_re, abs_zero] using hK
  have hQi (a : ℂ) (ha : a ∈ S) : |(Qs a).im| ≤ K * |a.im| := by
    by_cases hr : |a.re - X| < 1
    · simpa only [Qs, if_pos hr] using
        (hQ a hr.le (abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg ht.le
          ((hpacket a).mp ha).1)).2.2.1
    · simpa only [Qs, if_neg hr, Complex.zero_im, abs_zero] using
        mul_nonneg hK (abs_nonneg a.im)
  have hm (a : ℂ) (ha : a ∈ S) : zeroMult (riemannHeat t) a = 1 :=
    zeroMult_riemannHeat_eq_one ht.le ((hpacket a).mp ha).1 (hsimple a ha)
  have hcard : (S.card : ℝ) ≤ K := by
    have he : (∑ a ∈ S, zeroMult (riemannHeat t) a : ℕ) = S.card := by
      calc
        _ = ∑ _ ∈ S, 1 := Finset.sum_congr rfl hm
        _ = _ := by simp only [Finset.sum_const, smul_eq_mul, mul_one]
    rwa [he] at hcount
  have hn : heatPacketNonrealWeight S ws = heatLocalizedNonrealCount X w t := by
    rw [heatLocalizedNonrealCount, heatLocalizedZeroObservable_eq_sum ht.le w _ hsupp S
      (fun z hz hr => (hpacket z).mpr ⟨hz, by linarith only [hr]⟩)]
    unfold heatPacketNonrealWeight
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hm a ha, Nat.cast_one, one_mul]
    by_cases hy : a.im = 0 <;> simp only [ws, hy, if_true, if_false, mul_zero, mul_one]
  have hflux := heatPacket_drift_le hconj hM hK hV hws hvs
    (fun x => hwn (x - X)) (fun a _ => hwW (a.re - X))
    (fun a _ => hvV (a.re - X)) hQr hQi
  rw [hn] at hflux
  rw [heatLocalizedVerticalEnergy_deriv_eq_packet_drift ht hw hwn hsupp hpacket hsimple
    (fun z hr hi => ⟨(hQ z hr hi).1, (hQ z hr hi).2.2.2⟩)]
  have hEn : 0 ≤ heatPacketVerticalEnergy S := by
    unfold heatPacketVerticalEnergy
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcoeff : 2 * M * (S.card : ℝ) + (2 * V + 4 * W) * K ≤
      (2 * M + 2 * V + 4 * W) * K := by
    have h := mul_le_mul_of_nonneg_left hcard (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
    nlinarith only [h]
  have houter := heatPacketVerticalEnergy_le_outer ht.le
    (fun a ha => (hpacket a).mp ha)
  have hc0 : 0 ≤ (2 * M + 2 * V + 4 * W) * K := by positivity
  exact hflux.trans (add_le_add le_rfl
    ((mul_le_mul_of_nonneg_right hcoeff hEn).trans
      (mul_le_mul_of_nonneg_left houter hc0)))

/-- The truncated dissipation estimate integrates from time zero through all
collisions. The exterior constants are independent of the cutoff and the time interval. -/
private theorem heatLocalizedVerticalEnergy_truncated_evolution
    {C X₀ : ℝ} (hC : 0 < C) (hX₀ : 4096 ≤ X₀)
    (hcofactor : ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 → t * Real.log X ≤ 1 →
      ∃ (S : Finset ℂ) (Q : ℂ → ℂ),
        (∀ a : ℂ, a ∈ S ↔ riemannHeat t a = 0 ∧ |a.re - X| ≤ 2) ∧
        ((∑ a ∈ S, zeroMult (riemannHeat t) a : ℕ) : ℝ) ≤ C * Real.log X ∧
        (∀ x : ℝ, (Q x).im = 0) ∧
        ∀ z : ℂ, |z.re - X| ≤ 1 → |z.im| ≤ 1 / 2 →
          AnalyticAt ℂ Q z ∧ ‖Q z‖ ≤ C * Real.log X ∧
          ‖deriv Q z‖ ≤ C * Real.log X ∧
          |(Q z).im| ≤ C * Real.log X * |z.im| ∧
          (riemannHeat t z ≠ 0 → logDeriv (riemannHeat t) z =
            (∑ a ∈ S, (zeroMult (riemannHeat t) a : ℂ) / (z - a)) + Q z))
    {X M V W a b : ℝ} (hX : X₀ ≤ X) (hM : 0 ≤ M) (hV : 0 ≤ V) (hW : 0 ≤ W)
    {w v : ℝ → ℝ} (hw : ∀ x, HasDerivAt w (v x) x)
    (hwn : ∀ x, 0 ≤ w x) (hwW : ∀ x, w x ≤ W)
    (hvV : ∀ x, |v x| ≤ V) (hv : ∀ x x', |v x - v x'| ≤ M * |x - x'|)
    (hsupp : ∀ x, 1 ≤ |x| → w x = 0)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 8) (hbX : b * Real.log X ≤ 1)
    (n : ℕ) :
    heatLocalizedVerticalEnergy X w b - heatLocalizedVerticalEnergy X w a +
        2 * (∫ s in a..b, heatLocalizedZeroObservable X w (heatNonrealTruncation n) s) ≤
      (2 * M + 2 * V + 4 * W) * (C * Real.log X) *
        ∫ s in a..b, heatLocalizedVerticalEnergy X heatOuterCutoff s := by
  have hL : 0 ≤ Real.log X := (Real.log_pos (by linarith only [hX, hX₀])).le
  have hK : 0 ≤ C * Real.log X := mul_nonneg hC.le hL
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun x => (hw x).continuousAt
  have hcompact := hasCompactSupport_heat_cutoff hsupp
  let A := (2 * M + 2 * V + 4 * W) * (C * Real.log X)
  let E := fun s => heatLocalizedVerticalEnergy X heatOuterCutoff (max s 0)
  let N := fun s => heatLocalizedZeroObservable X w (heatNonrealTruncation n) (max s 0)
  have hEc : Continuous E := continuous_heatLocalizedZeroObservable_clamped
    continuous_heatOuterCutoff (by fun_prop : Continuous (fun y : ℝ => y^2))
    hasCompactSupport_heatOuterCutoff X
  have hNc : Continuous N := continuous_heatLocalizedZeroObservable_clamped hwc
    (continuous_heatNonrealTruncation n) hcompact X
  have hf : ContinuousOn (heatLocalizedVerticalEnergy X w) (Icc a b) :=
    (continuousOn_heatLocalizedVerticalEnergy hwc hcompact X).mono fun s hs => ha.trans hs.1
  have hB : Continuous (fun s => A * E s - 2 * N s) :=
    (continuous_const.mul hEc).sub (continuous_const.mul hNc)
  have hineq := sub_le_integral_of_forward_deriv_le hab hf hB (by
      intro x hx
      have hx0 : 0 < x := ha.trans_lt hx.1
      obtain ⟨δ, hδ, hregular⟩ := exists_compact_simple_riemannHeat_zeros_forward
        hx0 (isCompact_closedBall (X : ℂ) 3)
      refine ⟨δ, hδ, ?_⟩
      intro s hs hsb
      have hs0 : 0 < s := hx0.trans hs.1
      have hs8 : s ≤ 1 / 8 := hsb.le.trans hb
      have hsX : s * Real.log X ≤ 1 :=
        (mul_le_mul_of_nonneg_right hsb.le hL).trans hbX
      obtain ⟨S, Q, hpacket, hcount, _, hQ⟩ := hcofactor X hX s hs0.le hs8 hsX
      have hsimple (z : ℂ) (hz : z ∈ S) : deriv (riemannHeat s) z ≠ 0 := by
        obtain ⟨hzero, hr⟩ := (hpacket z).mp hz
        have hi := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg hs0.le hzero
        have hzball : z ∈ closedBall (X : ℂ) 3 := by
          rw [mem_closedBall, dist_eq_norm]
          have hn := Complex.norm_le_abs_re_add_abs_im (z - (X : ℂ))
          simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at hn
          linarith only [hn, hr, hi]
        exact (hregular s hs.1 hs.2 z hzball hzero).1
      obtain ⟨D, hD, hDb⟩ := heatLocalizedVerticalEnergy_simple_drift_le hs0 hM hV hW hK
        hw hwn hwW hvV hv hsupp hpacket hcount hsimple
        (fun z hr hi => ⟨(hQ z hr hi).1, (hQ z hr hi).2.1,
          (hQ z hr hi).2.2.2.1, (hQ z hr hi).2.2.2.2⟩)
      have hN := heatLocalizedZeroObservable_mono (X := X) hs0.le hcompact hwn
        (heatNonrealTruncation_le_indicator n)
      refine ⟨D, hD, ?_⟩
      dsimp only [A, E, N]
      rw [max_eq_left hs0.le]
      change heatLocalizedZeroObservable X w (heatNonrealTruncation n) s ≤
        heatLocalizedNonrealCount X w s at hN
      linarith only [hDb, hN])
  have hEI : IntervalIntegrable E volume a b := hEc.intervalIntegrable a b
  have hNI : IntervalIntegrable N volume a b := hNc.intervalIntegrable a b
  have hEint : (∫ s in a..b, E s) = ∫ s in a..b,
      heatLocalizedVerticalEnergy X heatOuterCutoff s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact congrArg (heatLocalizedVerticalEnergy X heatOuterCutoff)
      (max_eq_left (ha.trans hs.1))
  have hNint : (∫ s in a..b, N s) = ∫ s in a..b,
      heatLocalizedZeroObservable X w (heatNonrealTruncation n) s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact congrArg (heatLocalizedZeroObservable X w (heatNonrealTruncation n))
      (max_eq_left (ha.trans hs.1))
  rw [intervalIntegral.integral_sub (hEI.const_mul A) (hNI.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hEint, hNint] at hineq
  linarith only [hineq]

/-- Localized heat-zero energy pays the full nonreal count, with horizontal
and exterior flux charged only to nearby squared heights. This holds through
arbitrary collisions and includes the unheated endpoint. -/
theorem exists_uniform_heatLocalizedVerticalEnergy_evolution :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ (w v : ℝ → ℝ) (M V W : ℝ),
        0 ≤ M → 0 ≤ V → 0 ≤ W →
        (∀ x, HasDerivAt w (v x) x) →
        (∀ x, 0 ≤ w x) → (∀ x, w x ≤ W) → (∀ x, |v x| ≤ V) →
        (∀ x x', |v x - v x'| ≤ M * |x - x'|) →
        (∀ x, 1 ≤ |x| → w x = 0) →
        ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 / 8 → b * Real.log X ≤ 1 →
          IntervalIntegrable (heatLocalizedNonrealCount X w) volume a b ∧
          heatLocalizedVerticalEnergy X w b - heatLocalizedVerticalEnergy X w a +
              2 * (∫ s in a..b, heatLocalizedNonrealCount X w s) ≤
            (2 * M + 2 * V + 4 * W) * (C * Real.log X) *
              ∫ s in a..b, heatLocalizedVerticalEnergy X heatOuterCutoff s := by
  obtain ⟨C, hC, X₀, hX₀, hcofactor⟩ := exists_uniform_riemannHeat_exterior_force
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro X hX w v M V W hM hV hW hw hwn hwW hvV hv hsupp a b ha hab hb hbX
  have hL : 0 ≤ Real.log X := (Real.log_pos (by linarith only [hX, hX₀])).le
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun x => (hw x).continuousAt
  have hcompact := hasCompactSupport_heat_cutoff hsupp
  let N := fun n s => heatLocalizedZeroObservable X w (heatNonrealTruncation n) (max s 0)
  have hNc (n : ℕ) : Continuous (N n) := continuous_heatLocalizedZeroObservable_clamped hwc
    (continuous_heatNonrealTruncation n) hcompact X
  have hpacket (s : ℝ) (hs : s ∈ Icc a b) : ∃ S : Finset ℂ,
      (∀ z, z ∈ S ↔ riemannHeat s z = 0 ∧ |z.re - X| ≤ 2) ∧
      ((∑ z ∈ S, zeroMult (riemannHeat s) z : ℕ) : ℝ) ≤ C * Real.log X := by
    obtain ⟨S, Q, hS, hcount, _⟩ := hcofactor X hX s (ha.trans hs.1)
      (hs.2.trans hb) ((mul_le_mul_of_nonneg_right hs.2 hL).trans hbX)
    exact ⟨S, hS, hcount⟩
  have hlim (s : ℝ) (hs : s ∈ Icc a b) :
      Tendsto (fun n => N n s) atTop (𝓝 (heatLocalizedNonrealCount X w s)) := by
    have hs0 := ha.trans hs.1
    obtain ⟨S, hS, _⟩ := hpacket s hs
    have he := eventually_heatLocalizedZeroObservable_eq_nonrealCount hs0 w hsupp S
      (fun z hz hr => (hS z).mpr ⟨hz, by linarith only [hr]⟩)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    simpa only [N, max_eq_left hs0] using hn.symm
  have hbound (n : ℕ) (s : ℝ) (hs : s ∈ Icc a b) :
      |N n s| ≤ W * (C * Real.log X) := by
    have hs0 := ha.trans hs.1
    obtain ⟨S, hS, hcount⟩ := hpacket s hs
    have hu (y : ℝ) : 0 ≤ heatNonrealTruncation n y ∧ heatNonrealTruncation n y ≤ 1 := by
      refine ⟨heatNonrealTruncation_nonneg n y,
        (heatNonrealTruncation_le_indicator n y).trans ?_⟩
      split_ifs <;> norm_num
    dsimp only [N]
    rw [max_eq_left hs0, abs_of_nonneg (heatLocalizedZeroObservable_nonneg hwn
      (heatNonrealTruncation_nonneg n))]
    exact heatLocalizedZeroObservable_le_packet_degree hs0 hW (fun x => ⟨hwn x, hwW x⟩)
      hu hsupp S (fun z hz hr => (hS z).mpr ⟨hz, by linarith only [hr]⟩) hcount
  have hconv := tendsto_intervalIntegral_of_continuous_bounded hab hNc hbound hlim
  have hNint (n : ℕ) : (∫ s in a..b, N n s) =
      ∫ s in a..b, heatLocalizedZeroObservable X w (heatNonrealTruncation n) s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact congrArg (heatLocalizedZeroObservable X w (heatNonrealTruncation n))
      (max_eq_left (ha.trans hs.1))
  refine ⟨?_, ?_⟩
  · exact intervalIntegrable_of_continuous_bounded_limit hab hNc hbound hlim
  · apply le_of_tendsto (tendsto_const_nhds.add (tendsto_const_nhds.mul hconv))
    filter_upwards [] with n
    rw [hNint]
    exact heatLocalizedVerticalEnergy_truncated_evolution hC hX₀ hcofactor hX hM hV hW
      hw hwn hwW hvV hv hsupp ha hab hb hbX n


/-- The upper right slope has full conjugate dissipation even at a multiple
zero or at heat time zero. Only nearby vertical energy pays the flux error. -/
theorem exists_uniform_heatLocalizedVerticalEnergy_right_slope :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ (w v : ℝ → ℝ) (M V W : ℝ),
        0 ≤ M → 0 ≤ V → 0 ≤ W →
        (∀ x, HasDerivAt w (v x) x) →
        (∀ x, 0 ≤ w x) → (∀ x, w x ≤ W) → (∀ x, |v x| ≤ V) →
        (∀ x x', |v x - v x'| ≤ M * |x - x'|) →
        (∀ x, 1 ≤ |x| → w x = 0) →
        ∀ t : ℝ, 0 ≤ t → t < 1 / 8 → t * Real.log X < 1 →
          ∀ r : ℝ,
            -2 * heatLocalizedNonrealCount X w t +
                (2 * M + 2 * V + 4 * W) * (C * Real.log X) *
                  heatLocalizedVerticalEnergy X heatOuterCutoff t < r →
            ∀ᶠ h in 𝓝[>] (0 : ℝ),
              (heatLocalizedVerticalEnergy X w (t + h) -
                heatLocalizedVerticalEnergy X w t) / h ≤ r := by
  obtain ⟨C, hC, X₀, hX₀, hcofactor⟩ := exists_uniform_riemannHeat_exterior_force
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro X hX w v M V W hM hV hW hw hwn hwW hvV hv hsupp t ht ht8 htX r hr
  have hL : 0 < Real.log X := Real.log_pos (by linarith only [hX, hX₀])
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun x => (hw x).continuousAt
  have hcompact := hasCompactSupport_heat_cutoff hsupp
  obtain ⟨S, Q, hpacket, _, _⟩ := hcofactor X hX t ht ht8.le htX.le
  obtain ⟨n, hn⟩ := (eventually_heatLocalizedZeroObservable_eq_nonrealCount ht w hsupp S
    (fun z hz hzX => (hpacket z).mpr ⟨hz, by linarith only [hzX]⟩)).exists
  let A := (2 * M + 2 * V + 4 * W) * (C * Real.log X)
  let E := fun s => heatLocalizedVerticalEnergy X heatOuterCutoff (max s 0)
  let N := fun s => heatLocalizedZeroObservable X w (heatNonrealTruncation n) (max s 0)
  have hEc : Continuous E := continuous_heatLocalizedZeroObservable_clamped
    continuous_heatOuterCutoff (by fun_prop : Continuous (fun y : ℝ => y^2))
    hasCompactSupport_heatOuterCutoff X
  have hNc : Continuous N := continuous_heatLocalizedZeroObservable_clamped hwc
    (continuous_heatNonrealTruncation n) hcompact X
  have hB : Continuous (fun s => A * E s - 2 * N s) :=
    (continuous_const.mul hEc).sub (continuous_const.mul hNc)
  apply eventually_right_slope_le_of_integral_majorant hB
  · dsimp only [A, E, N]
    rw [max_eq_left ht, hn]
    linarith only [hr]
  · let δ := min (1 / 8 - t) ((1 - t * Real.log X) / Real.log X)
    have hδ : 0 < δ := lt_min (sub_pos.mpr ht8) (div_pos (sub_pos.mpr htX) hL)
    refine ⟨δ, hδ, ?_⟩
    intro h hh
    have hth : t ≤ t + h := le_add_of_nonneg_right hh.1.le
    have hth8 : t + h ≤ 1 / 8 := by
      have hb := hh.2.trans_le (min_le_left _ _)
      linarith only [hb]
    have hthX : (t + h) * Real.log X ≤ 1 := by
      have hb := hh.2.trans_le (min_le_right _ _)
      have hm := (lt_div_iff₀ hL).mp hb
      nlinarith only [hm]
    have he := heatLocalizedVerticalEnergy_truncated_evolution hC hX₀ hcofactor hX hM hV hW
      hw hwn hwW hvV hv hsupp ht hth hth8 hthX n
    have hEcI : IntervalIntegrable E volume t (t + h) := hEc.intervalIntegrable t (t + h)
    have hNcI : IntervalIntegrable N volume t (t + h) := hNc.intervalIntegrable t (t + h)
    have hEI : (∫ s in t..(t + h), E s) =
        ∫ s in t..(t + h), heatLocalizedVerticalEnergy X heatOuterCutoff s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hth] at hs
      exact congrArg (heatLocalizedVerticalEnergy X heatOuterCutoff)
        (max_eq_left (ht.trans hs.1))
    have hNI : (∫ s in t..(t + h), N s) =
        ∫ s in t..(t + h), heatLocalizedZeroObservable X w (heatNonrealTruncation n) s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hth] at hs
      exact congrArg (heatLocalizedZeroObservable X w (heatNonrealTruncation n))
        (max_eq_left (ht.trans hs.1))
    rw [intervalIntegral.integral_sub (hEcI.const_mul A) (hNcI.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hEI, hNI]
    linarith only [he]

end RHTower.DeBruijn

#print axioms RHTower.DeBruijn.exists_uniform_heatLocalizedVerticalEnergy_evolution
#print axioms RHTower.DeBruijn.exists_uniform_heatLocalizedVerticalEnergy_right_slope
