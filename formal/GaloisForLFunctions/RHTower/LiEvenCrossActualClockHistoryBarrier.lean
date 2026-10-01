import GaloisForLFunctions.RHTower.LiEvenCrossActualClockHistoryRetention
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitiveVolterra
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

/-!
# Actual undamped clock history and its conditional crossing barrier

The origin-filled density is the literal primitive divided by clock, and the
history is its genuine oriented integral. The factor-one source Volterra law
produces the complete signed history coefficient. Actual short-clock positivity
provides a strict integral reserve at any hypothetical first zero. The final
receiver assumes the outside-correlation budget only at such zeros after clock 20;
this leaf does not establish that budget or unconditional history positivity.
-/

open Set MeasureTheory Filter Topology
namespace RHTower
noncomputable section
local notation "B" => liEvenCrossActualClockBorelKernel
local notation "K" => deriv liEvenCrossActualClockBorelKernel
local notation "K1" => deriv (deriv liEvenCrossActualClockBorelKernel)
local notation "P" => liEvenCrossActualClockPrimitive
local notation "F" => liEvenCrossActualClockResponse
local notation "e" => liEvenCrossActualClockHistoryScale
local notation "q" => (1051 / 2184 : ℝ)
local notation "A0" => xiShiftAbsoluteMass 0

/-- Literal primitive quotient; totalized division fills its origin by zero. -/
def liEvenCrossActualClockLogHistoryDensity (t : ℝ) : ℝ := P t / t
/-- Genuine oriented integral of the undamped primitive quotient. -/
def liEvenCrossActualClockLogHistory (t : ℝ) : ℝ :=
  ∫ s in 0..t, liEvenCrossActualClockLogHistoryDensity s
/-- Complete signed coefficient in the history Volterra identity. -/
def liEvenCrossActualClockHistoryCoefficient (t s : ℝ) : ℝ :=
  K (t-s) - s*K1 (t-s)
/-- Literal outside-history correlation, retaining its signed integrand. -/
def liEvenCrossActualClockHistoryOutsideCorrelation (t : ℝ) : ℝ :=
  ∫ s in liEvenCrossActualClockHistoryScale t..t,
    liEvenCrossActualClockLogHistory s * (s*K1 (t-s)-K (t-s))
local notation "Dens" => liEvenCrossActualClockLogHistoryDensity
local notation "D" => liEvenCrossActualClockLogHistory
local notation "H" => liEvenCrossActualClockHistoryCoefficient
local notation "Cout" => liEvenCrossActualClockHistoryOutsideCorrelation

private theorem hgt_hb_P_cont : Continuous P :=
  contDiff_liEvenCrossActualClockPrimitive.continuous
private theorem hgt_hb_F_zero : F 0 = 0 := by simp [liEvenCrossActualClockResponse]
private theorem hgt_hb_P_deriv_zero : deriv P 0 = 0 := by
  rw [(hasDerivAt_liEvenCrossActualClockPrimitive 0).deriv, hgt_hb_F_zero]
private theorem hgt_hb_density_dslope : Dens = dslope P 0 := by
  funext t
  by_cases ht : t = 0
  · subst t
    simp [liEvenCrossActualClockLogHistoryDensity, hgt_hb_P_deriv_zero]
  · rw [dslope_of_ne _ ht, slope_def_field]
    simp only [liEvenCrossActualClockLogHistoryDensity,
      liEvenCrossActualClockPrimitive_origin_even.1, sub_zero]

/-- The literal quotient is continuous on the entire real line, including zero. -/
theorem continuous_liEvenCrossActualClockLogHistoryDensity : Continuous Dens := by
  rw [hgt_hb_density_dslope]
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    exact continuousAt_dslope_same.mpr
      (hasDerivAt_liEvenCrossActualClockPrimitive 0).differentiableAt
  · exact (continuousAt_dslope_of_ne ht).mpr hgt_hb_P_cont.continuousAt

/-- Both the filled quotient and its genuine integral vanish at the origin. -/
theorem liEvenCrossActualClockLogHistory_origin : Dens 0 = 0 ∧ D 0 = 0 := by
  simp [liEvenCrossActualClockLogHistoryDensity, liEvenCrossActualClockLogHistory]

/-- Genuine FTC admission at every real clock. -/
theorem hasDerivAt_liEvenCrossActualClockLogHistory (t : ℝ) :
    HasDerivAt D (Dens t) t :=
  (continuous_liEvenCrossActualClockLogHistoryDensity.integral_hasStrictDerivAt 0 t).hasDerivAt

private theorem hgt_hb_D_cont : Continuous D :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_liEvenCrossActualClockLogHistory t).continuousAt
private theorem hgt_hb_density_mul (t : ℝ) : t * Dens t = P t := by
  by_cases ht : t = 0
  · subst t
    simp [liEvenCrossActualClockPrimitive_origin_even.1]
  · simp only [liEvenCrossActualClockLogHistoryDensity]
    field_simp
private theorem hgt_hb_K_cont : Continuous K :=
  contDiff_liEvenCrossActualClockBorelKernel.continuous_deriv (by simp)
private theorem hgt_hb_K1_cont : Continuous K1 := by
  have hc : ContDiff ℝ (2 : ℕ∞) B :=
    contDiff_liEvenCrossActualClockBorelKernel.of_le
      (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  exact (show ContDiff ℝ (1 : ℕ∞) K from hc.deriv').continuous_deriv_one
private theorem hgt_hb_K_deriv (t : ℝ) : HasDerivAt K (K1 t) t := by
  have hc : ContDiff ℝ (2 : ℕ∞) B :=
    contDiff_liEvenCrossActualClockBorelKernel.of_le
      (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hd : Differentiable ℝ K := hc.differentiable_deriv_two
  exact (hd t).hasDerivAt
private theorem hgt_hb_K_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ K t := by
  rcases lt_or_eq_of_le ht with ht | ht
  · exact (liEvenCrossActualClockBorel_deriv_pos ht).le
  · rw [← ht, liEvenCrossActualClockHistory_origin.1]
private theorem hgt_hb_H_cont (t : ℝ) : Continuous (H t) :=
  (hgt_hb_K_cont.comp (continuous_const.sub continuous_id)).sub
    (continuous_id.mul (hgt_hb_K1_cont.comp (continuous_const.sub continuous_id)))
private theorem hgt_hb_weight_deriv (t s : ℝ) :
    HasDerivAt (fun s : ℝ => s*K (t-s)) (H t s) s := by
  have hk : HasDerivAt (fun s : ℝ => K (t-s)) (-K1 (t-s)) s := by
    simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using
      (hgt_hb_K_deriv (t-s)).comp s ((hasDerivAt_id s).const_sub t)
  convert (hasDerivAt_id s).mul hk using 1 <;>
    first | rfl | (dsimp [liEvenCrossActualClockHistoryCoefficient]; ring)

/-- Exact history identity from the actual factor-one primitive Volterra law. -/
theorem liEvenCrossActualClockLogHistory_slope_volterra {t : ℝ} (ht : 0 ≤ t) :
    t * deriv D t = t*K t + ∫ s in 0..t, D s * H t s := by
  have hw : Continuous (fun s : ℝ => s*K (t-s)) :=
    continuous_id.mul (hgt_hb_K_cont.comp (continuous_const.sub continuous_id))
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hgt_hb_D_cont.continuousOn hw.continuousOn
    (fun s _ => hasDerivAt_liEvenCrossActualClockLogHistory s)
    (fun s _ => hgt_hb_weight_deriv t s)
    (continuous_liEvenCrossActualClockLogHistoryDensity.intervalIntegrable 0 t)
    ((hgt_hb_H_cont t).intervalIntegrable 0 t)
  have hleft : (∫ s in 0..t, Dens s * (s*K (t-s))) =
      ∫ s in 0..t, P s * K (t-s) := by
    congr 1
    funext s
    rw [show Dens s * (s*K (t-s)) = (s*Dens s)*K (t-s) by ring,
      hgt_hb_density_mul]
  -- The IBP orientation here is integral D * weight', not density * weight.
  have heq : (∫ s in 0..t, P s * K (t-s)) = -(∫ s in 0..t, D s * H t s) := by
    rw [liEvenCrossActualClockLogHistory_origin.2, sub_self,
      liEvenCrossActualClockHistory_origin.1] at hip
    simp only [mul_zero, zero_mul, sub_zero, zero_sub] at hip
    rw [hleft] at hip
    linarith
  rw [(hasDerivAt_liEvenCrossActualClockLogHistory t).deriv, hgt_hb_density_mul]
  have hp := liEvenCrossActualClockPrimitive_volterra ht
  rw [heq] at hp
  linarith

/-- The cumulative opposite coefficient is nonpositive only on the stated clock interval. -/
theorem liEvenCrossActualClockHistory_cumulative_negative {t x : ℝ}
    (ht : 0 ≤ t) (hx : 0 ≤ x) (hxt : x ≤ t) :
    (∫ s in 0..x, s*K1 (t-s)-K (t-s)) = -x*K (t-x) ∧
      (∫ s in 0..x, s*K1 (t-s)-K (t-s)) ≤ 0 := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => -(s*K (t-s)))
      (s*K1 (t-s)-K (t-s)) s := by
    convert (hgt_hb_weight_deriv t s).neg using 1 <;>
      first | rfl | (dsimp [liEvenCrossActualClockHistoryCoefficient]; ring)
  have hc : Continuous (fun s : ℝ => s*K1 (t-s)-K (t-s)) :=
    (continuous_id.mul (hgt_hb_K1_cont.comp (continuous_const.sub continuous_id))).sub
      (hgt_hb_K_cont.comp (continuous_const.sub continuous_id))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 x)
  have heq : (∫ s in 0..x, s*K1 (t-s)-K (t-s)) = -x*K (t-x) := by
    simpa only [zero_mul, neg_zero, sub_zero, neg_mul] using hi
  have htlag : 0 ≤ t-x := by
    rcases eq_or_lt_of_le ht with hz | _
    · rw [← hz] at hxt ⊢
      have hx0 : x = 0 := le_antisymm hxt hx
      simp only [hx0, sub_zero, le_refl]
    · exact sub_nonneg.mpr hxt
  exact ⟨heq, heq ▸ mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx)
    (hgt_hb_K_nonneg htlag)⟩

private theorem hgt_hb_F_margin {t : ℝ} (ht : 0 ≤ t) (ht20 : t ≤ 20) :
    q*A0*t ≤ F t := by
  have hw : t^2/16 ≤ (25 : ℝ) := by nlinarith
  have h := liEvenCrossActualCurrentClockSeries_ge_positive_margin (by positivity : 0 ≤ t^2/16) hw
  simpa only [liEvenCrossActualClockResponse, mul_comm t] using
    mul_le_mul_of_nonneg_right h ht
private theorem hgt_hb_P_margin {t : ℝ} (ht : 0 ≤ t) (ht20 : t ≤ 20) :
    q*A0*t^2/2 ≤ P t := by
  have hi := intervalIntegral.integral_mono_on (μ := volume) ht
    ((continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (continuous_liEvenCrossActualClockResponse.intervalIntegrable 0 t)
    (fun s hs => hgt_hb_F_margin hs.1 (hs.2.trans ht20))
  change (∫ s in 0..t, q*A0*s) ≤ P t at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have hr : (∫ s in 0..t, s) = t^2/2 := by
    convert (integral_pow (a := (0 : ℝ)) (b := t) 1) using 1 <;> norm_num
  rw [hr] at hi
  nlinarith
private theorem hgt_hb_density_margin {t : ℝ} (ht : 0 ≤ t) (ht20 : t ≤ 20) :
    q*A0*t/2 ≤ Dens t := by
  rcases lt_or_eq_of_le ht with ht | ht
  · have hp := hgt_hb_P_margin ht.le ht20
    apply (le_div_iff₀ ht).mpr
    change q*A0*t/2*t ≤ P t
    nlinarith
  · rw [← ht, liEvenCrossActualClockLogHistory_origin.1]
    norm_num
private theorem hgt_hb_D_margin {t : ℝ} (ht : 0 ≤ t) (ht20 : t ≤ 20) :
    q*A0*t^2/4 ≤ D t := by
  have hi := intervalIntegral.integral_mono_on (μ := volume) ht
    ((continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (continuous_liEvenCrossActualClockLogHistoryDensity.intervalIntegrable 0 t)
    (fun s hs => by
      have h := hgt_hb_density_margin hs.1 (hs.2.trans ht20)
      change (q*A0/2)*s ≤ Dens s
      nlinarith)
  change (∫ s in 0..t, (q*A0/2)*s) ≤ D t at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have hr : (∫ s in 0..t, s) = t^2/2 := by
    convert (integral_pow (a := (0 : ℝ)) (b := t) 1) using 1 <;> norm_num
  rw [hr] at hi
  nlinarith

/-- Exact actual-source positive corridor through clock 20. -/
theorem liEvenCrossActualClockLogHistory_local_corridor {t : ℝ}
    (ht : 0 ≤ t) (ht20 : t ≤ 20) :
    q*A0*t ≤ F t ∧ q*A0*t^2/2 ≤ P t ∧ q*A0*t^2/4 ≤ D t :=
  ⟨hgt_hb_F_margin ht ht20, hgt_hb_P_margin ht ht20, hgt_hb_D_margin ht ht20⟩

private theorem hgt_hb_e_guards {t : ℝ} (ht : 0 < t) :
    0 < e t ∧ e t < t ∧ 0 < K1 t ∧ 4*e t*K1 t = K t := by
  have hg := liEvenCrossActualClockHistory_geometry ht
  have heq : 4*e t*K1 t = K t := by
    unfold liEvenCrossActualClockHistoryScale
    field_simp [ne_of_gt hg.2.1]
  exact ⟨hg.2.2.1, by linarith [hg.2.2.2], hg.2.1, heq⟩
private theorem hgt_hb_tangent {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hst : s ≤ t) :
    K t - K (t-s) ≤ K1 t*s := by
  have hd : Differentiable ℝ K := fun u => (hgt_hb_K_deriv u).differentiableAt
  have h := (convex_Icc (0 : ℝ) t).image_sub_le_mul_sub_of_deriv_le
    hgt_hb_K_cont.continuousOn hd.differentiableOn
    (fun u hu => by
      rw [(hgt_hb_K_deriv u).deriv]
      have huc : u ∈ Icc 0 t := interior_subset hu
      exact liEvenCrossActualClockHistory_source_curvature.2 huc.1 ht huc.2)
    (t-s) ⟨sub_nonneg.mpr hst, sub_le_self t hs⟩ t ⟨ht, le_rfl⟩
    (sub_le_self t hs)
  simpa only [sub_sub_cancel] using h
private theorem hgt_hb_coefficient_tangent {t s : ℝ} (ht : 0 < t)
    (hs : 0 ≤ s) (hst : s ≤ t) : K t-2*s*K1 t ≤ H t s := by
  have h1 := hgt_hb_tangent ht.le hs hst
  have h2 := liEvenCrossActualClockHistory_source_curvature.2
    (sub_nonneg.mpr hst) ht.le (sub_le_self t hs)
  have h3 := mul_le_mul_of_nonneg_left h2 hs
  unfold liEvenCrossActualClockHistoryCoefficient
  nlinarith

/-- Positive coefficient bounds on the favorable window and its first half. -/
theorem liEvenCrossActualClockHistory_coefficient_lower {t s : ℝ}
    (ht : 0 < t) (hs : 0 ≤ s) (hse : s ≤ e t) :
    K t/2 ≤ H t s ∧ (s ≤ e t/2 → 3*K t/4 ≤ H t s) := by
  have hg := hgt_hb_e_guards ht
  have hb := hgt_hb_coefficient_tangent ht hs (hse.trans hg.2.1.le)
  have hm := mul_le_mul_of_nonneg_right hse hg.2.2.1.le
  constructor
  · nlinarith [hg.2.2.2]
  · intro hhalf
    have hmhalf := mul_le_mul_of_nonneg_right hhalf hg.2.2.1.le
    nlinarith [hg.2.2.2]

/-- Quantitative recent-history bound under explicit nonnegative-history admission. -/
theorem liEvenCrossActualClockHistory_recent_lower {t : ℝ} (ht : 0 < t)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    K t/2 * (∫ s in 0..e t, D s) +
      K t/4 * (∫ s in 0..e t/2, D s) ≤
        ∫ s in 0..e t, D s * H t s := by
  have hg := hgt_hb_e_guards ht
  have hc := hgt_hb_D_cont.mul (hgt_hb_H_cont t)
  have hhalf : e t/2 ≤ e t := by linarith [hg.1]
  have hi1 := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun s : ℝ => 3*K t/4*D s) (g := fun s : ℝ => D s*H t s)
    (by linarith : 0 ≤ e t/2)
    ((continuous_const.mul hgt_hb_D_cont).intervalIntegrable 0 (e t/2))
    (hc.intervalIntegrable 0 (e t/2))
    (fun s hs => by
      rw [mul_comm (3*K t/4)]
      exact mul_le_mul_of_nonneg_left
        ((liEvenCrossActualClockHistory_coefficient_lower ht hs.1 (hs.2.trans hhalf)).2 hs.2)
        (hHist s ⟨hs.1, (hs.2.trans hhalf).trans hg.2.1.le⟩))
  have hi2 := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun s : ℝ => K t/2*D s) (g := fun s : ℝ => D s*H t s) hhalf
    ((continuous_const.mul hgt_hb_D_cont).intervalIntegrable (e t/2) (e t))
    (hc.intervalIntegrable (e t/2) (e t))
    (fun s hs => by
      rw [mul_comm (K t/2)]
      exact mul_le_mul_of_nonneg_left
        (liEvenCrossActualClockHistory_coefficient_lower ht (by linarith [hg.1, hs.1]) hs.2).1
        (hHist s ⟨by linarith [hg.1, hs.1], hs.2.trans hg.2.1.le⟩))
  have hi1' : 3*K t/4*(∫ s in 0..e t/2, D s) ≤ ∫ s in 0..e t/2, D s*H t s := by
    simpa only [intervalIntegral.integral_const_mul] using hi1
  have hi2' : K t/2*(∫ s in e t/2..e t, D s) ≤ ∫ s in e t/2..e t, D s*H t s := by
    simpa only [intervalIntegral.integral_const_mul] using hi2
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hgt_hb_D_cont.intervalIntegrable 0 (e t/2))
    (hgt_hb_D_cont.intervalIntegrable (e t/2) (e t))
  have hprod := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (e t/2)) (hc.intervalIntegrable (e t/2) (e t))
  calc
    _ = 3*K t/4*(∫ s in 0..e t/2, D s) + K t/2*(∫ s in e t/2..e t, D s) := by
      rw [← hsum]
      ring
    _ ≤ (∫ s in 0..e t/2, D s*H t s) + (∫ s in e t/2..e t, D s*H t s) := add_le_add hi1' hi2'
    _ = _ := hprod

private theorem hgt_hb_r_pos {t : ℝ} (ht : 0 < t) : 0 < min (e t/2) 20 :=
  lt_min (by linarith [(hgt_hb_e_guards ht).1]) (by norm_num)
private theorem hgt_hb_qmass_pos : 0 < q*A0 :=
  mul_pos (by norm_num) (xiShiftAbsoluteMass_pos 0)
private theorem hgt_hb_reserve_pos {t : ℝ} (ht : 0 < t) :
    0 < q*A0*K t*(min (e t/2) 20)^3/48 := by
  have hk := liEvenCrossActualClockBorel_deriv_pos ht
  have hr := hgt_hb_r_pos ht
  have hq := hgt_hb_qmass_pos
  positivity

/-- The actual early corridor supplies a strictly positive recent integral reserve. -/
theorem liEvenCrossActualClockHistory_recent_origin_reserve {t : ℝ}
    (ht : 0 < t) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    let r := min (e t/2) 20
    q*A0*r^3/12 ≤ (∫ s in 0..e t/2, D s) ∧
      0 < (∫ s in 0..e t/2, D s) := by
  dsimp only
  let r := min (e t/2) 20
  have hr : 0 < r := hgt_hb_r_pos ht
  have hre : r ≤ e t/2 := min_le_left _ _
  have hr20 : r ≤ 20 := min_le_right _ _
  have hg := hgt_hb_e_guards ht
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun s : ℝ => (q*A0/4)*s^2) (g := D) hr.le
    ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 r)
    (hgt_hb_D_cont.intervalIntegrable 0 r)
    (fun s hs => by
      have hh := hgt_hb_D_margin hs.1 (hs.2.trans hr20)
      nlinarith)
  have hi' : q*A0*r^3/12 ≤ ∫ s in 0..r, D s := by
    change (∫ s in 0..r, (q*A0/4)*s^2) ≤ _ at hi
    rw [intervalIntegral.integral_const_mul, integral_pow] at hi
    norm_num at hi
    nlinarith
  have hj : 0 ≤ ∫ s in r..e t/2, D s :=
    intervalIntegral.integral_nonneg hre (fun s hs => hHist s
      ⟨hr.le.trans hs.1, hs.2.trans (by linarith [hg.2.1])⟩)
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hgt_hb_D_cont.intervalIntegrable 0 r) (hgt_hb_D_cont.intervalIntegrable r (e t/2))
  have hbound : q*A0*r^3/12 ≤ ∫ s in 0..e t/2, D s := by linarith
  have hp : 0 < q*A0*r^3/12 := by
    have hq := hgt_hb_qmass_pos
    positivity
  exact ⟨hbound, hp.trans_le hbound⟩

private theorem hgt_hb_history_split {t : ℝ} :
    (∫ s in 0..t, D s*H t s) = (∫ s in 0..e t, D s*H t s) - Cout t := by
  have hc := hgt_hb_D_cont.mul (hgt_hb_H_cont t)
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (e t)) (hc.intervalIntegrable (e t) t)
  change (∫ s in 0..e t, D s*H t s) + (∫ s in e t..t, D s*H t s) =
    (∫ s in 0..t, D s*H t s) at hsum
  have hneg : (∫ s in e t..t, D s*H t s) = -Cout t := by
    unfold liEvenCrossActualClockHistoryOutsideCorrelation
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext s
    unfold liEvenCrossActualClockHistoryCoefficient
    ring
  rw [hneg] at hsum
  linarith

/-- Complete signed-history slope bound with the exact early reserve. -/
theorem liEvenCrossActualClockHistory_quantitative_slope {t : ℝ}
    (ht : 0 < t) (hzero : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    let r := min (e t/2) 20
    t*K t + K t/2*(∫ s in 0..e t, D s) - Cout t +
      q*A0*K t*r^3/48 ≤ t*deriv D t := by
  dsimp only
  have _ := hzero
  have hnear := liEvenCrossActualClockHistory_recent_lower ht hHist
  have hr := (liEvenCrossActualClockHistory_recent_origin_reserve ht hHist).1
  have hmul := mul_le_mul_of_nonneg_left hr ((liEvenCrossActualClockBorel_deriv_pos ht).le : 0 ≤ K t)
  rw [liEvenCrossActualClockLogHistory_slope_volterra ht.le, hgt_hb_history_split]
  nlinarith

/-- A nonstrict outside budget forces a strict positive slope reserve at a zero. -/
theorem liEvenCrossActualClockHistory_strict_slope_of_outside_budget {t : ℝ}
    (ht : 0 < t) (hzero : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s)
    (hM15 : Cout t ≤ t*K t + K t/2*(∫ s in 0..e t, D s)) :
    let r := min (e t/2) 20
    0 < q*A0*K t*r^3/48 ∧ q*A0*K t*r^3/48 ≤ t*deriv D t := by
  dsimp only
  exact ⟨hgt_hb_reserve_pos ht, by
    have h := liEvenCrossActualClockHistory_quantitative_slope ht hzero hHist
    dsimp only at h
    linarith⟩

/-- Any nonpositive-slope crossing must exceed the budget by the explicit reserve. -/
theorem liEvenCrossActualClockHistory_necessary_crossing_defect {t : ℝ}
    (ht : 0 < t) (hzero : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s)
    (hd : deriv D t ≤ 0) :
    let r := min (e t/2) 20
    t*K t + K t/2*(∫ s in 0..e t, D s) + q*A0*K t*r^3/48 ≤ Cout t := by
  dsimp only
  have h := liEvenCrossActualClockHistory_quantitative_slope ht hzero hHist
  dsimp only at h
  have hh := mul_nonpos_of_nonneg_of_nonpos ht.le hd
  linarith

private theorem hgt_hb_D_early_pos {t : ℝ} (ht : 0 < t) (ht20 : t ≤ 20) : 0 < D t := by
  have hp : 0 < q*A0*t^2/4 := by
    have hq := hgt_hb_qmass_pos
    positivity
  exact hp.trans_le (hgt_hb_D_margin ht.le ht20)

private theorem hgt_hb_first_zero {T : ℝ} (hT : 20 ≤ T) (hDT : D T ≤ 0) :
    ∃ t : ℝ, 20 < t ∧ t ≤ T ∧ D t = 0 ∧
      (∀ s ∈ Icc 0 t, 0 ≤ D s) ∧ deriv D t ≤ 0 := by
  have h20 : 0 < D 20 := hgt_hb_D_early_pos (by norm_num) le_rfl
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hT hgt_hb_D_cont.continuousOn
    (show (0 : ℝ) ∈ Icc (D T) (D 20) from ⟨hDT, h20.le⟩)
  let Z : Set ℝ := Icc 20 T ∩ D ⁻¹' {0}
  have hZc : IsCompact Z := isCompact_Icc.inter_right
    (isClosed_singleton.preimage hgt_hb_D_cont)
  have hZn : Z.Nonempty := ⟨z, hz, hz0⟩
  obtain ⟨t, htZ, htmin⟩ := hZc.exists_isMinOn hZn continuous_id.continuousOn
  have ht0 : D t = 0 := htZ.2
  have ht20 : 20 < t := by
    have htle : 20 ≤ t := htZ.1.1
    by_contra h
    have heq : t = 20 := le_antisymm (le_of_not_gt h) htle
    subst t
    linarith
  have ht : 0 < t := by linarith
  have hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s := by
    intro s hs
    by_cases hs20 : s ≤ 20
    · exact (hgt_hb_D_margin hs.1 hs20).trans' (by
        have hq := hgt_hb_qmass_pos
        positivity)
    · by_cases hst : s < t
      · by_contra hDs
        have hDs' : D s ≤ 0 := (lt_of_not_ge hDs).le
        obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' (le_of_not_ge hs20)
          hgt_hb_D_cont.continuousOn (show (0 : ℝ) ∈ Icc (D s) (D 20) from ⟨hDs', h20.le⟩)
        have hwZ : w ∈ Z := ⟨⟨hw.1, hw.2.trans (hst.le.trans htZ.1.2)⟩, hw0⟩
        have hh : t ≤ w := htmin hwZ
        linarith [hw.2]
      · have heq : s = t := le_antisymm hs.2 (le_of_not_gt hst)
        simpa only [heq, ht0] using (le_rfl : (0 : ℝ) ≤ 0)
  have hderiv : deriv D t ≤ 0 := by
    have hlo : Ioi (-t) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by linarith)
    have hlo' : ∀ᶠ h : ℝ in 𝓝[<] (0 : ℝ), -t < h := nhdsWithin_le_nhds hlo
    have hleft : ∀ᶠ h : ℝ in 𝓝[<] (0 : ℝ), h < 0 := self_mem_nhdsWithin
    have hslope : ∀ᶠ h : ℝ in 𝓝[<] (0 : ℝ),
        h⁻¹ • (D (t+h)-D t) ≤ 0 := by
      filter_upwards [hlo', hleft] with h hlow hneg
      have hD := hHist (t+h) ⟨by linarith, by linarith⟩
      simpa only [smul_eq_mul, ht0, sub_zero] using
        mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hneg.le) hD
    exact le_of_tendsto
      ((hasDerivAt_liEvenCrossActualClockLogHistory t).differentiableAt.hasDerivAt.tendsto_slope_zero_left)
      hslope
  exact ⟨t, ht20, htZ.1.2, ht0, hHist, hderiv⟩

/-- Conditional continuation: budgets only at nonnegative-history first zeros after 20 suffice. -/
theorem liEvenCrossActualClockLogHistory_pos_of_first_zero_budget
    (hM15 : ∀ t : ℝ, 20 < t → D t = 0 →
      (∀ s ∈ Icc 0 t, 0 ≤ D s) →
      Cout t ≤ t*K t + K t/2*(∫ s in 0..e t, D s)) :
    ∀ t : ℝ, 0 < t → 0 < D t := by
  intro T hT
  by_contra h
  have hDT : D T ≤ 0 := le_of_not_gt h
  have hT20 : 20 < T := by
    by_contra hh
    exact (not_lt_of_ge hDT) (hgt_hb_D_early_pos hT (le_of_not_gt hh))
  obtain ⟨t, ht20, _, ht0, hHist, hd⟩ := hgt_hb_first_zero hT20.le hDT
  have ht : 0 < t := by linarith
  have hstrict := liEvenCrossActualClockHistory_strict_slope_of_outside_budget
    ht ht0 hHist (hM15 t ht20 ht0 hHist)
  dsimp only at hstrict
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos ht.le hd
  linarith [hstrict.1, hstrict.2]

end
end RHTower
