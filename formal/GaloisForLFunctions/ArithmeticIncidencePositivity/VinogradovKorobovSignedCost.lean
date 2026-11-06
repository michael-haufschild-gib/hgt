import GaloisForLFunctions.ArithmeticIncidencePositivity.ReflectedPrimePolarAllocation
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovPrimeNumberTheorem
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheVinogradovKorobovBand

/-!
# Vinogradov–Korobov saving for the full signed prime–pole cost

The exact Abel pairing controls the reflected prime–pole cost by the weighted
Chebyshev defect on the full correlation interval. Below its midpoint the
exponential weight pays; above it the Vinogradov–Korobov prime number theorem
pays. Half the saving absorbs the interval length.

The resulting estimate is uniform over all odd compactly supported `C¹` tests,
with the pole-tilted Sobolev energy `¼∫F² + ∫F′²`. The scale is
`(2r)^(3/5) (log(2r))^(-5/3)` for `r ≥ 2`, regularized at smaller apertures.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The Vinogradov–Korobov scale at the full correlation horizon, regularized at small apertures. -/
def incidenceVKScale (r : ℝ) : ℝ := vkScale (Real.exp (max (2*r) 4))

private theorem incidenceVKScale_eq {r : ℝ} (hr : 2 ≤ r) :
    incidenceVKScale r = vkScale (Real.exp (2*r)) := by
  rw [incidenceVKScale, max_eq_left (by linarith)]

/-- Above the regularization threshold, the saving retains the full logarithmic loss. -/
theorem incidenceVKScale_of_two_le {r : ℝ} (hr : 2 ≤ r) :
    incidenceVKScale r = (2*r)^((3:ℝ)/5) * Real.log (2*r)^(-((5:ℝ)/3)) := by
  rw [incidenceVKScale_eq hr, vkScale, Real.log_exp]

private theorem incidenceVKScale_le (r : ℝ) : incidenceVKScale r ≤ max (2*r) 4 := by
  set L := max (2*r) 4
  have hL4 : 4 ≤ L := le_max_right _ _
  have hL1 : 1 ≤ L := by linarith only [hL4]
  have hL0 : 0 < L := by linarith only [hL4]
  have hlog : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have he := Real.exp_one_lt_d9
    linarith only [he, hL4]
  have hp : L ^ ((3:ℝ)/5) ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (3:ℝ)/5 ≤ 1)
  have hq : Real.log L ^ (-((5:ℝ)/3)) ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<1) hlog
        (by norm_num : -((5:ℝ)/3) ≤ 0)
  change vkScale (Real.exp L) ≤ L
  rw [vkScale, Real.log_exp]
  exact (mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hL0.le _)).trans (by simpa using hp)

private theorem eventually_incidenceVKScale_bounds :
    ∀ᶠ r : ℝ in atTop, 2 * Real.sqrt r ≤ vkKappa * incidenceVKScale r ∧
      vkKappa * incidenceVKScale r ≤ 2*r := by
  have ht : Tendsto (fun r : ℝ => Real.exp (2*r)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [ht.eventually (eventually_vk_conditions one_pos 0),
    eventually_ge_atTop (2:ℝ)] with r h hr
  rcases h with ⟨_, _, _, _, hlo, hhi, _⟩
  rw [log_vkHeight, Real.log_exp, ← incidenceVKScale_eq hr] at hlo hhi
  exact ⟨(mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith only [hr]))
    (by norm_num)).trans hlo, hhi⟩

private theorem exists_abs_twoPoleDefect_le_exp :
    ∃ K > 0, ∀ s : ℝ, 0 ≤ s → |chebyshevTwoPoleDefect s| ≤ K * Real.exp s := by
  obtain ⟨c, hc, K, hK, h⟩ := exists_abs_chebyshevTwoPoleDefect_mul_exp_le
  refine ⟨K, hK, fun s hs => ?_⟩
  have hb := h s hs 0 le_rfl (by norm_num) s ⟨hs,le_rfl⟩
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, sub_zero, one_mul] at hb
  exact hb.trans (mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg s))))

private theorem exists_eventually_weighted_twoPoleDefect_le_vk :
    ∃ K > 0, ∀ᶠ r : ℝ in atTop, ∀ s ∈ Icc (0:ℝ) (2*r),
      |chebyshevTwoPoleDefect s| * Real.exp (-s/2) ≤
        K * Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 54)) := by
  obtain ⟨B, hB, hpnt⟩ := exists_abs_sum_vonMangoldt_sub_self_vk_rate
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.mp (Real.tendsto_exp_atTop.eventually hpnt)
  obtain ⟨K₀,hK₀,htriv⟩ := exists_abs_twoPoleDefect_le_exp
  refine ⟨B+K₀+1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop s₀, eventually_ge_atTop (4:ℝ),
    eventually_incidenceVKScale_bounds] with r hr₀ hr4 hrB
  intro s hs
  have hr2 : 2 ≤ r := by linarith only [hr4]
  have hsave : vkKappa * incidenceVKScale r / 54 ≤ r/2 := by linarith only [hrB.2,hr4]
  have hE0 : 1 ≤ Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 54)) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith only [hsave,hr4])
  -- Early lags are paid by their exponential weight; late lags retain the PNT saving.
  rcases le_or_gt s r with hsr | hrs
  · have he : Real.exp (s/2) ≤ Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 54)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith only [hsave,hsr])
    calc |chebyshevTwoPoleDefect s| * Real.exp (-s/2)
        ≤ (K₀ * Real.exp s) * Real.exp (-s/2) :=
          mul_le_mul_of_nonneg_right (htriv s hs.1) (Real.exp_pos _).le
      _ = K₀ * Real.exp (s/2) := by
        rw [mul_assoc, ← Real.exp_add, show s + -s/2 = s/2 by ring]
      _ ≤ K₀ * (Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 54))) :=
        mul_le_mul_of_nonneg_left he hK₀.le
      _ ≤ (B+K₀+1) * Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 54)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith only [hB]) (by positivity)
  · have hP := hs₀ s (hr₀.trans hrs.le)
    have hP' : |Real.exp s - Chebyshev.psi (Real.exp s)| ≤
        B * Real.exp s * Real.exp (-(vkKappa * vkScale (Real.exp s) / 24)) := by
      rw [Chebyshev.psi_eq_sum_range, abs_sub_comm]
      exact hP
    have hcomp : 4/9 * incidenceVKScale r ≤ vkScale (Real.exp s) := by
      rw [incidenceVKScale_eq hr2]
      apply four_ninths_mul_vkScale_le
      · rw [Real.log_exp]; linarith only [hr4,hrs]
      · rw [Real.log_exp, Real.log_exp]; linarith only [hrs,hr4]
      · simpa only [Real.log_exp] using hs.2
    have hrate : Real.exp (-(vkKappa * vkScale (Real.exp s) / 24)) ≤
        Real.exp (-(vkKappa * incidenceVKScale r / 54)) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hcomp vkKappa_pos.le
      linarith only [hm]
    have hlin : |s-1| ≤ Real.exp (s/2) := by
      have hq := Real.quadratic_le_exp_of_nonneg (by linarith only [hr4,hrs] : 0 ≤ s/2)
      have hpoly : s+1 ≤ Real.exp (s/2) := by nlinarith only [hq, hr4,hrs]
      rw [abs_le]
      constructor <;> linarith only [hpoly,hr4,hrs]
    have hdef : chebyshevTwoPoleDefect s =
        (Real.exp s - Chebyshev.psi (Real.exp s)) + (s-1) := by
      rw [chebyshevTwoPoleDefect_eq_error_add, chebyshevError, lagChebyshev_eq_chebyshevPsi]
    have hwhole : |chebyshevTwoPoleDefect s| ≤
        B * Real.exp s * Real.exp (-(vkKappa * vkScale (Real.exp s) / 24)) + Real.exp (s/2) := by
      rw [hdef]
      exact (abs_add_le _ _).trans (add_le_add hP' hlin)
    have hexp : Real.exp (s/2) ≤ Real.exp r := Real.exp_le_exp.mpr (by linarith only [hs.2])
    have hcancel : Real.exp (s/2) * Real.exp (-s/2) = 1 := by
      rw [← Real.exp_add, show s/2 + -s/2 = 0 by ring, Real.exp_zero]
    calc |chebyshevTwoPoleDefect s| * Real.exp (-s/2)
        ≤ (B * Real.exp s * Real.exp (-(vkKappa * vkScale (Real.exp s) / 24)) + Real.exp (s/2)) *
            Real.exp (-s/2) := mul_le_mul_of_nonneg_right hwhole (Real.exp_pos _).le
      _ = B * Real.exp (s/2) * Real.exp (-(vkKappa * vkScale (Real.exp s) / 24)) + 1 := by
        rw [add_mul,hcancel]
        have he : Real.exp s * Real.exp (-s/2) = Real.exp (s/2) := by
          rw [← Real.exp_add, show s + -s/2 = s/2 by ring]
        rw [show B * Real.exp s * Real.exp (-(vkKappa * vkScale (Real.exp s) / 24)) * Real.exp (-s/2) =
          B * (Real.exp s * Real.exp (-s/2)) * Real.exp (-(vkKappa * vkScale (Real.exp s) / 24)) by ring, he]
      _ ≤ B * Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 54)) + 1 :=
        add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hexp hB) hrate
          (Real.exp_pos _).le (by positivity)) le_rfl
      _ ≤ (B+K₀+1) * Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 54)) := by
        have hpos : 0 ≤ K₀ * (Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 54))) := by positivity
        nlinarith only [hE0,hpos]

private theorem exists_eventually_integral_twoPoleDefect_le_vk :
    ∃ K > 0, ∀ᶠ r : ℝ in atTop,
      (∫ s in Ioc (0:ℝ) (2*r), 2 * Real.exp (-s/2) * |chebyshevTwoPoleDefect s|) ≤
        K * Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 108)) := by
  obtain ⟨K,hK,hbound⟩ := exists_eventually_weighted_twoPoleDefect_le_vk
  refine ⟨4*K*5832, by positivity, ?_⟩
  filter_upwards [hbound, eventually_incidenceVKScale_bounds,
    eventually_gt_atTop (0:ℝ)] with r hB hR hr
  have hS : 0 < 2*r := by linarith only [hr]
  set M := 2*K*Real.exp r*Real.exp (-(vkKappa * incidenceVKScale r / 54))
  have hpoint : ∀ s ∈ Ioc (0:ℝ) (2*r),
      2 * Real.exp (-s/2) * |chebyshevTwoPoleDefect s| ≤ M := by
    intro s hs
    have hb := mul_le_mul_of_nonneg_left (hB s ⟨hs.1.le,hs.2⟩) (by norm_num : (0:ℝ)≤2)
    dsimp only [M]
    nlinarith only [hb]
  have hi := setIntegral_mono_on (integrableOn_Ioc_exp_mul_abs_chebyshevTwoPoleDefect hS)
    (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc hpoint
  have hconst : (∫ _s in Ioc (0:ℝ) (2*r), M) = 2*r*M := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hS.le, smul_eq_mul]
  have hquad : r * Real.exp (-(Real.sqrt r/54)) ≤ 5832 := by
    have hq := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ Real.sqrt r/54)
    have hsq : (Real.sqrt r/54)^2 = r/2916 := by rw [div_pow, Real.sq_sqrt hr.le]; norm_num
    rw [hsq] at hq
    have hp : r ≤ 5832 * Real.exp (Real.sqrt r/54) := by
      nlinarith only [hq, Real.sqrt_nonneg r]
    have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-(Real.sqrt r/54))).le
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hm
    exact hm
  have hsave : r * Real.exp (-(vkKappa * incidenceVKScale r / 108)) ≤ 5832 := by
    refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hr.le).trans hquad
    linarith only [hR.1]
  -- One half of the saving pays the integration length, leaving the other half intact.
  have hsplit : Real.exp (-(vkKappa * incidenceVKScale r / 54)) =
      Real.exp (-(vkKappa * incidenceVKScale r / 108)) *
        Real.exp (-(vkKappa * incidenceVKScale r / 108)) := by
    rw [← Real.exp_add,
      show -(vkKappa * incidenceVKScale r / 108) + -(vkKappa * incidenceVKScale r / 108) =
        -(vkKappa * incidenceVKScale r / 54) by ring]
  calc (∫ s in Ioc (0:ℝ) (2*r), 2 * Real.exp (-s/2) * |chebyshevTwoPoleDefect s|)
      ≤ 2*r*M := hi.trans hconst.le
    _ = 4*K*(r*Real.exp (-(vkKappa * incidenceVKScale r / 108))) *
        (Real.exp r*Real.exp (-(vkKappa * incidenceVKScale r / 108))) := by
      dsimp only [M]
      rw [hsplit]
      ring
    _ ≤ 4*K*5832 * Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 108)) := by
      have hm := mul_le_mul_of_nonneg_left hsave (by positivity : 0 ≤ 4*K)
      have hm' := mul_le_mul_of_nonneg_right hm
        (by positivity : 0 ≤ Real.exp r*Real.exp (-(vkKappa * incidenceVKScale r / 108)))
      simpa only [mul_assoc] using hm'

private theorem exists_abs_reflectedPrimePolarCost_le_vk_firstOrder :
    ∃ K > 0, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 1 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      |reflectedPrimePolarCost F r| ≤
        K * Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 108)) *
          ((∫ x, F x^2) + (1/2) * ∫ x, deriv F x^2) := by
  obtain ⟨K₁,hK₁,hev⟩ := exists_eventually_integral_twoPoleDefect_le_vk
  obtain ⟨R,hR⟩ := eventually_atTop.mp hev
  obtain ⟨c₀,hc₀,K₀,hK₀,hold⟩ := exists_abs_reflectedPrimePolarCost_le_exp_sub_sqrt_mul_sobolev
  set B := max (2*R) 4
  set K := K₁ + K₀ * Real.exp (vkKappa*B/108)
  refine ⟨K, by positivity, fun r F hr hF hFc hodd hsupp => ?_⟩
  set S := (∫ x, F x^2) + (1/2) * ∫ x, deriv F x^2
  have hS : 0 ≤ S := add_nonneg (integral_nonneg fun _ => sq_nonneg _)
    (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
  -- The bounded aperture range is absorbed into one universal constant.
  rcases le_or_gt R r with hrR | hrR
  · have hcost := abs_reflectedPrimePolarCost_le_chebyshevTwoPoleDefect_L1_mul_sobolev
      hF hFc hodd hr hsupp
    have hmain := hcost.trans (mul_le_mul_of_nonneg_right (hR r hrR) hS)
    refine hmain.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by
          dsimp only [K]
          exact le_add_of_nonneg_right (by positivity) : K₁ ≤ K)
          (Real.exp_pos _).le) (Real.exp_pos _).le) hS
  · have hQ : incidenceVKScale r ≤ B := (incidenceVKScale_le r).trans
      (max_le_max (by linarith only [hrR]) le_rfl)
    have hfac : 1 ≤ Real.exp (vkKappa*B/108) * Real.exp (-(vkKappa * incidenceVKScale r / 108)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have hm := mul_le_mul_of_nonneg_left hQ vkKappa_pos.le
      linarith only [hm]
    have hsmall := hold r F hr hF hFc hodd hsupp
    have hdrop : Real.exp (-c₀*Real.sqrt r) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc₀.le) (Real.sqrt_nonneg r))
    have hbudget : K₀ * Real.exp r * S ≤
        (K₀ * Real.exp (vkKappa*B/108)) * Real.exp r *
          Real.exp (-(vkKappa * incidenceVKScale r / 108)) * S := by
      have hm := mul_le_mul_of_nonneg_left hfac
        (by positivity : 0 ≤ K₀*Real.exp r*S)
      nlinarith only [hm]
    calc |reflectedPrimePolarCost F r|
        ≤ K₀ * Real.exp r * Real.exp (-c₀*Real.sqrt r) * S := hsmall
      _ ≤ K₀ * Real.exp r * S := by
        exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) hdrop) hS
      _ ≤ (K₀ * Real.exp (vkKappa*B/108)) * Real.exp r *
          Real.exp (-(vkKappa * incidenceVKScale r / 108)) * S := hbudget
      _ ≤ K * Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 108)) * S := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith only [hK₁])
              (Real.exp_pos _).le) (Real.exp_pos _).le) hS

/-- The full signed prime–pole cost has the Vinogradov–Korobov saving, uniformly over odd tests. -/
theorem exists_abs_reflectedPrimePolarCost_le_vinogradovKorobov_mul_sobolev :
    ∃ K > 0, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 1 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      |reflectedPrimePolarCost F r| ≤
        K * Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 108)) *
          ((1/4) * (∫ x, F x^2) + ∫ x, deriv F x^2) := by
  obtain ⟨K,hK,hbound⟩ := exists_abs_reflectedPrimePolarCost_le_vk_firstOrder
  refine ⟨4*K, by positivity, fun r F hr hF hFc hodd hsupp => ?_⟩
  have hb := hbound r F hr hF hFc hodd hsupp
  have hS : (∫ x, F x^2) + (1/2) * ∫ x, deriv F x^2 ≤
      4 * ((1/4) * (∫ x, F x^2) + ∫ x, deriv F x^2) := by
    have hd : 0 ≤ ∫ x, deriv F x^2 := integral_nonneg fun _ => sq_nonneg _
    linarith only [hd]
  have hm := mul_le_mul_of_nonneg_left hS
    (by positivity : 0 ≤ K * Real.exp r * Real.exp (-(vkKappa * incidenceVKScale r / 108)))
  exact hb.trans (by nlinarith only [hm])

#print axioms exists_abs_reflectedPrimePolarCost_le_vinogradovKorobov_mul_sobolev
#print axioms incidenceVKScale_of_two_le

end GaloisForLFunctions.ArithmeticIncidencePositivity
