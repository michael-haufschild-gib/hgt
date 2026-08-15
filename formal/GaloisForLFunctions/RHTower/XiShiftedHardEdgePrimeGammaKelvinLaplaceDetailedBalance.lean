import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeGammaKelvinMellinCriticalPhase
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter MeasureTheory Polynomial Set

noncomputable section

namespace RHTower

private theorem routeUIntegral_pow_mul_exp_neg_mul_Ioi
    (k : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-(c * t))) =
      k.factorial / c ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := c) (by positivity) hc
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [h, Real.Gamma_nat_eq_factorial]
  rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  simp only [one_div, inv_pow]
  ring

private theorem routeUIntegrableOn_pow_mul_exp_neg_mul_Ioi
    (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(c * t))) (Ioi 0) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := c) (by positivity) hc
  have hne :
      (∫ t : ℝ in Ioi 0,
        t ^ ((k : ℝ) + 1 - 1) * Real.exp (-(c * t))) ≠ 0 := by
    rw [h]
    positivity
  have hint : IntegrableOn
      (fun t : ℝ =>
        t ^ ((k : ℝ) + 1 - 1) * Real.exp (-(c * t))) (Ioi 0) :=
    Integrable.of_integral_ne_zero hne
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using hint

/-- The complete Route U Laplace filter applied to one Kelvin-paired cross orbit. -/
def routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent
    (a : ℝ) (P : Polynomial ℝ) (weight : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ),
    t ^ (2 * routeUHardEdgeKelvinDegree a P) * Real.exp (-(a ^ 2 * t)) *
      routeUHardEdgeKelvinPairedCrossCurrent a P t weight x

/-- Separate the heat dependence of the actual Kelvin-paired current from its zero-heat cross
state. -/
theorem routeUHardEdgeKelvinPairedCrossCurrent_eq_zeroHeatDifference
    {a x t : ℝ} (ha : 0 < a) (hx : 0 < x) (P : Polynomial ℝ)
    (weight : ℝ → ℝ) :
    routeUHardEdgeKelvinPairedCrossCurrent a P t weight x =
      routeUHardEdgeKelvinCrossDensity a P 0 x *
        (Real.exp (-(t * x ^ 2)) * weight x -
          (a ^ 2 / x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P + 1) *
            Real.exp (-(t * (a ^ 2 / x) ^ 2)) * weight (a ^ 2 / x)) := by
  rw [routeUHardEdgeKelvinPairedCrossCurrent_eq_weightDefect ha hx P]
  rw [routeUHardEdgeKelvinCrossDensity, routeUHardEdgeKelvinCrossDensity]
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  have hexp : Real.exp (-(t * x ^ 2)) *
      Real.exp (-(t * ((a ^ 2 / x) ^ 2 - x ^ 2))) =
      Real.exp (-(t * (a ^ 2 / x) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show 2 * routeUHardEdgeKelvinDegree a P + 1 =
      2 * routeUHardEdgeKelvinDegree a P + 1 by rfl]
  rw [← hexp]
  ring

/-- Exact Kelvin--Laplace detailed balance: the source-matched heat filter removes the entire
Kelvin cocycle and leaves only the source-weight commutator. -/
theorem routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent_eq
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (P : Polynomial ℝ)
    (weight : ℝ → ℝ) :
    routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent a P weight x =
      ((2 * routeUHardEdgeKelvinDegree a P).factorial : ℝ) *
        routeUHardEdgeKelvinCrossDensity a P 0 x /
          (a ^ 2 + x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P + 1) *
            (weight x - weight (a ^ 2 / x)) := by
  let d := routeUHardEdgeKelvinDegree a P
  let y := a ^ 2 / x
  let r := a ^ 2 / x ^ 2
  have hcx : 0 < a ^ 2 + x ^ 2 := by positivity
  have hcy : 0 < a ^ 2 + y ^ 2 := by positivity
  have hr : 0 < r := div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hx)
  have hden : a ^ 2 + y ^ 2 = r * (a ^ 2 + x ^ 2) := by
    dsimp only [y, r]
    field_simp [ne_of_gt hx]
    ring
  have hfun : (fun t : ℝ =>
      t ^ (2 * d) * Real.exp (-(a ^ 2 * t)) *
        routeUHardEdgeKelvinPairedCrossCurrent a P t weight x) =
      fun t : ℝ =>
        routeUHardEdgeKelvinCrossDensity a P 0 x * weight x *
            (t ^ (2 * d) * Real.exp (-((a ^ 2 + x ^ 2) * t))) -
          routeUHardEdgeKelvinCrossDensity a P 0 x * r ^ (2 * d + 1) * weight y *
            (t ^ (2 * d) * Real.exp (-((a ^ 2 + y ^ 2) * t))) := by
    funext t
    rw [routeUHardEdgeKelvinPairedCrossCurrent_eq_zeroHeatDifference ha hx]
    dsimp only [d, y, r]
    have hexpx : Real.exp (-(a ^ 2 * t)) * Real.exp (-(t * x ^ 2)) =
        Real.exp (-((a ^ 2 + x ^ 2) * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexpy : Real.exp (-(a ^ 2 * t)) * Real.exp (-(t * (a ^ 2 / x) ^ 2)) =
        Real.exp (-((a ^ 2 + (a ^ 2 / x) ^ 2) * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexpx, ← hexpy]
    ring
  rw [routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent]
  change (∫ t in Ioi (0 : ℝ),
    t ^ (2 * d) * Real.exp (-(a ^ 2 * t)) *
      routeUHardEdgeKelvinPairedCrossCurrent a P t weight x) = _
  rw [hfun]
  rw [integral_sub
    ((routeUIntegrableOn_pow_mul_exp_neg_mul_Ioi (2 * d) hcx).const_mul _)
    ((routeUIntegrableOn_pow_mul_exp_neg_mul_Ioi (2 * d) hcy).const_mul _),
    integral_const_mul, integral_const_mul,
    routeUIntegral_pow_mul_exp_neg_mul_Ioi (2 * d) hcx,
    routeUIntegral_pow_mul_exp_neg_mul_Ioi (2 * d) hcy]
  have hratio : r ^ (2 * d + 1) / (a ^ 2 + y ^ 2) ^ (2 * d + 1) =
      1 / (a ^ 2 + x ^ 2) ^ (2 * d + 1) := by
    rw [hden, mul_pow]
    field_simp [ne_of_gt hr, ne_of_gt hcx]
  rw [show (2 * d).factorial / (a ^ 2 + y ^ 2) ^ (2 * d + 1) =
      ((2 * d).factorial : ℝ) *
        (1 / (a ^ 2 + y ^ 2) ^ (2 * d + 1)) by ring]
  have hsecond :
      routeUHardEdgeKelvinCrossDensity a P 0 x * r ^ (2 * d + 1) * weight y *
          (((2 * d).factorial : ℝ) *
            (1 / (a ^ 2 + y ^ 2) ^ (2 * d + 1))) =
        routeUHardEdgeKelvinCrossDensity a P 0 x * weight y *
          (((2 * d).factorial : ℝ) *
            (1 / (a ^ 2 + x ^ 2) ^ (2 * d + 1))) := by
    rw [show routeUHardEdgeKelvinCrossDensity a P 0 x * r ^ (2 * d + 1) *
        weight y * (((2 * d).factorial : ℝ) *
          (1 / (a ^ 2 + y ^ 2) ^ (2 * d + 1))) =
      routeUHardEdgeKelvinCrossDensity a P 0 x * weight y *
        (((2 * d).factorial : ℝ) *
          (r ^ (2 * d + 1) / (a ^ 2 + y ^ 2) ^ (2 * d + 1))) by ring,
      hratio]
  rw [hsecond]
  dsimp only [d, y]
  ring

/-- Unit source weight cancels orbit by orbit after the exact Route U heat filter. -/
theorem routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent_one
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (P : Polynomial ℝ) :
    routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent a P (fun _ => 1) x = 0 := by
  rw [routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent_eq ha hx]
  ring

/-- Complete zero classification for the source-filtered Kelvin orbit. -/
theorem routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent_eq_zero_iff
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (P : Polynomial ℝ)
    (weight : ℝ → ℝ) :
    routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent a P weight x = 0 ↔
      routeUHardEdgeKelvinCrossDensity a P 0 x = 0 ∨
        weight x = weight (a ^ 2 / x) := by
  rw [routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent_eq ha hx]
  have hcoeff :
      ((2 * routeUHardEdgeKelvinDegree a P).factorial : ℝ) /
          (a ^ 2 + x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P + 1) ≠ 0 := by
    positivity
  rw [show ((2 * routeUHardEdgeKelvinDegree a P).factorial : ℝ) *
        routeUHardEdgeKelvinCrossDensity a P 0 x /
          (a ^ 2 + x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P + 1) *
            (weight x - weight (a ^ 2 / x)) =
      (((2 * routeUHardEdgeKelvinDegree a P).factorial : ℝ) /
        (a ^ 2 + x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P + 1)) *
          routeUHardEdgeKelvinCrossDensity a P 0 x *
            (weight x - weight (a ^ 2 / x)) by ring]
  simp only [mul_eq_zero, hcoeff, false_or, sub_eq_zero]

/-- On an inner Kelvin orbit, the filtered Gamma current has the opposite sign to the zero-heat
cross density. -/
theorem routeUHardEdgeKelvinLaplaceFilteredPairedGammaCrossCurrent_neg_of_pos
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hxa : x < a) (P : Polynomial ℝ)
    (hcross : 0 < routeUHardEdgeKelvinCrossDensity a P 0 x) :
    routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent
        a P gammaHardyPhaseRate x < 0 := by
  rw [routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent_eq ha hx]
  have hy : x < a ^ 2 / x := by
    rw [lt_div_iff₀ hx]
    nlinarith
  have hgamma : gammaHardyPhaseRate x < gammaHardyPhaseRate (a ^ 2 / x) :=
    strictMonoOn_gammaHardyPhaseRate (mem_Ici.mpr hx.le)
      (mem_Ici.mpr (div_nonneg (sq_nonneg a) hx.le)) hy
  have hfactor : 0 <
      ((2 * routeUHardEdgeKelvinDegree a P).factorial : ℝ) *
        routeUHardEdgeKelvinCrossDensity a P 0 x /
          (a ^ 2 + x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P + 1) := by
    positivity
  exact mul_neg_of_pos_of_neg hfactor (sub_neg.mpr hgamma)

theorem routeUHardEdgeKelvinLaplaceFilteredPairedGammaCrossCurrent_pos_of_neg
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hxa : x < a) (P : Polynomial ℝ)
    (hcross : routeUHardEdgeKelvinCrossDensity a P 0 x < 0) :
    0 < routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent
        a P gammaHardyPhaseRate x := by
  rw [routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent_eq ha hx]
  have hy : x < a ^ 2 / x := by
    rw [lt_div_iff₀ hx]
    nlinarith
  have hgamma : gammaHardyPhaseRate x < gammaHardyPhaseRate (a ^ 2 / x) :=
    strictMonoOn_gammaHardyPhaseRate (mem_Ici.mpr hx.le)
      (mem_Ici.mpr (div_nonneg (sq_nonneg a) hx.le)) hy
  have hfactor :
      ((2 * routeUHardEdgeKelvinDegree a P).factorial : ℝ) *
        routeUHardEdgeKelvinCrossDensity a P 0 x /
          (a ^ 2 + x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P + 1) < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hcross) (by positivity)
  exact mul_pos_of_neg_of_neg hfactor (sub_neg.mpr hgamma)

/-- On every strict inner orbit, the Gamma commutator is nonzero, so filtered-current vanishing
detects precisely the zero-heat cross seam. -/
theorem routeUHardEdgeKelvinLaplaceFilteredPairedGammaCrossCurrent_eq_zero_iff
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hxa : x < a) (P : Polynomial ℝ) :
    routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent
        a P gammaHardyPhaseRate x = 0 ↔
      routeUHardEdgeKelvinCrossDensity a P 0 x = 0 := by
  rw [routeUHardEdgeKelvinLaplaceFilteredPairedCrossCurrent_eq_zero_iff ha hx]
  have hy : x < a ^ 2 / x := by
    rw [lt_div_iff₀ hx]
    nlinarith
  have hgamma : gammaHardyPhaseRate x ≠ gammaHardyPhaseRate (a ^ 2 / x) :=
    ne_of_lt (strictMonoOn_gammaHardyPhaseRate (mem_Ici.mpr hx.le)
      (mem_Ici.mpr (div_nonneg (sq_nonneg a) hx.le)) hy)
  simp only [hgamma, or_false]

/-- Away from the self-dual seam, the hard-edge mass is the unique Laplace rate matched to Kelvin
inversion. -/
theorem routeUHardEdgeKelvinLaplaceRate_matching_iff
    {a x lambda : ℝ} (ha : 0 < a) (hx : 0 < x) (hxa : x ≠ a) :
    lambda + (a ^ 2 / x) ^ 2 =
        (a ^ 2 / x ^ 2) * (lambda + x ^ 2) ↔
      lambda = a ^ 2 := by
  have hdiff : x ^ 2 - a ^ 2 ≠ 0 := by
    rw [show x ^ 2 - a ^ 2 = (x - a) * (x + a) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr hxa) (by positivity)
  constructor
  · intro h
    field_simp [ne_of_gt hx] at h
    have hprod : (x ^ 2 - a ^ 2) * (lambda - a ^ 2) = 0 := by
      nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hdiff)
  · rintro rfl
    field_simp [ne_of_gt hx]
    ring

end RHTower
