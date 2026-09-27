import GaloisForLFunctions.RHTower.CCMIntegerLogGapCrossBound
import GaloisForLFunctions.RHTower.XiHeatCassiniLogMeshPrimeGapQuadrature

/-!
# The square-root prime-gap scale in the actual source cross interaction

Two equal-radius source balls whose difference interval lies inside a consecutive
prime-log cell have regular-kernel interaction at most the additive prime gap
divided by twice the square root of the lower prime, times their total physical
mass. This connects the source geometry to the existing prime-gap quadrature
infrastructure. No asymptotic estimate for prime gaps is assumed.

This module bounds the continuous interaction. Prime-power translations inside
the prime-log cell can still contribute to the complete Weil quadratic.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.RHTower

theorem screwSignThreshold_lt_primeLogHeight (N : ℕ) :
    screwSignThreshold < xiMassNthPrimeLogHeight N := by
  unfold screwSignThreshold xiMassNthPrimeLogHeight
  apply Real.log_lt_log plasticRoot_pos
  exact plasticRoot_mem_Ioo.2.trans_le (by exact_mod_cast (nthPrimeSubtype N).prop.two_le)

theorem primeLogGap_mul_criticalHalfDensity_le_gap_div_sqrt (N : ℕ) :
    xiHeatCassiniOrderedPrimeLogGap N *
        Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) ≤
      2 * xiHeatCassiniOrderedPrimeGap N / Real.sqrt (nthPrimeSubtype N : ℝ) := by
  let p : ℝ := nthPrimeSubtype N
  let q : ℝ := nthPrimeSubtype (N + 1)
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hq : 0 < q := nthPrimeSubtype_pos (N + 1)
  have hq2p : q ≤ 2 * p := by
    dsimp only [p, q]
    exact_mod_cast nthPrimeSubtype_succ_le_two_mul N
  have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hsqrt : Real.sqrt q ≤ 2 * Real.sqrt p := by
    calc
      Real.sqrt q ≤ Real.sqrt (2 * p) := Real.sqrt_le_sqrt hq2p
      _ = Real.sqrt 2 * Real.sqrt p := by rw [Real.sqrt_mul (by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsqrtTwo (Real.sqrt_nonneg p)
  have hexp : Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) = Real.sqrt q := by
    dsimp only [xiMassNthPrimeLogHeight, q]
    rw [← Real.log_sqrt hq.le, Real.exp_log (Real.sqrt_pos.mpr hq)]
  rw [hexp]
  calc
    _ ≤ (xiHeatCassiniOrderedPrimeGap N / p) * (2 * Real.sqrt p) :=
      mul_le_mul (xiHeatCassiniOrderedPrimeLogGap_le_gap_div_prime N) hsqrt
        (Real.sqrt_nonneg q) (div_nonneg (xiHeatCassiniOrderedPrimeGap_nonneg N) hp.le)
    _ = _ := by
      change _ = 2 * xiHeatCassiniOrderedPrimeGap N / Real.sqrt p
      calc
        _ = 2 * xiHeatCassiniOrderedPrimeGap N * (Real.sqrt p / p) := by ring
        _ = _ := by rw [Real.sqrt_div_self']; ring

/-- The continuous cross interaction of actual CCM sources sees normalized additive
prime gaps at square-root scale. -/
theorem abs_screwRegularForm_ccm_primeLogCell_le {a b : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (v : CCMComplexSmoothInteriorSource b)
    (N : ℕ) {c₁ c₂ r : ℝ} (hr : 0 ≤ r)
    (hu : Function.support u ⊆ Metric.ball c₁ r)
    (hv : Function.support v ⊆ Metric.ball c₂ r)
    (hleft : xiMassNthPrimeLogHeight N ≤ c₂ - c₁ - 2 * r)
    (hright : c₂ - c₁ + 2 * r ≤ xiMassNthPrimeLogHeight (N + 1)) :
    |screwRegularForm (fun x => (u x).re) (fun x => (v x).re)| ≤
      (xiHeatCassiniOrderedPrimeGap N / (2 * Real.sqrt (nthPrimeSubtype N : ℝ))) *
        (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
          ‖ccmArchimedeanFormEmbedding b v.toCCMFormVector‖ ^ 2) := by
  have hgap := (screwSignThreshold_lt_primeLogHeight N).le.trans hleft
  have hsep : ∀ x ∈ Function.support v, ∀ y ∈ Function.support u,
      screwSignThreshold < x - y ∧ x - y ≤ xiMassNthPrimeLogHeight (N + 1) := by
    intro x hx y hy
    have hx' := hv hx
    have hy' := hu hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx' hy'
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  have hwidth : 4 * r ≤ xiHeatCassiniOrderedPrimeLogGap N := by
    unfold xiHeatCassiniOrderedPrimeLogGap
    linarith
  have hscale := primeLogGap_mul_criticalHalfDensity_le_gap_div_sqrt N
  have hcoef : Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) * r ≤
      xiHeatCassiniOrderedPrimeGap N / (2 * Real.sqrt (nthPrimeSubtype N : ℝ)) := by
    have hw := mul_le_mul_of_nonneg_right hwidth
      (Real.exp_pos (xiMassNthPrimeLogHeight (N + 1) / 2)).le
    have he : 2 * xiHeatCassiniOrderedPrimeGap N / Real.sqrt (nthPrimeSubtype N : ℝ) =
        4 * (xiHeatCassiniOrderedPrimeGap N / (2 * Real.sqrt (nthPrimeSubtype N : ℝ))) := by
      field_simp
      ring
    rw [he] at hscale
    nlinarith only [hw, hscale]
  have hbound := (abs_screwRegularForm_ccm_le_l1 u v hsep).trans
    (mul_le_mul_of_nonneg_left (ccmSmooth_l1_product_le_ball_mass_sum u v hr hu hv)
      (Real.exp_pos _).le)
  calc
    _ ≤ Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) * (r *
        (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
          ‖ccmArchimedeanFormEmbedding b v.toCCMFormVector‖ ^ 2)) := hbound
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef
        (add_nonneg (sq_nonneg _) (sq_nonneg _))

end RHTower
