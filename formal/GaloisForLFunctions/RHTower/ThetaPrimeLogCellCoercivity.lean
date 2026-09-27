import GaloisForLFunctions.RHTower.PrimeLogCellAtomBound
import GaloisForLFunctions.RHTower.ThetaPrimeGapPolarization
import GaloisForLFunctions.RHTower.ThetaFinitePrimeAtomPolarization

/-!
# Full source positivity on cofinally many genuine prime-log cells

The continuous interaction is bounded by the square-root normalized prime gap.
Every active prime-power interaction is bounded by the cell's actual atom mass.
Cofinal cells make both budgets arbitrarily small. Together with the proved
center-independent diagonal gap, this gives a uniform positive gap for both
signs of every real source pair fitting into those cells.

No avoidance of integer or prime-power translations is required. This remains
a restricted source class and does not establish the all-source RH criterion.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem abs_thetaPrimeScalingCross_primeLogCell_difference_le
    (phi psi : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport phi)
    (N : ℕ) {c₁ c₂ r : ℝ}
    (hp : Function.support phi ⊆ Metric.ball c₁ r)
    (hq : Function.support psi ⊆ Metric.ball c₂ r)
    (hleft : xiMassNthPrimeLogHeight N ≤ c₂ - c₁ - 2 * r)
    (hright : c₂ - c₁ + 2 * r ≤ xiMassNthPrimeLogHeight (N + 1)) :
    |thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
      thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi - psi)).toBoundedContinuousFunction| ≤
      primeLogCellAtomMass N *
        (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) := by
  have hdiff (x : ℝ) (hx : x ∈ Function.support psi)
      (y : ℝ) (hy : y ∈ Function.support phi) :
      xiMassNthPrimeLogHeight N < x - y ∧
        x - y < xiMassNthPrimeLogHeight (N + 1) := by
    have hx' := hq hx
    have hy' := hp hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx' hy'
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  apply abs_thetaPrimeScalingCross_difference_le_finite_mass phi psi hc
    (Finset.Ioc (nthPrimeSubtype N : ℕ) (nthPrimeSubtype (N + 1) : ℕ))
  · intro x hx y hy
    exact screwSignThreshold_pos.trans
      ((screwSignThreshold_lt_primeLogHeight N).trans (hdiff x hx y hy).1)
  · intro x hx y hy n hn he
    have hd := hdiff x hx y hy
    rw [he] at hd
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (IsPrimePow.one_lt hn).trans' Nat.zero_lt_one
    have hlow := (Real.log_lt_log_iff (nthPrimeSubtype_pos N) hn0).mp hd.1
    have hhigh := (Real.log_lt_log_iff hn0 (nthPrimeSubtype_pos (N + 1))).mp hd.2
    exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast hlow, by exact_mod_cast hhigh.le⟩

theorem abs_thetaRealArithmeticQuadratic_primeLogCell_full_difference_le
    (phi psi : 𝓢(ℝ, ℝ)) (hpc : HasCompactSupport phi) (hqc : HasCompactSupport psi)
    (N : ℕ) {c₁ c₂ r : ℝ} (hr : 0 ≤ r)
    (hp : Function.support phi ⊆ Metric.ball c₁ r)
    (hq : Function.support psi ⊆ Metric.ball c₂ r)
    (hleft : xiMassNthPrimeLogHeight N ≤ c₂ - c₁ - 2 * r)
    (hright : c₂ - c₁ + 2 * r ≤ xiMassNthPrimeLogHeight (N + 1)) :
    |thetaRealArithmeticQuadratic (phi + psi) - thetaRealArithmeticQuadratic (phi - psi)| ≤
      2 * (xiHeatCassiniOrderedPrimeGap N / Real.sqrt (nthPrimeSubtype N : ℝ) +
        primeLogCellAtomMass N) *
        (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) := by
  have h := abs_thetaRealArithmeticQuadratic_primeLogCell_difference_le
    phi psi hpc hqc N hr hp hq hleft hright
  have ha := abs_thetaPrimeScalingCross_primeLogCell_difference_le
    phi psi hpc N hp hq hleft hright
  calc
    _ ≤ (2 * xiHeatCassiniOrderedPrimeGap N / Real.sqrt (nthPrimeSubtype N : ℝ)) *
          (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) +
        2 * (primeLogCellAtomMass N *
          (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi))) := by
      linarith only [h, ha]
    _ = _ := by ring

/-- One positive constant works on every source pair in cofinally many actual prime-log cells. -/
theorem exists_thetaReal_cofinal_primeLogCell_coercivity :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ (phi psi : 𝓢(ℝ, ℝ)), HasCompactSupport phi → HasCompactSupport psi →
      ∀ c₁ c₂ r : ℝ, 0 ≤ r →
        Function.support phi ⊆ Metric.ball c₁ r →
        Function.support psi ⊆ Metric.ball c₂ r →
        xiMassNthPrimeLogHeight n ≤ c₂ - c₁ - 2 * r →
        c₂ - c₁ + 2 * r ≤ xiMassNthPrimeLogHeight (n + 1) →
        kappa * (thetaGroundNormSq (thetaComplexify phi) +
            thetaGroundNormSq (thetaComplexify psi)) ≤ thetaRealArithmeticQuadratic (phi + psi) ∧
        kappa * (thetaGroundNormSq (thetaComplexify phi) +
            thetaGroundNormSq (thetaComplexify psi)) ≤ thetaRealArithmeticQuadratic (phi - psi) := by
  obtain ⟨delta, C, hd, hC, hlocal⟩ := exists_thetaReal_center_independent_gap
  refine ⟨C / 2, half_pos hC, fun N => ?_⟩
  obtain ⟨n, hn, hg, ha⟩ := exists_primeLogCell_small_budgets
    (lt_min (div_pos hC (by positivity : (0 : ℝ) < 4)) hd) N
  refine ⟨n, hn, fun phi psi hpc hqc c₁ c₂ r hr hp hq hleft hright => ?_⟩
  have hp1 : 1 ≤ (nthPrimeSubtype n : ℝ) := by exact_mod_cast (nthPrimeSubtype n).prop.one_lt.le
  have hs1 : 1 ≤ Real.sqrt (nthPrimeSubtype n : ℝ) := Real.one_le_sqrt.mpr hp1
  have hsp := Real.sqrt_pos.mpr (nthPrimeSubtype_pos n)
  have hsle : Real.sqrt (nthPrimeSubtype n : ℝ) ≤ (nthPrimeSubtype n : ℝ) := by
    nlinarith [Real.sq_sqrt (nthPrimeSubtype_pos n).le]
  have hw : 4 * r ≤ xiHeatCassiniOrderedPrimeLogGap n := by
    unfold xiHeatCassiniOrderedPrimeLogGap
    linarith
  have hscale : xiHeatCassiniOrderedPrimeLogGap n ≤
      xiHeatCassiniOrderedPrimeGap n / Real.sqrt (nthPrimeSubtype n : ℝ) :=
    (xiHeatCassiniOrderedPrimeLogGap_le_gap_div_prime n).trans
      (div_le_div_of_nonneg_left (xiHeatCassiniOrderedPrimeGap_nonneg n) hsp hsle)
  have hrd : r < delta := by
    have hgd := hg.trans_le (min_le_right _ _)
    linarith
  have hps : tsupport phi ⊆ Metric.ball c₁ delta :=
    (closure_minimal (hp.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hrd)
  have hqs : tsupport psi ⊆ Metric.ball c₂ delta :=
    (closure_minimal (hq.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hrd)
  have hpl := hlocal phi hpc c₁ hps
  have hql := hlocal psi hqc c₂ hqs
  have hpara := thetaRealArithmeticQuadratic_compact_parallelogram phi psi hpc hqc
  have hdiff := abs_thetaRealArithmeticQuadratic_primeLogCell_full_difference_le
    phi psi hpc hqc n hr hp hq hleft hright
  have hcoef : 2 * (xiHeatCassiniOrderedPrimeGap n / Real.sqrt (nthPrimeSubtype n : ℝ) +
      primeLogCellAtomMass n) ≤ C := by
    have hgc := hg.trans_le (min_le_left _ _)
    have hac := ha.trans_le (min_le_left _ _)
    linarith
  have hm := add_nonneg (thetaGroundNormSq_nonneg (thetaComplexify phi))
    (thetaGroundNormSq_nonneg (thetaComplexify psi))
  obtain ⟨hminus, hplus⟩ := abs_le.mp
    (hdiff.trans (mul_le_mul_of_nonneg_right hcoef hm))
  constructor <;> nlinarith only [hpl, hql, hpara, hminus, hplus]

end RHTower
