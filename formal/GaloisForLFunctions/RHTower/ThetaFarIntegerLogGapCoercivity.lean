import GaloisForLFunctions.RHTower.ThetaRealTranslatedCoercivity

/-!
# Coercivity of the full Weil form for far integer-log-free source pairs

Local positivity is uniform after recentering. Complete integer-log exclusion
forces the component radius to shrink, while the normalized cross interaction
decays. Beyond one fixed separation, both the sum and difference therefore have
a uniform positive energy gap in total physical mass.

This proves a sign result for this source class. It does not cover general
prime-power-free gaps or arbitrary sources and does not prove RH.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem exists_thetaReal_farIntegerLogGap_coercivity :
    ∃ R kappa : ℝ, 0 < R ∧ 0 < kappa ∧
      ∀ (phi psi : 𝓢(ℝ, ℝ)), HasCompactSupport phi → HasCompactSupport psi →
      ∀ c₁ c₂ r : ℝ, 0 ≤ r → R ≤ c₂ - c₁ - 2 * r →
        Function.support phi ⊆ Metric.ball c₁ r →
        Function.support psi ⊆ Metric.ball c₂ r →
        (∀ n : ℕ, 2 ≤ n → Real.log n ∉ Ioo (c₂ - c₁ - 2 * r) (c₂ - c₁ + 2 * r)) →
        kappa * (thetaGroundNormSq (thetaComplexify phi) +
            thetaGroundNormSq (thetaComplexify psi)) ≤ thetaRealArithmeticQuadratic (phi + psi) ∧
        kappa * (thetaGroundNormSq (thetaComplexify phi) +
            thetaGroundNormSq (thetaComplexify psi)) ≤ thetaRealArithmeticQuadratic (phi - psi) := by
  obtain ⟨delta, C, hd, hC, hlocal⟩ := exists_thetaReal_center_independent_gap
  let R := max (screwSignThreshold + 1)
    (max (-Real.log (4 * delta) + 1) (1 - 2 * Real.log C))
  have hRt : screwSignThreshold + 1 ≤ R := le_max_left _ _
  have hRr : -Real.log (4 * delta) + 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRe : 1 - 2 * Real.log C ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hRp : 0 < R := by linarith [screwSignThreshold_pos]
  refine ⟨R, C / 2, hRp, half_pos hC, fun phi psi hpc hqc c₁ c₂ r hr hR hp hq hfree => ?_⟩
  have hgap : screwSignThreshold ≤ c₂ - c₁ - 2 * r := by linarith
  have hl : 0 ≤ c₂ - c₁ - 2 * r := screwSignThreshold_pos.le.trans hgap
  have hw := integerLogFree_equalRadius_width_le hl hfree
  have he : Real.exp (-(c₂ - c₁ - 2 * r)) < 4 * delta := by
    calc
      _ < Real.exp (Real.log (4 * delta)) := Real.exp_lt_exp.mpr (by linarith)
      _ = _ := Real.exp_log (by positivity)
  have hrd : r < delta := by linarith
  have hps : tsupport phi ⊆ Metric.ball c₁ delta :=
    (closure_minimal (hp.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hrd)
  have hqs : tsupport psi ⊆ Metric.ball c₂ delta :=
    (closure_minimal (hq.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hrd)
  have hpl := hlocal phi hpc c₁ hps
  have hql := hlocal psi hqc c₂ hqs
  have hpara := thetaRealArithmeticQuadratic_compact_parallelogram phi psi hpc hqc
  have hdiff := abs_thetaRealArithmeticQuadratic_integerLogGap_difference_le
    phi psi hpc hqc hr hp hq hgap hfree
  have hcoef : Real.exp (1 / 2) * Real.exp (-(c₂ - c₁ - 2 * r) / 2) ≤ C := by
    calc
      _ = Real.exp (1 / 2 - (c₂ - c₁ - 2 * r) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (Real.log C) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hC
  have hm := add_nonneg (thetaGroundNormSq_nonneg (thetaComplexify phi))
    (thetaGroundNormSq_nonneg (thetaComplexify psi))
  have hbound := hdiff.trans (mul_le_mul_of_nonneg_right hcoef hm)
  obtain ⟨hminus, hplus⟩ := abs_le.mp hbound
  constructor <;> nlinarith only [hpl, hql, hpara, hminus, hplus]

end RHTower
