import GaloisForLFunctions.RHTower.XiGaussianHeatRegularTransfer
import GaloisForLFunctions.HTGeometry.MomentNormalBlockDividedDifference

/-!
# The canonical heat transfer frame is a source Padé frame

The companion polynomial is exactly the heat moment functional applied to
the admission's divided difference. This identifies the second solution
with the actual source, including an initial gap with vanishing total mass.
The numerator and denominator have an explicit Bezout certificate at every
regular head, so their rational quotient has no polynomial cancellation.
-/

open Polynomial HTGeometry
namespace RHTower
noncomputable section

/-- The canonical companion is the source divided-difference numerator.
Every positive heat time and every regular head are covered, without a
positivity or nonzero-total-mass premise. -/
theorem hcf_regular_companion_source (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) :
    (heatRegularCompanion a j).eval x =
      momentFunctional (heatRealMoments a) (heatRegularAdmission a j /ₘ (X - C x)) := by
  have hpairs (j : ℕ) :
      momentDividedValue (heatRealMoments a) (heatRegularAdmission a j) x =
        (heatRegularCompanion a j).eval x ∧
      momentDividedValue (heatRealMoments a) (heatRegularAdmission a (j + 1)) x =
        (heatRegularCompanion a (j + 1)).eval x := by
    induction j with
    | zero =>
      constructor
      · simp [momentDividedValue]
      · rw [heatRegularCompanion_one, eval_C]
        have he : heatRegularAdmission a 1 =
            monicMomentAdmissionPolynomial (heatRealMoments a) (heatRegularGap a 0) := by
          unfold heatRegularAdmission
          rw [← heatRegularHead_add_gap a 0]
          simp only [heatRegularHead, zero_add]
        rw [he]
        exact (heatRegularGap_normalBlock a 0).divided_value_first x
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have hprod : momentDividedValue (heatRealMoments a)
          (heatRegularQuotient a (j + 1) * heatRegularAdmission a (j + 1)) x =
          (heatRegularQuotient a (j + 1)).eval x *
            momentDividedValue (heatRealMoments a) (heatRegularAdmission a (j + 1)) x := by
        apply (heatRegularGap_normalBlock a (j + 1)).divided_value_mul
        · have := le_heatRegularHead a (j + 1)
          omega
        · exact (heatRegularQuotient_monic_degree a (j + 1)).2.le
      rw [hcf_regular_head_recurrence a j, momentDividedValue_sub_C_mul,
        hprod, ih.2, ih.1, heatRegularCompanion_recurrence a j,
        eval_sub, eval_mul, eval_mul, eval_C]
  exact (hpairs j).1.symm

/-- Explicit source numerator/denominator Bezout identity at a regular head. -/
theorem hcf_regular_pade_bezout (a : {t : ℝ // 0 < t}) (j : ℕ) :
    (-(C ((heatRegularCoupling a j)⁻¹) * heatRegularCompanion a j)) *
        heatRegularAdmission a (j + 1) +
      (C ((heatRegularCoupling a j)⁻¹) * heatRegularAdmission a j) *
        heatRegularCompanion a (j + 1) = 1 := by
  calc
    _ = C ((heatRegularCoupling a j)⁻¹) *
        (-(heatRegularAdmission a (j + 1) * heatRegularCompanion a j -
          heatRegularCompanion a (j + 1) * heatRegularAdmission a j)) := by ring
    _ = 1 := by
      rw [hcf_regular_head_casoratian, C_neg, neg_neg, ← C_mul,
        inv_mul_cancel₀ (heatRegularCoupling_ne_zero a j), C_1]

/-- Every canonical regular-head rational approximant is reduced. Singular
gaps cannot introduce a common factor into its source numerator and denominator. -/
theorem hcf_regular_pade_reduced (a : {t : ℝ // 0 < t}) (j : ℕ) :
    IsCoprime (heatRegularAdmission a j) (heatRegularCompanion a j) := by
  cases j with
  | zero => exact ⟨1, 0, by simp⟩
  | succ j => exact ⟨_, _, hcf_regular_pade_bezout a j⟩

theorem hcf_regular_pade_no_common_root (a : {t : ℝ // 0 < t}) (j : ℕ) (z : ℂ) :
    aeval z (heatRegularAdmission a j) ≠ 0 ∨
      aeval z (heatRegularCompanion a j) ≠ 0 :=
  aeval_ne_zero_of_isCoprime (hcf_regular_pade_reduced a j) z

end
end RHTower
