import GaloisForLFunctions.RHTower.ThetaCuspThreeAtomSourceDerivatives
import GaloisForLFunctions.HilbertMetric.ReflectionFourthJet

/-!
# Negative fourth logarithmic jet of the three-atom source

The normalized derivative polynomials are assembled for the first three
positive theta atoms. Their fourth logarithmic numerator is exactly
sixteen times the reduced Euler numerator. This transfers its uniform
negative margin to the literal source derivative jets, without an
unproved sign premise or a truncated substitute for any retained atom.
-/

namespace RHTower.ThetaCuspThreeAtomFourth

/-- The first-three-atom raw derivative jet in exponential coordinates. -/
noncomputable def rawHeadJet (j : ℕ) (q z w : ℝ) : ℝ :=
  (atomJetPolynomial j).eval q + 4*(atomJetPolynomial j).eval (4*q)*z +
    9*(atomJetPolynomial j).eval (9*q)*w

theorem rawHeadJet_eq_normalized (j : ℕ) (q : ℝ) :
    rawHeadJet j q (Real.exp (-3*q)) (Real.exp (-8*q)) =
      normalizedAtomJet j q 1 + normalizedAtomJet j q 2 + normalizedAtomJet j q 3 := by
  norm_num [rawHeadJet, normalizedAtomJet]
  ring_nf

theorem rawHeadJet_zero (q z w : ℝ) : rawHeadJet 0 q z w = eulerJet 0 q z w := by
  simp [rawHeadJet, atomJetPolynomial, eulerJet]
  ring

/-- Exact conversion from raw derivatives to the reduced Euler numerator. -/
theorem rawHeadJet_fourth_numerator (q z w : ℝ) :
    (rawHeadJet 0 q z w)^3 * rawHeadJet 4 q z w -
      4*(rawHeadJet 0 q z w)^2 * rawHeadJet 3 q z w * rawHeadJet 1 q z w -
      3*(rawHeadJet 0 q z w)^2 * (rawHeadJet 2 q z w)^2 +
      12*rawHeadJet 0 q z w * rawHeadJet 2 q z w * (rawHeadJet 1 q z w)^2 -
      6*(rawHeadJet 1 q z w)^4 = 16*numerator q z w := by
  norm_num [rawHeadJet, atomJetPolynomial_eval, atomCoefficient, Finset.sum_range_succ,
    numerator, eulerJet]
  ring

theorem rawHeadJet_fourthLogJet_eq (q z w : ℝ) (h0 : rawHeadJet 0 q z w ≠ 0) :
    HilbertMetric.logarithmicFourthJet (rawHeadJet 0 q z w) (rawHeadJet 1 q z w)
      (rawHeadJet 2 q z w) (rawHeadJet 3 q z w) (rawHeadJet 4 q z w) =
      16*(numerator q z w / (eulerJet 0 q z w)^4) := by
  have hid := rawHeadJet_fourth_numerator q z w
  rw [← rawHeadJet_zero]
  unfold HilbertMetric.logarithmicFourthJet
  field_simp
  linear_combination hid

theorem rawHeadJet_fourthLogJet_lt {q : ℝ} (hq : Real.pi ≤ q) :
    HilbertMetric.logarithmicFourthJet
      (rawHeadJet 0 q (Real.exp (-3*q)) (Real.exp (-8*q)))
      (rawHeadJet 1 q (Real.exp (-3*q)) (Real.exp (-8*q)))
      (rawHeadJet 2 q (Real.exp (-3*q)) (Real.exp (-8*q)))
      (rawHeadJet 3 q (Real.exp (-3*q)) (Real.exp (-8*q)))
      (rawHeadJet 4 q (Real.exp (-3*q)) (Real.exp (-8*q))) < -(17/10) := by
  have hq3 : 3 ≤ q := by linarith [Real.pi_gt_d2]
  have h0 : rawHeadJet 0 q (Real.exp (-3*q)) (Real.exp (-8*q)) ≠ 0 := by
    rw [rawHeadJet_zero]
    exact (head_pos hq3).ne'
  rw [rawHeadJet_fourthLogJet_eq _ _ _ h0]
  have h := normalized_numerator_lt hq
  linarith

/-- Literal derivative jets of the first three positive source atoms. -/
noncomputable def headSourceJet (j : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv j (fun y => thetaCuspSourceTerm y 1) x +
    iteratedDeriv j (fun y => thetaCuspSourceTerm y 2) x +
    iteratedDeriv j (fun y => thetaCuspSourceTerm y 3) x

theorem headSourceJet_eq_normalized (j : ℕ) (x : ℝ) :
    headSourceJet j x = sourcePrefactor x *
      rawHeadJet j (sourceScale x) (Real.exp (-3*sourceScale x)) (Real.exp (-8*sourceScale x)) := by
  simp only [headSourceJet, iteratedDeriv_sourceTerm_eq_normalized, rawHeadJet_eq_normalized]
  ring

private theorem fourthLogJet_scale (c a₀ a₁ a₂ a₃ a₄ : ℝ) (hc : c ≠ 0) (h0 : a₀ ≠ 0) :
    HilbertMetric.logarithmicFourthJet (c*a₀) (c*a₁) (c*a₂) (c*a₃) (c*a₄) =
      HilbertMetric.logarithmicFourthJet a₀ a₁ a₂ a₃ a₄ := by
  unfold HilbertMetric.logarithmicFourthJet
  field_simp

/-- Uniform negative fourth logarithmic jet for the literal three-atom head. -/
theorem headSourceJet_fourthLogJet_lt {x : ℝ} (hx : 0 ≤ x) :
    HilbertMetric.logarithmicFourthJet (headSourceJet 0 x) (headSourceJet 1 x)
      (headSourceJet 2 x) (headSourceJet 3 x) (headSourceJet 4 x) < -(17/10) := by
  have hq := sourceScale_ge_pi hx
  have hq3 : 3 ≤ sourceScale x := by linarith [Real.pi_gt_d2]
  have h0 : rawHeadJet 0 (sourceScale x) (Real.exp (-3*sourceScale x))
      (Real.exp (-8*sourceScale x)) ≠ 0 := by
    rw [rawHeadJet_zero]
    exact (head_pos hq3).ne'
  simp only [headSourceJet_eq_normalized]
  rw [fourthLogJet_scale _ _ _ _ _ _ (sourcePrefactor_pos x).ne' h0]
  exact rawHeadJet_fourthLogJet_lt hq

end RHTower.ThetaCuspThreeAtomFourth
