import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectReserve
/-!
# Finite cumulant grading of the curvature-defect cooling functional

The third and fifth grades are nonnegative. The fourth and sixth grades
are controlled by actual normalized moment products and tail probability.
The remaining negative binary grade is isolated without discarding any
cumulant contribution. Its absorption is a separate open obligation.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section
private theorem third_grade_nonneg (c3 c4 c5 c6 e1 e2 e3 e4 : ℝ)
    (hc4 : 0 ≤ c4) (hc6 : 0 ≤ c6) (hc56 : 0 ≤ 9*c6+c5)
    (hc34 : 0 ≤ 18*c4+c3) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (he3 : 0 ≤ e3) (he4 : 0 ≤ e4) (h12 : 3*e1 ≤ e2) (h23 : 3*e2 ≤ e3) :
    0 ≤ c3*e1^3+6*c4*e1^2*e2+c5*(10*e1^2*e3+15*e1*e2^2)+
      c6*(15*e1^2*e4+60*e1*e2*e3+15*e2^3) := by
  have hd12 : 0 ≤ e2-3*e1 := sub_nonneg.mpr h12
  have hd23 : 0 ≤ e3-3*e2 := sub_nonneg.mpr h23
  calc
    0 ≤ 15*c6*e1^2*e4+30*c6*e1*(e2-3*e1)*e3+
      30*c6*e1*e2*(e3-3*e2)+15*c6*e2^2*(e2-3*e1)+
      10*(9*c6+c5)*e1^2*e3+15*(9*c6+c5)*e1*e2^2+
      6*c4*e1^2*(e2-3*e1)+(18*c4+c3)*e1^3 := by positivity
    _ = _ := by ring
private theorem fifth_grade_nonneg (c5 c6 e1 e2 : ℝ)
    (hc6 : 0 ≤ c6) (hc56 : 0 ≤ 9*c6+c5) (he1 : 0 ≤ e1) (h12 : 3*e1 ≤ e2) :
    0 ≤ c5*e1^5+15*c6*e1^4*e2 := by
  have hd12 : 0 ≤ e2-3*e1 := sub_nonneg.mpr h12
  have h45 : 0 ≤ 45*c6+c5 := by linarith
  calc
    0 ≤ 15*c6*e1^4*(e2-3*e1)+(45*c6+c5)*e1^5 := by positivity
    _ = _ := by ring
end
end RHTower.ThetaCuspDefect
namespace RHTower.ThetaCuspDefect
noncomputable section
private theorem fourth_grade_upper
    (c4 c5 c6 e1 e2 e3 e4 e6 p : ℝ)
    (hc4 : 0 ≤ c4) (hc5 : c5 ≤ 0) (hc6 : 0 ≤ c6) (hc46 : c4 ≤ 16*c6)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (he4 : 0 ≤ e4) (_he6 : 0 ≤ e6) (hp : 0 ≤ p)
    (h11 : e1^2 ≤ p*e2) (h22 : e2^2 ≤ p*e4)
    (h13 : e1*e3 ≤ p*e4) (h24 : e2*e4 ≤ p*e6)
    (h46 : 9*e4 ≤ e6) :
    c4*e1^4+10*c5*e1^3*e2+c6*(20*e1^3*e3+45*e1^2*e2^2) ≤
      67*c6*p^3*e6 := by
  have h1113 : e1^3*e3 ≤ p^3*e6 := by
    calc
      e1^3*e3 = e1^2*(e1*e3) := by ring
      _ ≤ (p*e2)*(p*e4) := mul_le_mul h11 h13 (by positivity) (by positivity)
      _ = p^2*(e2*e4) := by ring
      _ ≤ p^2*(p*e6) := mul_le_mul_of_nonneg_left h24 (sq_nonneg p)
      _ = p^3*e6 := by ring
  have h1122 : e1^2*e2^2 ≤ p^3*e6 := by
    calc
      e1^2*e2^2 ≤ (p*e2)*(p*e4) := mul_le_mul h11 h22 (sq_nonneg e2) (by positivity)
      _ = p^2*(e2*e4) := by ring
      _ ≤ p^2*(p*e6) := mul_le_mul_of_nonneg_left h24 (sq_nonneg p)
      _ = p^3*e6 := by ring
  have h1111 : e1^4 ≤ p^3*e4 := by
    calc
      e1^4 = e1^2*e1^2 := by ring
      _ ≤ (p*e2)*(p*e2) := mul_le_mul h11 h11 (sq_nonneg e1) (by positivity)
      _ = p^2*e2^2 := by ring
      _ ≤ p^2*(p*e4) := mul_le_mul_of_nonneg_left h22 (sq_nonneg p)
      _ = p^3*e4 := by ring
  have hn : 10*c5*e1^3*e2 ≤ 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg hc5 (show 0 ≤ 10*e1^3*e2 by positivity)
    nlinarith only [this]
  have hrem : c4*e4 ≤ 2*c6*e6 := by
    have h0 := mul_le_mul_of_nonneg_right hc46 he4
    have h1 := mul_le_mul_of_nonneg_left h46 hc6
    nlinarith
  have hlin := mul_le_mul_of_nonneg_left h1111 hc4
  have hlin' := mul_le_mul_of_nonneg_left hrem (show 0 ≤ p^3 by positivity)
  have ha := mul_le_mul_of_nonneg_left h1113 (show 0 ≤ 20*c6 by positivity)
  have hb := mul_le_mul_of_nonneg_left h1122 (show 0 ≤ 45*c6 by positivity)
  nlinarith only [hn,hlin,hlin',ha,hb]
end
end RHTower.ThetaCuspDefect

namespace RHTower.ThetaCuspDefect
noncomputable section
def gradeTwo (q : ℝ) (e : ℕ → ℝ) : ℝ :=
  coolingCoefficient q 2*(e 1)^2+3*coolingCoefficient q 3*e 1*e 2+
  coolingCoefficient q 4*(4*e 1*e 3+3*(e 2)^2)+
  coolingCoefficient q 5*(5*e 1*e 4+10*e 2*e 3)+
  coolingCoefficient q 6*(6*e 1*e 5+15*e 2*e 4+10*(e 3)^2)
def gradeThree (q : ℝ) (e : ℕ → ℝ) : ℝ :=
  coolingCoefficient q 3*(e 1)^3+6*coolingCoefficient q 4*(e 1)^2*e 2+
  coolingCoefficient q 5*(10*(e 1)^2*e 3+15*e 1*(e 2)^2)+
  coolingCoefficient q 6*(15*(e 1)^2*e 4+60*e 1*e 2*e 3+15*(e 2)^3)
def gradeFour (q : ℝ) (e : ℕ → ℝ) : ℝ :=
  coolingCoefficient q 4*(e 1)^4+10*coolingCoefficient q 5*(e 1)^3*e 2+
  coolingCoefficient q 6*(20*(e 1)^3*e 3+45*(e 1)^2*(e 2)^2)
def gradeFive (q : ℝ) (e : ℕ → ℝ) : ℝ :=
  coolingCoefficient q 5*(e 1)^5+15*coolingCoefficient q 6*(e 1)^4*e 2
def gradeSix (q : ℝ) (e : ℕ → ℝ) : ℝ := coolingCoefficient q 6*(e 1)^6
def likelihoodCumulant (q : ℝ) : ℕ → ℝ
  | 2 => thetaCuspLikelihoodVariance q
  | 3 => thetaCuspLikelihoodThirdCumulant q
  | 4 => thetaCuspLikelihoodFourthCumulant q
  | 5 => thetaCuspLikelihoodFifthCumulant q
  | 6 => thetaCuspLikelihoodSixthCumulant q
  | _ => 0

theorem cooling_cumulant_grades (q : ℝ) :
    coolingFunctional q (likelihoodCumulant q) =
      coolingFunctional q (thetaCuspLikelihoodNormalizedMoment q)-
      gradeTwo q (thetaCuspLikelihoodNormalizedMoment q)+
      2*gradeThree q (thetaCuspLikelihoodNormalizedMoment q)-
      6*gradeFour q (thetaCuspLikelihoodNormalizedMoment q)+
      24*gradeFive q (thetaCuspLikelihoodNormalizedMoment q)-
      120*gradeSix q (thetaCuspLikelihoodNormalizedMoment q) := by
  simp only [coolingFunctional,Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num only [Nat.reduceAdd,likelihoodCumulant]
  unfold thetaCuspLikelihoodThirdCumulant thetaCuspLikelihoodFourthCumulant
    thetaCuspLikelihoodFifthCumulant thetaCuspLikelihoodSixthCumulant
    gradeTwo gradeThree gradeFour gradeFive gradeSix
  rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
  simp only [thetaCuspLikelihoodNormalizedMoment_one_eq_mean]
  unfold thetaCuspLikelihoodNormalizedMoment
  ring
end
end RHTower.ThetaCuspDefect

namespace RHTower.ThetaCuspDefect
noncomputable section
private theorem coefficient_nine_six_add_five_nonneg {q : ℝ} (hq : 3/2 ≤ q) :
    0 ≤ 9*coolingCoefficient q 6+coolingCoefficient q 5 := by
  have h (y : ℝ) (hy : 0 ≤ y) :
      0 ≤ 9*coolingCoefficient (3/2+y) 6+coolingCoefficient (3/2+y) 5 := by
    simp only [coolingCoefficient]
    ring_nf
    positivity
  simpa only [show 3/2+(q-3/2)=q by ring] using h (q-3/2) (by linarith)
private theorem coefficient_eighteen_four_add_three_nonneg {q : ℝ} (hq : 3/2 ≤ q) :
    0 ≤ 18*coolingCoefficient q 4+coolingCoefficient q 3 := by
  have h (y : ℝ) (hy : 0 ≤ y) :
      0 ≤ 18*coolingCoefficient (3/2+y) 4+coolingCoefficient (3/2+y) 3 := by
    simp only [coolingCoefficient]
    ring_nf
    positivity
  simpa only [show 3/2+(q-3/2)=q by ring] using h (q-3/2) (by linarith)
private theorem normalizedMoment_nonneg {q : ℝ} (hq : 0 < q) (j : ℕ) :
    0 ≤ thetaCuspLikelihoodNormalizedMoment q j :=
  div_nonneg (thetaCuspHigherLikelihoodSpectralMoment_nonneg j)
    (thetaCuspLikelihoodPartition_pos hq).le

theorem gradeThree_normalized_nonneg {q : ℝ} (hq : 3/2 ≤ q) :
    0 ≤ gradeThree q (thetaCuspLikelihoodNormalizedMoment q) := by
  have hq0 : 0 < q := by linarith
  apply third_grade_nonneg
  · simp only [coolingCoefficient]; positivity
  · simp only [coolingCoefficient]; positivity
  · exact coefficient_nine_six_add_five_nonneg hq
  · exact coefficient_eighteen_four_add_three_nonneg hq
  · exact normalizedMoment_nonneg hq0 1
  · exact normalizedMoment_nonneg hq0 2
  · exact normalizedMoment_nonneg hq0 3
  · exact normalizedMoment_nonneg hq0 4
  · exact three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hq0 1
  · exact three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hq0 2

theorem gradeFive_normalized_nonneg {q : ℝ} (hq : 3/2 ≤ q) :
    0 ≤ gradeFive q (thetaCuspLikelihoodNormalizedMoment q) := by
  have hq0 : 0 < q := by linarith
  apply fifth_grade_nonneg
  · simp only [coolingCoefficient]; positivity
  · exact coefficient_nine_six_add_five_nonneg hq
  · exact normalizedMoment_nonneg hq0 1
  · exact three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hq0 1
end
end RHTower.ThetaCuspDefect

namespace RHTower.ThetaCuspDefect
noncomputable section
private theorem coefficient_four_le_six {q : ℝ} (hq : 3/2 ≤ q) :
    coolingCoefficient q 4 ≤ 16*coolingCoefficient q 6 := by
  have h (y : ℝ) (hy : 0 ≤ y) :
      coolingCoefficient (3/2+y) 4 ≤ 16*coolingCoefficient (3/2+y) 6 := by
    apply sub_nonneg.mp
    simp only [coolingCoefficient]
    ring_nf
    positivity
  simpa only [show 3/2+(q-3/2)=q by ring] using h (q-3/2) (by linarith)

theorem gradeFour_normalized_upper {q : ℝ} (hq : 3/2 ≤ q) :
    gradeFour q (thetaCuspLikelihoodNormalizedMoment q) ≤
      67*coolingCoefficient q 6*(thetaCuspLikelihoodTailProbability q)^3*
        thetaCuspLikelihoodNormalizedMoment q 6 := by
  have hq0 : 0 < q := by linarith
  apply fourth_grade_upper
  · simp only [coolingCoefficient]; positivity
  · simp only [coolingCoefficient]
    have h : 0 ≤ 13*q*(q+3)*(q+3/2)^2+(4*q+15)*(q+3/2)^3 := by positivity
    linarith
  · simp only [coolingCoefficient]; positivity
  · exact coefficient_four_le_six hq
  · exact normalizedMoment_nonneg hq0 1
  · exact normalizedMoment_nonneg hq0 2
  · exact normalizedMoment_nonneg hq0 3
  · exact normalizedMoment_nonneg hq0 4
  · exact normalizedMoment_nonneg hq0 6
  · exact normalizedMoment_nonneg hq0 0
  · simpa only [pow_two,Nat.reduceAdd] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hq0 1 1
  · simpa only [pow_two,Nat.reduceAdd] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hq0 2 2
  · exact thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hq0 1 3
  · exact thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hq0 2 4
  · have h45 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hq0 4
    have h56 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hq0 5
    norm_num only [Nat.reduceAdd] at h45 h56
    linarith

theorem gradeSix_normalized_upper {q : ℝ} (hq : 3/2 ≤ q) :
    gradeSix q (thetaCuspLikelihoodNormalizedMoment q) ≤
      coolingCoefficient q 6*(thetaCuspLikelihoodTailProbability q)^5*
        thetaCuspLikelihoodNormalizedMoment q 6 := by
  have hq0 : 0 < q := by linarith
  let e := thetaCuspLikelihoodNormalizedMoment q
  let p := thetaCuspLikelihoodTailProbability q
  have hp : 0 ≤ p := normalizedMoment_nonneg hq0 0
  have he2 : 0 ≤ e 2 := normalizedMoment_nonneg hq0 2
  have h11 : (e 1)^2 ≤ p*e 2 := by
    simpa only [e,p,pow_two,Nat.reduceAdd] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hq0 1 1
  have h22 : (e 2)^2 ≤ p*e 4 := by
    simpa only [e,p,pow_two,Nat.reduceAdd] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hq0 2 2
  have h24 : e 2*e 4 ≤ p*e 6 :=
    thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hq0 2 4
  have h222 : (e 2)^3 ≤ p^2*e 6 := by
    calc
      (e 2)^3 = e 2*(e 2)^2 := by ring
      _ ≤ e 2*(p*e 4) := mul_le_mul_of_nonneg_left h22 he2
      _ = p*(e 2*e 4) := by ring
      _ ≤ p*(p*e 6) := mul_le_mul_of_nonneg_left h24 hp
      _ = p^2*e 6 := by ring
  have h6 : (e 1)^6 ≤ p^5*e 6 := by
    calc
      (e 1)^6 = ((e 1)^2)^3 := by ring
      _ ≤ (p*e 2)^3 := by gcongr
      _ = p^3*(e 2)^3 := by ring
      _ ≤ p^3*(p^2*e 6) := mul_le_mul_of_nonneg_left h222 (by positivity)
      _ = p^5*e 6 := by ring
  have hc6 : 0 ≤ coolingCoefficient q 6 := by simp only [coolingCoefficient]; positivity
  simpa only [gradeSix,e,p,mul_assoc] using mul_le_mul_of_nonneg_left h6 hc6

theorem cooling_cumulant_lower_pair {q : ℝ} (hq : 3/2 ≤ q) :
    coolingFunctional q (thetaCuspLikelihoodNormalizedMoment q)-
      gradeTwo q (thetaCuspLikelihoodNormalizedMoment q)-
      (402*(thetaCuspLikelihoodTailProbability q)^3+120*(thetaCuspLikelihoodTailProbability q)^5)*
        coolingCoefficient q 6*thetaCuspLikelihoodNormalizedMoment q 6 ≤
      coolingFunctional q (likelihoodCumulant q) := by
  rw [cooling_cumulant_grades]
  have h3 := gradeThree_normalized_nonneg hq
  have h4 := gradeFour_normalized_upper hq
  have h5 := gradeFive_normalized_nonneg hq
  have h6 := gradeSix_normalized_upper hq
  nlinarith only [h3,h4,h5,h6]
end
end RHTower.ThetaCuspDefect

