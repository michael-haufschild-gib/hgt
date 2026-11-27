import GaloisForLFunctions.HTGeometry.GaussianSmallBallLowerBound
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.BoxMass

/-! # Gaussian mass of a narrow box with one large field -/
open Set MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
noncomputable section

private def densityFactor : ℝ := (sqrt (2*π))⁻¹

private theorem interval_floor (a : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    (2*densityFactor*r)*exp (-((|a|+1)^2)/2) ≤ (gaussianReal 0 1).real (Icc (a-r) (a+r)) := by
  let p := densityFactor*exp (-((|a|+1)^2)/2)
  have hp : 0 ≤ p := mul_nonneg (by dsimp [densityFactor]; positivity) (exp_pos _).le
  have hpdf (x : ℝ) (hx : x∈Icc (a-r) (a+r)) : ENNReal.ofReal p ≤ gaussianPDF 0 1 x := by
    have hb : |x-a| ≤ r := abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
    have hx₁ : |x| ≤ |a|+1 := calc
      _ = |a+(x-a)| := by congr 1; ring
      _ ≤ _ := (abs_add_le ..).trans (add_le_add le_rfl (hb.trans hr₁))
    have hsq := pow_le_pow_left₀ (abs_nonneg x) hx₁ 2
    rw [sq_abs] at hsq
    apply ENNReal.ofReal_le_ofReal
    have he : gaussianPDFReal 0 1 x=densityFactor*exp (-x^2/2) := by
      unfold gaussianPDFReal densityFactor
      norm_num
    rw [he]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith only [hsq])) (by dsimp [densityFactor]; positivity)
  have hmass : ENNReal.ofReal (p*(2*r)) ≤ gaussianReal 0 1 (Icc (a-r) (a+r)) := by
    rw [gaussianReal_apply 0 (by norm_num)]
    have hm : ∫⁻ _ in Icc (a-r) (a+r), ENNReal.ofReal p ≤
        ∫⁻ x in Icc (a-r) (a+r), gaussianPDF 0 1 x := by
      refine setLIntegral_mono_ae (by fun_prop) ?_
      filter_upwards with x hx using hpdf x hx
    rwa [setLIntegral_const,Real.volume_Icc,show a+r-(a-r)=2*r by ring,←ENNReal.ofReal_mul hp] at hm
  have h := ENNReal.toReal_mono (measure_ne_top _ _) hmass
  rw [ENNReal.toReal_ofReal (mul_nonneg hp (mul_nonneg zero_le_two hr))] at h
  exact (show (2*densityFactor*r)*exp (-((|a|+1)^2)/2)=p*(2*r) by dsimp only [p]; ring).le.trans h

/-- Only the selected widths shrink by s. The shift cost depends on
the sum of squared coordinate bounds, so a single large field pays once. -/
theorem gaussian_rectangular_floor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (a : ι→ℝ) {r s : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (hs : 1 ≤ s) :
    let w := fun i => if i∈S then r/s else r
    let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
    (2*(sqrt (2*π))⁻¹*r)^(Fintype.card ι)*exp (-(∑ i, (|a i|+1)^2)/2) ≤
      s^S.card * μ.real (Set.univ.pi fun i => Icc (a i-w i) (a i+w i)) := by
  intro w μ
  have hs₀ := zero_lt_one.trans_le hs
  have hw (i) : 0 ≤ w i ∧ w i ≤ 1 := by
    by_cases hi : i∈S
    · exact ⟨by dsimp only [w]; rw [if_pos hi]; positivity,
        (if_pos hi).le.trans ((div_le_self hr.le hs).trans hr₁)⟩
    · simpa only [w,if_neg hi] using And.intro hr.le hr₁
  let E (i : ι) := Icc (a i-w i) (a i+w i)
  let p (i : ι) := (2*densityFactor*w i)*exp (-((|a i|+1)^2)/2)
  have hmass : (∏ i, p i) ≤ μ.real (Set.univ.pi E) := by
    change _ ≤ ((Measure.pi _) (Set.univ.pi E)).toReal
    rw [Measure.pi_pi,ENNReal.toReal_prod]
    exact prod_le_prod (fun i _ => mul_nonneg (mul_nonneg (by dsimp [densityFactor]; positivity) (hw i).1) (exp_pos _).le)
      (fun i _ => interval_floor _ (hw i).1 (hw i).2)
  have hsprod : s^S.card=∏ i : ι, if i∈S then s else 1 := by simp
  have hfix (i : ι) : (if i∈S then s else 1)*p i=(2*densityFactor*r)*exp (-((|a i|+1)^2)/2) := by
    by_cases hi : i∈S <;> simp only [p,w,hi,ite_true,ite_false,one_mul]
    field_simp [hs₀.ne']
  have heq : s^S.card*(∏ i, p i) =
      (2*densityFactor*r)^(Fintype.card ι)*exp (-(∑ i, (|a i|+1)^2)/2) := by
    rw [hsprod,←prod_mul_distrib]
    simp only [hfix]
    rw [prod_mul_distrib,prod_const,card_univ,←Real.exp_sum,←sum_div,sum_neg_distrib]
  exact heq.symm.le.trans (mul_le_mul_of_nonneg_left hmass (pow_nonneg hs₀.le _))

#print axioms gaussian_rectangular_floor
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
