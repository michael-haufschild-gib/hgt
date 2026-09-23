import GaloisForLFunctions.RHTower.ThetaCuspMiddleCompensationBounds
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomAffineEvenFour
import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomCentralFactorial
/-!
# Complete center compensation reserve on scales five through eight

Complete first-moment transport controls the source slope. Its negative
quadratic correction coefficient is transferred through the full mass ceiling
and absorbed in 240 normalized units. Four first-atom coordinate reserves
remain available for the separate reflection-entry comparison.
-/
namespace RHTower
noncomputable section
set_option maxHeartbeats 1000000
/-- The complete-source slope budget fits strictly inside 240 normalized last-coordinate units. -/
theorem middleCompensationBudget_pos {q : ℝ} (hq : 5 ≤ q) :
    0 < 240*(8*q)^(6 : ℕ)+1000000000000*(101/100 : ℝ)^(2 : ℕ)*(1+(9/5)*q-(2/5)*q^(2 : ℕ)) := by
  by_cases hu : q ≤ 6
  · let u := 6-q
    let v := q-5
    have hu0 : 0 ≤ u := by dsimp [u]; linarith
    have hv0 : 0 ≤ v := by dsimp [v]; linarith
    have huv : u+v = 1 := by dsimp [u,v]; ring
    have huvpos : 0 < u ∨ 0 < v := by
      by_cases h : 0 < u
      · exact Or.inl h
      · exact Or.inr (by linarith)
    have hp : 0 <
        240*(8*(5*u+6*v))^(6 : ℕ)+
          1000000000000*(101/100 : ℝ)^(2 : ℕ)*
            ((u+v)^(2 : ℕ)+(9/5)*(5*u+6*v)*(u+v)-(2/5)*(5*u+6*v)^(2 : ℕ))*(u+v)^(4 : ℕ) := by
      rcases huvpos with hpos | hpos
      all_goals ring_nf; positivity
    have he : 5*u+6*v = q := by dsimp [u,v]; ring
    rw [he,huv] at hp
    norm_num at hp ⊢
    exact hp
  · let v := q-6
    have hv : 0 ≤ v := by dsimp [v]; linarith
    have he : q = 6+v := by dsimp [v]; ring
    rw [he]
    have hp : 0 <
        240*(8*(6+v))^(6 : ℕ)+1000000000000*(101/100 : ℝ)^(2 : ℕ)*
          (1+(9/5)*(6+v)-(2/5)*(6+v)^(2 : ℕ)) := by
      have hcert : 0 <
          240*(8*(6+v))^(6 : ℕ)+1000000000000*(101/100 : ℝ)^(2 : ℕ)*
            (1+(9/5)*(6+v)-(2/5)*(6+v)^(2 : ℕ))-700000000000*(v-1/10)^(2 : ℕ) := by
        ring_nf
        positivity
      nlinarith only [hcert,sq_nonneg (v-1/10)]
    exact hp
private theorem middleReserve_first_slope_eq (x : ℝ) :
    deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)*
        (-8*thetaCuspSingleAtomReflectionScale 1 x^(3 : ℕ)+
          30*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-15*thetaCuspSingleAtomReflectionScale 1 x) := by
  have h := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
  rw [iteratedDeriv_one] at h
  rw [h]
  dsimp [thetaCuspGaussianScaleJet, thetaCuspGaussianScaleMoment]
  ring

private theorem middleReserve_first_slope_affine_lower {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (9/2-2*thetaCuspSingleAtomReflectionScale 1 x)*thetaCuspSourceTerm x 1 ≤
      deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hqp : 0 ≤ q := by dsimp [q]; linarith
  rw [middleReserve_first_slope_eq, thetaCuspSourceTerm_one_eq_scale_profile]
  change (9/2-2*q)*(Real.exp (x/2-q)*(4*q^(2 : ℕ)-6*q)) ≤
    Real.exp (x/2-q)*(-8*q^(3 : ℕ)+30*q^(2 : ℕ)-15*q)
  nlinarith only [mul_nonneg (Real.exp_pos (x/2-q)).le hqp]


private theorem middleReserve_full_slope_transport {L x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hfL : L*thetaCuspSourceTerm x 1 ≤ deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x) :
    (L-thetaCuspSingleAtomReflectionScale 1 x/250)*thetaCuspFullSource x ≤
      deriv thetaCuspFullSource x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let R := thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 0
  let M := thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 1
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hR : 0 ≤ R := thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hM : M ≤ 1/500 := thetaCuspHigherLikelihoodSpectralMoment_one_le_middle hq
  have hF : f ≤ F := (thetaCuspFullSource_mass_bounds_middle hq).1
  have heF : F = f*(1+R) := by
    dsimp [F, f, R]
    rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition hB,
      thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
  have hcore : L*F ≤ deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x*(1+R) := by
    rw [heF]
    nlinarith only [mul_le_mul_of_nonneg_right hfL (show 0 ≤ 1+R by linarith)]
  have htail := mul_le_mul_of_nonneg_left hM (show 0 ≤ 2*q*f by positivity)
  have hmass := mul_le_mul_of_nonneg_left hF (show 0 ≤ q/250 by positivity)
  have hd : deriv thetaCuspFullSource x =
      deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x*(1+R)-2*q*f*M :=
    deriv_thetaCuspFullSource_eq_likelihood_moment hx
  change (L-q/250)*F ≤ deriv thetaCuspFullSource x
  linarith only [hcore, htail, hmass, hd]


/-- The complete moment transport keeps its affine slope through scale eight. -/
theorem thetaCuspFullSource_slope_affine_lower_eight {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 8) :
    (4-2*thetaCuspSingleAtomReflectionScale 1 x)*thetaCuspFullSource x ≤
      deriv thetaCuspFullSource x := by
  have ht := middleReserve_full_slope_transport hq (middleReserve_first_slope_affine_lower hq)
  have hf := thetaCuspFullSource_pos_all x
  have hc : 4-2*thetaCuspSingleAtomReflectionScale 1 x ≤
      9/2-2*thetaCuspSingleAtomReflectionScale 1 x-thetaCuspSingleAtomReflectionScale 1 x/250 := by linarith
  exact (mul_le_mul_of_nonneg_right hc hf.le).trans ht

/-- Complete-source center correction on the remaining middle scale interval. -/
theorem thetaCuspCenterCompensationSource_quadratic_lower_eight {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 8) :
    (1+(9/5)*thetaCuspSingleAtomReflectionScale 1 x-
      (2/5)*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ))*thetaCuspFullSource x^(2 : ℕ) ≤
      thetaCuspCenterCompensationSource x := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hF := thetaCuspFullSource_pos_all x
  have hd := mul_le_mul_of_nonneg_left (thetaCuspFullSource_slope_affine_lower_eight hq hqu)
    (show 0 ≤ 2*x*thetaCuspFullSource x by positivity)
  have hc := ten_mul_center_add_five_halves_le_firstAtomScale hx.le
  have hr := mul_nonneg
    (show 0 ≤ thetaCuspSingleAtomReflectionScale 1 x-10*x-5/2 by linarith)
    (show 0 ≤ (2*thetaCuspSingleAtomReflectionScale 1 x-4)*thetaCuspFullSource x^(2 : ℕ) by
      apply mul_nonneg (by linarith) (sq_nonneg _))
  unfold thetaCuspCenterCompensationSource
  nlinarith only [hd,hr]

/-- The full compensation costs strictly fewer than 240 last-coordinate units on scales five to eight. -/
theorem thetaCuspFullCompensation_lower_middle_240 {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 8) :
    -240*thetaCuspSourceTerm x 1^(2 : ℕ)*(8*thetaCuspSingleAtomReflectionScale 1 x)^(6 : ℕ) <
      1000000000000*thetaCuspCenterCompensationSource x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let B := 1+(9/5)*q-(2/5)*q^(2 : ℕ)
  have hql : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos (thetaCusp_pos_of_thirtySevenTenths_le hql)
    (by norm_num : 0 < (1 : ℕ))
  have hF := thetaCuspFullSource_pos_all x
  have hB : B ≤ 0 := by
    have he : B = (5-q)*(2*q+1)/5 := by dsimp [B]; ring
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by dsimp [q]; linarith) (by dsimp [q]; linarith)) (by norm_num)
  have hm : F^(2 : ℕ) ≤ ((101/100)*f)^(2 : ℕ) :=
    pow_le_pow_left₀ hF.le (thetaCuspFullSource_mass_bounds_middle hql).2 2
  have hg : B*F^(2 : ℕ) ≤ thetaCuspCenterCompensationSource x :=
    thetaCuspCenterCompensationSource_quadratic_lower_eight hql hqu
  have hb := mul_le_mul_of_nonpos_left hm hB
  have hh : B*((101/100)*f)^(2 : ℕ) ≤ thetaCuspCenterCompensationSource x := hb.trans hg
  have hL := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1000000000000)
  have hp := mul_pos (middleCompensationBudget_pos hq) (sq_pos_of_pos hf)
  change (0 : ℝ) < (240*(8*q)^(6 : ℕ)+1000000000000*(101/100 : ℝ)^(2 : ℕ)*B)*f^(2 : ℕ) at hp
  change -240*f^(2 : ℕ)*(8*q)^(6 : ℕ) < _
  nlinarith only [hL,hp]
/-- Four explicit coordinate reserves survive the complete compensation on the middle interval. -/
theorem firstAtomEnergy_fullCompensation_middle_reserve {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 8) (c : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let h := 6/(2*q-3)^(2 : ℕ)
    let y := firstAtomCentralCoordinates ((2*q)⁻¹) (8*q) c
    thetaCuspSourceTerm x 1^(2 : ℕ)*
      ((y 0+h*y 1)^(2 : ℕ)+(7/8)*(y 1)^(2 : ℕ)+3*(y 2)^(2 : ℕ)+42*(y 3)^(2 : ℕ)) ≤
      firstAtomEvenEnergy x c+1000000000000*thetaCuspCenterCompensationSource x*(c 3)^(2 : ℕ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hqp : 0 < q := by dsimp [q]; linarith
  have hd : 2*q-3 ≠ 0 := by dsimp [q]; linarith
  have hv : 0 ≤ (2*q)⁻¹ := by positivity
  have hvU : (2*q)⁻¹ ≤ (1/8 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < 2*q)).mpr
    dsimp [q]
    linarith
  have hrel : (6/(2*q-3)^(2 : ℕ))*(1-3*(2*q)⁻¹)^(2 : ℕ) = 6*((2*q)⁻¹)^(2 : ℕ) := by
    field_simp [hqp.ne',hd]
  let y := firstAtomCentralCoordinates ((2*q)⁻¹) (8*q) c
  have hm := mul_le_mul_of_nonneg_left (centralHermiteQuadratic_lower hv hvU hrel y)
    (sq_nonneg (thetaCuspSourceTerm x 1))
  have hid := firstAtomEvenEnergy_eq_centralHermite
    (by linarith : 3/2 < thetaCuspSingleAtomReflectionScale 1 x) c
  change firstAtomEvenEnergy x c = thetaCuspSourceTerm x 1^(2 : ℕ)*
    centralHermiteQuadratic ((2*q)⁻¹) (6/(2*q-3)^(2 : ℕ)) y at hid
  rw [← hid] at hm
  have hc := mul_le_mul_of_nonneg_right (thetaCuspFullCompensation_lower_middle_240 hq hqu).le
    (sq_nonneg (c 3))
  have hy3 : y 3 = (8*q)^(3 : ℕ)*c 3 := rfl
  have he : thetaCuspSourceTerm x 1^(2 : ℕ)*(y 3)^(2 : ℕ) =
      thetaCuspSourceTerm x 1^(2 : ℕ)*(8*q)^(6 : ℕ)*(c 3)^(2 : ℕ) := by rw [hy3]; ring
  change thetaCuspSourceTerm x 1^(2 : ℕ)*
    ((y 0+(6/(2*q-3)^(2 : ℕ))*y 1)^(2 : ℕ)+(7/8)*(y 1)^(2 : ℕ)+3*(y 2)^(2 : ℕ)+42*(y 3)^(2 : ℕ)) ≤ _
  nlinarith only [hm,hc,he]
end
end RHTower
