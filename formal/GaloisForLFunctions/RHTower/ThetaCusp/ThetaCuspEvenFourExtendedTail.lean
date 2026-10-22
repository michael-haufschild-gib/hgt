import GaloisForLFunctions.HTGeometry.FirstAtomEvenTailExtendedReserve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourExplicitTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomScaleSevenProfiles
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspScaleSevenCompensationSource
/-!
# Complete compensated even-source positivity beyond center one

The first-atom reserve extends to scale fifteen. Retaining the `32^k`
balancing factor bounds every complete-source entry error by `2 / 10^(9 : ℕ)`
at scale twenty-one, preserving a determinant floor of `1 / 20000`.
The scale-seven mass and slope estimates then control the compensation
in twelfth-entry units. Every coefficient in `[0, 3*10^(12 : ℕ)]` has positive
Schur margin for `x ≥ 1`, including the actual canonical coefficient.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry

/-- Inverse scale on the extended complete-source ray. -/
theorem inverseScale_bounds_of_twentyOne_le {x : ℝ}
    (hq : 21 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ∧
      (thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ≤ 1/21 := by
  constructor
  · positivity
  · simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 21) hq

/-- Exact inverse-scale formula for the previously unbounded twelfth entry. -/
theorem thetaCuspFirstAtomScaledEvenJet_six_eq_profile_of_twentyOne_le {x : ℝ}
    (hq : 21 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 6 x =
      HTGeometry.firstAtomEvenTailProfile 6 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by nlinarith
  have hu := inverseScale_bounds_of_twentyOne_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/21 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_12, thetaCuspSourceTerm_one_eq_scale_profile]
  norm_num [HTGeometry.firstAtomEvenTailProfile]
  dsimp [HTGeometry.firstAtomEvenTailNumerator6, HTGeometry.firstAtomOddTailDenominator]
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  ring

/-- Every balanced entry uses the actual first atom in its proved rational profile. -/
theorem thetaCuspFirstAtomScaledEvenJet_fin_eq_profile_of_twentyOne_le {x : ℝ}
    (hq : 21 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : Fin 7) :
    thetaCuspFirstAtomScaledEvenJet k.val x =
      HTGeometry.firstAtomEvenTailProfile k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  fin_cases k
  · have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
    have hf := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))).ne'
    simp [thetaCuspFirstAtomScaledEvenJet, thetaCuspFirstAtomReflectionJet,
      HTGeometry.firstAtomEvenTailProfile]
    field_simp [hf]
  · simpa [HTGeometry.firstAtomEvenTailProfile] using thetaCuspFirstAtomScaledEvenJet_1_eq_profile_of_seven_le (by linarith)
  · simpa [HTGeometry.firstAtomEvenTailProfile] using thetaCuspFirstAtomScaledEvenJet_2_eq_profile_of_seven_le (by linarith)
  · simpa [HTGeometry.firstAtomEvenTailProfile] using thetaCuspFirstAtomScaledEvenJet_3_eq_profile_of_seven_le (by linarith)
  · simpa [HTGeometry.firstAtomEvenTailProfile] using thetaCuspFirstAtomScaledEvenJet_4_eq_profile_of_seven_le (by linarith)
  · simpa [HTGeometry.firstAtomEvenTailProfile] using thetaCuspFirstAtomScaledEvenJet_5_eq_profile_of_seven_le (by linarith)
  · exact thetaCuspFirstAtomScaledEvenJet_six_eq_profile_of_twentyOne_le hq

/-- Cubing the proved exponential bound calibrates the complete likelihood tail. -/
theorem base_scale_twentyOne_le :
    Real.exp (3*Real.pi)/399 * Real.exp (-(3*(21 : ℝ))) ≤
      32/(1300000000 : ℝ)^(3 : ℕ) := by
  have h63 : (1300000000 : ℝ)^(3 : ℕ) < Real.exp 63 := by
    have hp := pow_lt_pow_left₀ exp_twentyOne_gt (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    exact hp
  rw [show -(3*(21 : ℝ)) = -63 by norm_num, Real.exp_neg]
  rw [show Real.exp (3*Real.pi)/399*(Real.exp 63)⁻¹ =
      Real.exp (3*Real.pi)/(399*Real.exp 63) by field_simp]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 399*Real.exp 63)).mpr
  nlinarith [exp_three_pi_lt_12704]

/-- Keep the balancing denominator while estimating every moment through order twelve. -/
theorem abs_thetaCuspNativeScaledEvenJet_sub_first_div_balancing_le_of_twentyOne_le
    {k : ℕ} (hk : k ≤ 6) {x : ℝ}
    (hq : 21 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x| /
      (32 : ℝ)^k ≤ 2/(10 : ℝ)^(9 : ℕ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hkr : ((2*k : ℕ) : ℝ) ≤ 12 := by exact_mod_cast (by omega : 2*k ≤ 12)
  have hqe : ((2*k : ℕ) : ℝ)+6 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hb := abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective k hx hqe
  have hq1 : 1 ≤ q := by dsimp [q]; linarith
  have he0 := (regimeOneLikelihoodScale_pos x).le
  have hp18 : (18 : ℝ)^k ≤ (18 : ℝ)^(6 : ℕ) := pow_le_pow_right₀ (by norm_num) hk
  have hpq : q^k ≤ q^(6 : ℕ) := pow_le_pow_right₀ hq1 hk
  have hprod := mul_le_mul hp18 hpq (pow_nonneg (by linarith : 0 ≤ q) k) (by positivity)
  have hs := mul_le_mul_of_nonneg_right hprod he0
  have hq6 := pow_mul_regimeOneLikelihoodScale_le (k := 6) (A₁ := 21)
    (by norm_num) (by norm_num) hq
  calc
    |thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x| /(32 : ℝ)^k ≤
        (27*(24 : ℝ)^(2*k)*q^k*regimeOneLikelihoodScale x)/(32 : ℝ)^k :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = 27*(18 : ℝ)^k*q^k*regimeOneLikelihoodScale x := by
      rw [pow_mul, show (24 : ℝ)^(2 : ℕ) = 18*32 by norm_num, mul_pow]
      field_simp
    _ ≤ 27*(18 : ℝ)^(6 : ℕ)*(q^(6 : ℕ)*regimeOneLikelihoodScale x) := by nlinarith only [hs]
    _ ≤ 27*(18 : ℝ)^(6 : ℕ)*((21 : ℝ)^(6 : ℕ)*
        (Real.exp (3*Real.pi)/399*Real.exp (-(3*(21 : ℝ))))) :=
      mul_le_mul_of_nonneg_left hq6 (by positivity)
    _ ≤ 27*(18 : ℝ)^(6 : ℕ)*((21 : ℝ)^(6 : ℕ)*(32/(1300000000 : ℝ)^(3 : ℕ))) := by
      gcongr
      exact base_scale_twentyOne_le
    _ ≤ 2/(10 : ℝ)^(9 : ℕ) := by norm_num
/-- Balancing preserves the complete-source accuracy of every entry. -/
theorem abs_thetaCuspNativeEvenTailBalanced_sub_first_le_of_twentyOne_le {x : ℝ}
    (hq : 21 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : Fin 7) :
    |thetaCuspNativeEvenTailBalanced k x-
      HTGeometry.firstAtomEvenTailBalanced k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹)| ≤
        2/(10 : ℝ)^(9 : ℕ) := by
  have he := abs_thetaCuspNativeScaledEvenJet_sub_first_div_balancing_le_of_twentyOne_le
    (by omega : k.val ≤ 6) hq
  unfold thetaCuspNativeEvenTailBalanced HTGeometry.firstAtomEvenTailBalanced
  rw [← thetaCuspFirstAtomScaledEvenJet_fin_eq_profile_of_twentyOne_le hq k]
  rw [show thetaCuspNativeScaledEvenJet k.val x/(32 : ℝ)^k.val-
      (if k.val = 6 then 100000000/(32 : ℝ)^(6 : ℕ) else 0)-
      (thetaCuspFirstAtomScaledEvenJet k.val x/(32 : ℝ)^k.val-
        (if k.val = 6 then 100000000/(32 : ℝ)^(6 : ℕ) else 0)) =
      (thetaCuspNativeScaledEvenJet k.val x-thetaCuspFirstAtomScaledEvenJet k.val x)/(32 : ℝ)^k.val by ring]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 32^k.val)]
  exact he

/-- The entire infinite-source perturbation costs less than half the exact matrix reserve. -/
theorem thetaCuspNativeEvenTailBalancedDet_lower_of_twentyOne_le {x : ℝ}
    (hq : 21 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (1/20000 : ℝ) ≤ thetaCuspNativeEvenTailBalancedDet x := by
  have hu := inverseScale_bounds_of_twentyOne_le hq
  have hb (k : Fin 7) := HTGeometry.firstAtomEvenTailBalanced_abs_le_of_twentyOne hu.1 hu.2 k
  have he (k : Fin 7) := abs_thetaCuspNativeEvenTailBalanced_sub_first_le_of_twentyOne_le hq k
  have ha (k : Fin 7) : |thetaCuspNativeEvenTailBalanced k x| ≤ 5 := by
    have ht := abs_add_le
      (thetaCuspNativeEvenTailBalanced k x-
        HTGeometry.firstAtomEvenTailBalanced k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
      (HTGeometry.firstAtomEvenTailBalanced k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
    rw [sub_add_cancel] at ht
    linarith [hb k, he k]
  have herr := hankelFourDet_error_le (M := 5) (δ := 2/(10 : ℝ)^(9 : ℕ))
    (by norm_num) (by positivity) ha (fun k => (hb k).trans (by norm_num : (4 : ℝ) ≤ 5)) he
  have hd := HTGeometry.firstAtomEvenTailBalancedDet_lower_of_fifteen hu.1 (by linarith [hu.2])
  change |thetaCuspNativeEvenTailBalancedDet x-
    HTGeometry.firstAtomEvenTailBalancedDet ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹)| ≤ _ at herr
  have hl := (abs_le.mp herr).1
  linarith only [hl, hd]

/-- The actual complete twelfth-entry Schur coordinate exceeds one hundred million in Gaussian units. -/
theorem thetaCuspNativeEvenFourSchur_normalized_lower_of_twentyOne_le {x : ℝ}
    (hq : 21 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    100000000 < thetaCuspNativeEvenFourSchur x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) := by
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hd : 0 < (32 : ℝ)^(12 : ℕ)*thetaCuspSourceTerm x 1^(8 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(12 : ℕ) := by positivity
  have hhead := (thetaCuspNativeEvenHead_posDef hx.le).det_pos
  have hr := thetaCuspNativeEvenTailBalancedDet_lower_of_twentyOne_le hq
  have hp : 0 < thetaCuspNativeEvenTailBalancedDet x := by linarith
  rw [thetaCuspNativeEvenTailBalancedDet_eq_reserved_ratio hx] at hp
  have hn := (lt_div_iff₀ hd).mp hp
  simp only [zero_mul] at hn
  rw [thetaCuspNativeEvenFourDet_eq_head_mul_schur hx.le] at hn
  have hs : 0 < thetaCuspNativeEvenFourSchur x-
      100000000*thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ) := by
    apply (mul_pos_iff_of_pos_left hhead).mp
    nlinarith only [hn]
  apply (lt_div_iff₀ (by positivity : 0 < thetaCuspSourceTerm x 1^(2 : ℕ)*
    thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ))).mpr
  nlinarith only [hs]
/-- Retaining four inverse-scale powers controls the complete compensation on the extended ray. -/
theorem thetaCuspCenterCompensationSource_six_normalized_lower_of_twentyOne_le {x : ℝ}
    (hq : 21 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -(13/50 : ℝ)/21^(4 : ℕ) ≤ thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let d := deriv thetaCuspFullSource x
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hqp : 0 < q := by dsimp [q]; linarith
  have hb := thetaCuspFullSource_mass_slope_le_scaleSeven (by linarith : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x)
  change F ≤ (101/100)*f ∧ |d| ≤ (201/100)*q*f at hb
  have hprod := mul_le_mul hb.1 hb.2 (abs_nonneg d) (by positivity : (0 : ℝ) ≤ (101/100)*f)
  have hprod1 : F*|d| ≤ (52/25)*q*f^(2 : ℕ) := by
    have hpos : 0 ≤ q*f^(2 : ℕ) := by positivity
    nlinarith only [hprod, hpos]
  have hprod2 := mul_le_mul_of_nonneg_left hprod1 (by positivity : (0 : ℝ) ≤ 2*x)
  have hxd := sixteen_mul_center_le_firstAtomScale hx.le
  change 16*x ≤ q at hxd
  have hscale := mul_le_mul_of_nonneg_right hxd (by positivity : (0 : ℝ) ≤ (13/50)*q*f^(2 : ℕ))
  have hd := neg_abs_le d
  have hneg := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2*x*F)
  have hraw : -(13/50)*q^(2 : ℕ)*f^(2 : ℕ) ≤ thetaCuspCenterCompensationSource x := by
    change -(13/50)*q^(2 : ℕ)*f^(2 : ℕ) ≤ 3*F^(2 : ℕ)+2*x*F*d
    nlinarith only [hprod2, hscale, hneg, sq_nonneg F]
  have hnorm : -(13/50 : ℝ)/q^(4 : ℕ) ≤ thetaCuspCenterCompensationSource x/(f^(2 : ℕ)*q^(6 : ℕ)) := by
    apply (le_div_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(6 : ℕ))).mpr
    calc
      (-(13/50 : ℝ)/q^(4 : ℕ))*(f^(2 : ℕ)*q^(6 : ℕ)) = -(13/50)*q^(2 : ℕ)*f^(2 : ℕ) := by field_simp
      _ ≤ thetaCuspCenterCompensationSource x := hraw
  have hp4 : (21 : ℝ)^(4 : ℕ) ≤ q^(4 : ℕ) := pow_le_pow_left₀ (by norm_num) hq 4
  have hi : (1 : ℝ)/q^(4 : ℕ) ≤ 1/(21 : ℝ)^(4 : ℕ) := one_div_le_one_div_of_le (by norm_num) hp4
  change -(13/50 : ℝ)/21^(4 : ℕ) ≤ thetaCuspCenterCompensationSource x/(f^(2 : ℕ)*q^(6 : ℕ))
  simp only [div_eq_mul_inv] at hi hnorm ⊢
  linarith only [hi, hnorm]
/-- The physical endpoint one already lies beyond scale twenty-one. -/
theorem twentyOne_le_firstAtomScale_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    21 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have h1 : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : (27/10 : ℝ)^(2 : ℕ) ≤ Real.exp 2 := by
    have h := pow_le_pow_left₀ (by norm_num) h1 2
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  have hxexp := Real.exp_le_exp.mpr (show (2 : ℝ) ≤ 2*x by linarith)
  have hp := mul_le_mul_of_nonneg_left (h2.trans hxexp) Real.pi_pos.le
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
  nlinarith [Real.pi_gt_three]
/-- A uniform positive margin survives the full correction throughout its rational coefficient band. -/
theorem thetaCuspNativeEvenFourCompensated_normalized_lower_of_twentyOne_le {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000)
    (hq : 21 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    90000000 < (thetaCuspNativeEvenFourSchur x+C*thetaCuspCenterCompensationSource x) /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) := by
  have hs := thetaCuspNativeEvenFourSchur_normalized_lower_of_twentyOne_le hq
  have hg := thetaCuspCenterCompensationSource_six_normalized_lower_of_twentyOne_le hq
  have hm := mul_le_mul_of_nonneg_left hg hC0
  rw [add_div, mul_div_assoc]
  nlinarith only [hs, hm, hC1]

/-- Literal source positivity on the whole scale-twenty-one ray, with no omitted tail contribution. -/
theorem thetaCuspNativeEvenFourCompensated_posDef_of_twentyOne_le {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000)
    (hq : 21 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hd : 0 < thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ) := by positivity
  have hm := thetaCuspNativeEvenFourCompensated_normalized_lower_of_twentyOne_le hC0 hC1 hq
  have hp : 0 < (thetaCuspNativeEvenFourSchur x+C*thetaCuspCenterCompensationSource x) /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) := by linarith
  rw [thetaCuspNativeEvenFourCompensated_posDef_iff hx.le]
  exact (div_pos_iff_of_pos_right hd).mp hp

/-- One is an explicit physical outer endpoint for the entire bounded coefficient family. -/
theorem thetaCuspNativeEvenFourCompensated_posDef_of_one_le {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000) (hx : 1 ≤ x) :
    (thetaCuspNativeEvenFourCompensated C x).PosDef :=
  thetaCuspNativeEvenFourCompensated_posDef_of_twentyOne_le hC0 hC1
    (twentyOne_le_firstAtomScale_of_one_le hx)

/-- The actual source-selected coefficient satisfies the explicit complete-source tail sign. -/
theorem thetaCuspNativeEvenFourCanonical_posDef_of_one_le :
    ∀ x : ℝ, 1 ≤ x →
      (thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient x).PosDef := by
  intro x hx
  exact thetaCuspNativeEvenFourCompensated_posDef_of_one_le
    thetaCuspNativeEvenCompensationCoefficient_pos.le
    thetaCuspNativeEvenCompensationCoefficient_bounds.2.le hx

/-- The literal weighted matrix is positive past two for every positive aperture. -/
theorem thetaCuspCenterCorrectedEvenFour_posDef_of_two_le {a C r : ℝ}
    (ha : 0 < a) (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000) (hr : 2 ≤ r) :
    (thetaCuspCenterCorrectedEvenFour a C r).PosDef := by
  apply thetaCuspCenterCorrectedEvenFour_posDef_of_source ha hC0 (by linarith)
  exact thetaCuspNativeEvenFourCompensated_posDef_of_one_le hC0 hC1 (by linarith)

/-- Closed canonical weighted tail positivity, uniformly over every positive aperture. -/
theorem thetaCuspCenterCorrectedEvenFourCanonical_posDef_of_two_le :
    ∀ a r : ℝ, 0 < a → 2 ≤ r →
      (thetaCuspCenterCorrectedEvenFour a thetaCuspNativeEvenCompensationCoefficient r).PosDef := by
  intro a r ha hr
  exact thetaCuspCenterCorrectedEvenFour_posDef_of_two_le ha
    thetaCuspNativeEvenCompensationCoefficient_pos.le
    thetaCuspNativeEvenCompensationCoefficient_bounds.2.le hr

/-- Every possible failure in the rational family lies below the fixed outer endpoint one. -/
theorem exists_thetaCuspEvenCompensation_rationalFamily_outer_gap_below_one :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ C x : ℝ,
      1000000000000 ≤ C → C ≤ 3000000000000 → 0 ≤ x → (x < δ ∨ 1 ≤ x) →
        (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  obtain ⟨δ, hδ, hnear⟩ := exists_thetaCuspEvenCompensation_rationalFamily_posDef_near_zero
  refine ⟨min δ (1), lt_min hδ (by norm_num), min_le_right _ _, fun C x hCL hCU hx h => ?_⟩
  rcases h with h | h
  · exact hnear C x hCL hCU hx ((lt_min_iff.mp h).1)
  · exact thetaCuspNativeEvenFourCompensated_posDef_of_one_le (by linarith) hCU h

end
end RHTower
