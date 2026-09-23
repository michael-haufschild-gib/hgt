import GaloisForLFunctions.HTGeometry.FirstAtomEvenTailEntrywiseReserve
import GaloisForLFunctions.RHTower.ThetaCuspSupportScaleReflectionApproximation
import GaloisForLFunctions.RHTower.ThetaCuspEvenFourExtendedTail
/-!
# Complete compensated even-source positivity beyond four fifths

At scale fifteen, each balanced entry has error at most `120^k*2/10^(17 : ℕ)`.
The entry-specific determinant bound leaves reserve `1/25000`. The actual
compensated Schur coordinate then exceeds eighty million in Gaussian units
for every coefficient in `[0, 3*10^(12 : ℕ)]`. This closes the literal complete
even source on `x >= 4/5`, including the canonical coefficient and weighted
source. The inner source comparison and global degree-six sign remain open.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
/-- Inverse scale on the extended complete-source ray. -/
theorem inverseScale_bounds_of_fifteen_le {x : ℝ}
    (hq : 15 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ∧
      (thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ≤ 1/15 := by
  constructor
  · positivity
  · simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 15) hq

/-- Exact inverse-scale formula for the previously unbounded twelfth entry. -/
theorem thetaCuspFirstAtomScaledEvenJet_six_eq_profile_of_fifteen_le {x : ℝ}
    (hq : 15 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 6 x =
      HTGeometry.firstAtomEvenTailProfile 6 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by nlinarith
  have hu := inverseScale_bounds_of_fifteen_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/15 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_12, thetaCuspSourceTerm_one_eq_scale_profile]
  norm_num [HTGeometry.firstAtomEvenTailProfile]
  dsimp [HTGeometry.firstAtomEvenTailNumerator6, HTGeometry.firstAtomOddTailDenominator]
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  ring

/-- Every balanced entry uses the actual first atom in its proved rational profile. -/
theorem thetaCuspFirstAtomScaledEvenJet_fin_eq_profile_of_fifteen_le {x : ℝ}
    (hq : 15 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : Fin 7) :
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
  · exact thetaCuspFirstAtomScaledEvenJet_six_eq_profile_of_fifteen_le hq

/-- Reflection retains the linear and quadratic likelihood errors after balancing. -/
theorem abs_thetaCuspNativeScaledEvenJet_sub_first_div_balancing_le_supportScale
    (k : ℕ) {x : ℝ} (hx : 0 < x)
    (h6 : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq : ((2*k : ℕ) : ℝ)+3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x| /(32 : ℝ)^k ≤
      18*(8 : ℝ)^k*thetaCuspSingleAtomReflectionScale 1 x^k*regimeOneLikelihoodScale x+
        9*(18 : ℝ)^k*thetaCuspSingleAtomReflectionScale 1 x^k*regimeOneLikelihoodScale x^(2 : ℕ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hqpos : 0 < q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have heq : thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x =
      (-1 : ℝ)^k * ((thetaCuspNativeReflectionJet (2*k) x-thetaCuspFirstAtomReflectionJet (2*k) x) /
        thetaCuspSourceTerm x 1^(2 : ℕ)) / q^k := by
    unfold thetaCuspNativeScaledEvenJet thetaCuspFirstAtomScaledEvenJet
    dsimp [q]
    field_simp [hf.ne', hqpos.ne']
  rw [heq, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (pow_nonneg hqpos.le k), div_div]
  apply (div_le_iff₀ (by positivity : 0 < q^k*(32 : ℝ)^k)).mpr
  have hb := abs_thetaCuspNativeReflectionJet_relative_error_le_supportScale (2*k) hx h6 hq
  calc
    _ ≤ 18*(16*q)^(2*k)*regimeOneLikelihoodScale x+
        9*(24*q)^(2*k)*regimeOneLikelihoodScale x^(2 : ℕ) := hb
    _ = _ := by
      dsimp only [q]
      rw [mul_pow, mul_pow, pow_mul (16 : ℝ), pow_mul (24 : ℝ),
        show (16 : ℝ)^(2 : ℕ) = 8*32 by norm_num, show (24 : ℝ)^(2 : ℕ) = 18*32 by norm_num]
      simp only [mul_pow, Nat.two_mul, pow_add]
      ring

theorem exp_fifteen_gt : (3200000 : ℝ) < Real.exp 15 := by
  have h := Real.exp_one_gt_d9
  have h15 : Real.exp 15 = Real.exp 1 ^ (15 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h15]
  calc (3200000 : ℝ) < 2.7182818283 ^ (15 : ℕ) := by norm_num
    _ < Real.exp 1 ^ (15 : ℕ) := pow_lt_pow_left₀ h (by norm_num) (by norm_num)

/-- A rational exponential ceiling for the complete likelihood tail at scale fifteen. -/
theorem base_scale_fifteen_le :
    Real.exp (3*Real.pi)/399*Real.exp (-(3*(15 : ℝ))) ≤ 32/(3200000 : ℝ)^(3 : ℕ) := by
  have h45 : (3200000 : ℝ)^(3 : ℕ) < Real.exp 45 := by
    have hp := pow_lt_pow_left₀ exp_fifteen_gt (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    exact hp
  rw [show -(3*(15 : ℝ)) = -45 by norm_num, Real.exp_neg]
  rw [show Real.exp (3*Real.pi)/399*(Real.exp 45)⁻¹ =
      Real.exp (3*Real.pi)/(399*Real.exp 45) by field_simp]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 399*Real.exp 45)).mpr
  nlinarith [exp_three_pi_lt_12704]

/-- The complete reflected error retains its own power of 120 at each derivative order. -/
theorem abs_thetaCuspNativeScaledEvenJet_sub_first_div_balancing_le_of_fifteen_le
    {k : ℕ} (hk : k ≤ 6) {x : ℝ}
    (hq : 15 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x| /(32 : ℝ)^k ≤
      (120 : ℝ)^k*(2/(10 : ℝ)^(17 : ℕ)) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let ε := regimeOneLikelihoodScale x
  let E : ℝ := 32/(3200000 : ℝ)^(3 : ℕ)
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hkr : ((2*k : ℕ) : ℝ) ≤ 12 := by exact_mod_cast (by omega : 2*k ≤ 12)
  have hqe : ((2*k : ℕ) : ℝ)+3 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hb := abs_thetaCuspNativeScaledEvenJet_sub_first_div_balancing_le_supportScale k hx (by linarith) hqe
  have he0 : 0 ≤ ε := (regimeOneLikelihoodScale_pos x).le
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hp (j : ℕ) (hj : j ≤ 6) : q^j*ε ≤ (15 : ℝ)^j*E := by
    have hjr : (j : ℝ) ≤ 6 := by exact_mod_cast hj
    have h := pow_mul_regimeOneLikelihoodScale_le (k := j) (A₁ := 15)
      (by norm_num) (by linarith) hq
    calc
      _ ≤ (15 : ℝ)^j*(Real.exp (3*Real.pi)/399*Real.exp (-(3*(15 : ℝ)))) := h
      _ ≤ (15 : ℝ)^j*E := mul_le_mul_of_nonneg_left base_scale_fifteen_le (by positivity)
  have heE : ε ≤ E := by simpa using hp 0 (by omega)
  have hqk := hp k hk
  have hqksq : q^k*ε^(2 : ℕ) ≤ (15 : ℝ)^k*E^(2 : ℕ) := by
    have h := mul_le_mul hqk heE he0 (by positivity : 0 ≤ (15 : ℝ)^k*E)
    nlinarith only [h]
  calc
    _ ≤ 18*(8 : ℝ)^k*(q^k*ε)+9*(18 : ℝ)^k*(q^k*ε^(2 : ℕ)) := by simpa only [mul_assoc] using hb
    _ ≤ 18*(8 : ℝ)^k*((15 : ℝ)^k*E)+9*(18 : ℝ)^k*((15 : ℝ)^k*E^(2 : ℕ)) := by gcongr
    _ = 18*(120 : ℝ)^k*E+9*(270 : ℝ)^k*E^(2 : ℕ) := by
      rw [show (120 : ℝ) = 8*15 by norm_num, show (270 : ℝ) = 18*15 by norm_num]
      simp only [mul_pow]
      ring
    _ ≤ (120 : ℝ)^k*(2/(10 : ℝ)^(17 : ℕ)) := by interval_cases k <;> norm_num [E]

/-- Balancing preserves the complete-source accuracy of every entry. -/
theorem abs_thetaCuspNativeEvenTailBalanced_sub_first_le_of_fifteen_le {x : ℝ}
    (hq : 15 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : Fin 7) :
    |thetaCuspNativeEvenTailBalanced k x-
      HTGeometry.firstAtomEvenTailBalanced k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹)| ≤
        (120 : ℝ)^k.val*(2/(10 : ℝ)^(17 : ℕ)) := by
  have he := abs_thetaCuspNativeScaledEvenJet_sub_first_div_balancing_le_of_fifteen_le
    (by omega : k.val ≤ 6) hq
  unfold thetaCuspNativeEvenTailBalanced HTGeometry.firstAtomEvenTailBalanced
  rw [← thetaCuspFirstAtomScaledEvenJet_fin_eq_profile_of_fifteen_le hq k]
  rw [show thetaCuspNativeScaledEvenJet k.val x/(32 : ℝ)^k.val-
      (if k.val = 6 then 100000000/(32 : ℝ)^(6 : ℕ) else 0)-
      (thetaCuspFirstAtomScaledEvenJet k.val x/(32 : ℝ)^k.val-
        (if k.val = 6 then 100000000/(32 : ℝ)^(6 : ℕ) else 0)) =
      (thetaCuspNativeScaledEvenJet k.val x-thetaCuspFirstAtomScaledEvenJet k.val x)/(32 : ℝ)^k.val by ring]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 32^k.val)]
  exact he

/-- Every complete-source contribution fits inside the exact reserved determinant floor. -/
theorem thetaCuspNativeEvenTailBalancedDet_lower_of_fifteen_le {x : ℝ}
    (hq : 15 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (1/25000 : ℝ) ≤ thetaCuspNativeEvenTailBalancedDet x := by
  have hu := inverseScale_bounds_of_fifteen_le hq
  have hb (k : Fin 7) := HTGeometry.firstAtomEvenTailBalanced_with_error_le_of_fifteen hu.1 hu.2 k
  have he (k : Fin 7) := abs_thetaCuspNativeEvenTailBalanced_sub_first_le_of_fifteen_le hq k
  have ha (k : Fin 7) : |thetaCuspNativeEvenTailBalanced k x| ≤ hankelFourTailEntryCeiling k := by
    have ht := abs_add_le
      (thetaCuspNativeEvenTailBalanced k x-
        HTGeometry.firstAtomEvenTailBalanced k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
      (HTGeometry.firstAtomEvenTailBalanced k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
    rw [sub_add_cancel] at ht
    linarith only [hb k, he k, ht]
  have hb' (k : Fin 7) : |HTGeometry.firstAtomEvenTailBalanced k ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹)| ≤
      hankelFourTailEntryCeiling k := by
    have hp : 0 ≤ (120 : ℝ)^k.val*(2/(10 : ℝ)^(17 : ℕ)) := by positivity
    linarith only [hb k, hp]
  have herr := hankelFourDet_error_le_scale120 (ε := 2/(10 : ℝ)^(17 : ℕ)) (by positivity) ha hb' he
  have hd := HTGeometry.firstAtomEvenTailBalancedDet_lower_of_fifteen hu.1 hu.2
  change |thetaCuspNativeEvenTailBalancedDet x-
    HTGeometry.firstAtomEvenTailBalancedDet ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹)| ≤ _ at herr
  have hl := (abs_le.mp herr).1
  linarith only [hl, hd]

/-- The actual complete twelfth-entry Schur coordinate exceeds one hundred million in Gaussian units. -/
theorem thetaCuspNativeEvenFourSchur_normalized_lower_of_fifteen_le {x : ℝ}
    (hq : 15 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    100000000 < thetaCuspNativeEvenFourSchur x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) := by
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hd : 0 < (32 : ℝ)^(12 : ℕ)*thetaCuspSourceTerm x 1^(8 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(12 : ℕ) := by positivity
  have hhead := (thetaCuspNativeEvenHead_posDef hx.le).det_pos
  have hr := thetaCuspNativeEvenTailBalancedDet_lower_of_fifteen_le hq
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
theorem thetaCuspCenterCompensationSource_six_normalized_lower_of_fifteen_le {x : ℝ}
    (hq : 15 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -(13/50 : ℝ)/15^(4 : ℕ) ≤ thetaCuspCenterCompensationSource x /
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
  have hp4 : (15 : ℝ)^(4 : ℕ) ≤ q^(4 : ℕ) := pow_le_pow_left₀ (by norm_num) hq 4
  have hi : (1 : ℝ)/q^(4 : ℕ) ≤ 1/(15 : ℝ)^(4 : ℕ) := one_div_le_one_div_of_le (by norm_num) hp4
  change -(13/50 : ℝ)/15^(4 : ℕ) ≤ thetaCuspCenterCompensationSource x/(f^(2 : ℕ)*q^(6 : ℕ))
  simp only [div_eq_mul_inv] at hi hnorm ⊢
  linarith only [hi, hnorm]

/-- Four fifths is an explicit physical endpoint for scale fifteen. -/
theorem fifteen_le_firstAtomScale_of_fourFifths_le {x : ℝ} (hx : 4/5 ≤ x) :
    15 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8/5) 8
  norm_num [Finset.sum_range_succ] at he
  have hm := Real.exp_le_exp.mpr (show (8/5 : ℝ) ≤ 2*x by linarith only [hx])
  have hp := mul_le_mul_of_nonneg_left (he.trans hm) Real.pi_pos.le
  norm_num [thetaCuspSingleAtomReflectionScale]
  nlinarith only [Real.pi_gt_d2, hp]

/-- A uniform positive margin survives the full correction throughout its rational coefficient band. -/
theorem thetaCuspNativeEvenFourCompensated_normalized_lower_of_fifteen_le {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000)
    (hq : 15 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    80000000 < (thetaCuspNativeEvenFourSchur x+C*thetaCuspCenterCompensationSource x) /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) := by
  have hs := thetaCuspNativeEvenFourSchur_normalized_lower_of_fifteen_le hq
  have hg := thetaCuspCenterCompensationSource_six_normalized_lower_of_fifteen_le hq
  have hm := mul_le_mul_of_nonneg_left hg hC0
  rw [add_div, mul_div_assoc]
  nlinarith only [hs, hm, hC1]

/-- Literal source positivity on the whole scale-fifteen ray, with no omitted tail contribution. -/
theorem thetaCuspNativeEvenFourCompensated_posDef_of_fifteen_le {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000)
    (hq : 15 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hd : 0 < thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ) := by positivity
  have hm := thetaCuspNativeEvenFourCompensated_normalized_lower_of_fifteen_le hC0 hC1 hq
  have hp : 0 < (thetaCuspNativeEvenFourSchur x+C*thetaCuspCenterCompensationSource x) /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) := by linarith
  rw [thetaCuspNativeEvenFourCompensated_posDef_iff hx.le]
  exact (div_pos_iff_of_pos_right hd).mp hp

/-- Four fifths is an explicit physical outer endpoint for the entire bounded coefficient family. -/
theorem thetaCuspNativeEvenFourCompensated_posDef_of_fourFifths_le {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000) (hx : 4/5 ≤ x) :
    (thetaCuspNativeEvenFourCompensated C x).PosDef :=
  thetaCuspNativeEvenFourCompensated_posDef_of_fifteen_le hC0 hC1
    (fifteen_le_firstAtomScale_of_fourFifths_le hx)

/-- The actual source-selected coefficient satisfies the explicit complete-source tail sign. -/
theorem thetaCuspNativeEvenFourCanonical_posDef_of_fourFifths_le :
    ∀ x : ℝ, 4/5 ≤ x →
      (thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient x).PosDef := by
  intro x hx
  exact thetaCuspNativeEvenFourCompensated_posDef_of_fourFifths_le
    thetaCuspNativeEvenCompensationCoefficient_pos.le
    thetaCuspNativeEvenCompensationCoefficient_bounds.2.le hx

/-- The literal weighted matrix is positive past eight fifths for every positive aperture. -/
theorem thetaCuspCenterCorrectedEvenFour_posDef_of_eightFifths_le {a C r : ℝ}
    (ha : 0 < a) (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000) (hr : 8/5 ≤ r) :
    (thetaCuspCenterCorrectedEvenFour a C r).PosDef := by
  apply thetaCuspCenterCorrectedEvenFour_posDef_of_source ha hC0 (by linarith)
  exact thetaCuspNativeEvenFourCompensated_posDef_of_fourFifths_le hC0 hC1 (by linarith)

/-- Closed canonical weighted tail positivity, uniformly over every positive aperture. -/
theorem thetaCuspCenterCorrectedEvenFourCanonical_posDef_of_eightFifths_le :
    ∀ a r : ℝ, 0 < a → 8/5 ≤ r →
      (thetaCuspCenterCorrectedEvenFour a thetaCuspNativeEvenCompensationCoefficient r).PosDef := by
  intro a r ha hr
  exact thetaCuspCenterCorrectedEvenFour_posDef_of_eightFifths_le ha
    thetaCuspNativeEvenCompensationCoefficient_pos.le
    thetaCuspNativeEvenCompensationCoefficient_bounds.2.le hr

/-- Every possible failure in the rational family lies below the fixed outer endpoint four fifths. -/
theorem exists_thetaCuspEvenCompensation_rationalFamily_outer_gap_below_fourFifths :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 4/5 ∧ ∀ C x : ℝ,
      1000000000000 ≤ C → C ≤ 3000000000000 → 0 ≤ x → (x < δ ∨ 4/5 ≤ x) →
        (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  obtain ⟨δ, hδ, hnear⟩ := exists_thetaCuspEvenCompensation_rationalFamily_posDef_near_zero
  refine ⟨min δ (4/5), lt_min hδ (by norm_num), min_le_right _ _, fun C x hCL hCU hx h => ?_⟩
  rcases h with h | h
  · exact hnear C x hCL hCU hx ((lt_min_iff.mp h).1)
  · exact thetaCuspNativeEvenFourCompensated_posDef_of_fourFifths_le (by linarith) hCU h

end
end RHTower
