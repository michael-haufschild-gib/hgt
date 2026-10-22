import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticDriftTensor
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity


def KineticDriftBound (P : KineticPolynomial) (d : ℕ) : Prop :=
  ∀ h : ℂ, ∀ j b : ℕ, d<b → kineticDriftCell h P j b=0

theorem kineticDriftBound_add {P Q : KineticPolynomial} {d : ℕ}
    (hP : KineticDriftBound P d) (hQ : KineticDriftBound Q d) :
    KineticDriftBound (P+Q) d := by
  intro h j b hb
  rw [kineticDriftCell_add,hP h j b hb,hQ h j b hb,add_zero]

theorem kineticDriftBound_sub {P Q : KineticPolynomial} {d : ℕ}
    (hP : KineticDriftBound P d) (hQ : KineticDriftBound Q d) :
    KineticDriftBound (P-Q) d := by
  intro h j b hb
  rw [kineticDriftCell_sub,hP h j b hb,hQ h j b hb,sub_self]

theorem kineticDriftBound_neg {P : KineticPolynomial} {d : ℕ}
    (hP : KineticDriftBound P d) : KineticDriftBound (-P) d := by
  intro h j b hb
  rw [kineticDriftCell_neg,hP h j b hb,neg_zero]

theorem kineticDriftBound_nat_mul (n : ℕ) {P : KineticPolynomial} {d : ℕ}
    (hP : KineticDriftBound P d) : KineticDriftBound ((n:KineticPolynomial)*P) d := by
  intro h j b hb
  rw [kineticDriftCell_nat_mul,hP h j b hb,mul_zero]

theorem kineticDriftBound_mul {P Q : KineticPolynomial} {d e : ℕ}
    (hP : KineticDriftBound P d) (hQ : KineticDriftBound Q e) :
    KineticDriftBound (P*Q) (d+e) := by
  intro h j b hb
  rw [kineticDriftCell_mul]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : d<c
  · rw [hP h a c hc,zero_mul]
  · have he : e<b-c := by omega
    rw [hQ h (j-a) (b-c) he,mul_zero]

theorem kineticMoment2_drift_bound : KineticDriftBound kineticMoment2 1 := by
  intro h j b hb
  have hz0 : (driftReader h clearMoment2KineticCoeff0).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment2KineticCoeff0_drift_degree h).trans_lt hb)
  have hz1 : (driftReader h clearMoment2KineticCoeff1).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment2KineticCoeff1_drift_degree h).trans_lt hb)
  have hz2 : (driftReader h clearMoment2KineticCoeff2).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment2KineticCoeff2_drift_degree h).trans_lt hb)
  by_cases hj : j≤2
  · interval_cases j
    · norm_num only [kineticDriftCell,kineticMoment2_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz0
    · norm_num only [kineticDriftCell,kineticMoment2_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz1
    · norm_num only [kineticDriftCell,kineticMoment2_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz2
  · have hp : kineticMoment2.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticMoment2_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero]


theorem kineticMoment4_drift_bound : KineticDriftBound kineticMoment4 2 := by
  intro h j b hb
  have hz0 : (driftReader h clearMoment4KineticCoeff0).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment4KineticCoeff0_drift_degree h).trans_lt hb)
  have hz1 : (driftReader h clearMoment4KineticCoeff1).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment4KineticCoeff1_drift_degree h).trans_lt hb)
  have hz2 : (driftReader h clearMoment4KineticCoeff2).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment4KineticCoeff2_drift_degree h).trans_lt hb)
  have hz3 : (driftReader h clearMoment4KineticCoeff3).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment4KineticCoeff3_drift_degree h).trans_lt hb)
  have hz4 : (driftReader h clearMoment4KineticCoeff4).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment4KineticCoeff4_drift_degree h).trans_lt hb)
  by_cases hj : j≤4
  · interval_cases j
    · norm_num only [kineticDriftCell,kineticMoment4_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz0
    · norm_num only [kineticDriftCell,kineticMoment4_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz1
    · norm_num only [kineticDriftCell,kineticMoment4_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz2
    · norm_num only [kineticDriftCell,kineticMoment4_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz3
    · norm_num only [kineticDriftCell,kineticMoment4_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz4
  · have hp : kineticMoment4.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticMoment4_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero]


theorem kineticMoment6_drift_bound : KineticDriftBound kineticMoment6 3 := by
  intro h j b hb
  have hz0 : (driftReader h clearMoment6KineticCoeff0).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment6KineticCoeff0_drift_degree h).trans_lt hb)
  have hz1 : (driftReader h clearMoment6KineticCoeff1).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment6KineticCoeff1_drift_degree h).trans_lt hb)
  have hz2 : (driftReader h clearMoment6KineticCoeff2).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment6KineticCoeff2_drift_degree h).trans_lt hb)
  have hz3 : (driftReader h clearMoment6KineticCoeff3).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment6KineticCoeff3_drift_degree h).trans_lt hb)
  have hz4 : (driftReader h clearMoment6KineticCoeff4).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment6KineticCoeff4_drift_degree h).trans_lt hb)
  have hz5 : (driftReader h clearMoment6KineticCoeff5).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment6KineticCoeff5_drift_degree h).trans_lt hb)
  have hz6 : (driftReader h clearMoment6KineticCoeff6).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment6KineticCoeff6_drift_degree h).trans_lt hb)
  by_cases hj : j≤6
  · interval_cases j
    · norm_num only [kineticDriftCell,kineticMoment6_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz0
    · norm_num only [kineticDriftCell,kineticMoment6_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz1
    · norm_num only [kineticDriftCell,kineticMoment6_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz2
    · norm_num only [kineticDriftCell,kineticMoment6_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz3
    · norm_num only [kineticDriftCell,kineticMoment6_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz4
    · norm_num only [kineticDriftCell,kineticMoment6_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz5
    · norm_num only [kineticDriftCell,kineticMoment6_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz6
  · have hp : kineticMoment6.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticMoment6_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero]


theorem kineticMoment8_drift_bound : KineticDriftBound kineticMoment8 4 := by
  intro h j b hb
  have hz0 : (driftReader h clearMoment8KineticCoeff0).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment8KineticCoeff0_drift_degree h).trans_lt hb)
  have hz1 : (driftReader h clearMoment8KineticCoeff1).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment8KineticCoeff1_drift_degree h).trans_lt hb)
  have hz2 : (driftReader h clearMoment8KineticCoeff2).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment8KineticCoeff2_drift_degree h).trans_lt hb)
  have hz3 : (driftReader h clearMoment8KineticCoeff3).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment8KineticCoeff3_drift_degree h).trans_lt hb)
  have hz4 : (driftReader h clearMoment8KineticCoeff4).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment8KineticCoeff4_drift_degree h).trans_lt hb)
  have hz5 : (driftReader h clearMoment8KineticCoeff5).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment8KineticCoeff5_drift_degree h).trans_lt hb)
  have hz6 : (driftReader h clearMoment8KineticCoeff6).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment8KineticCoeff6_drift_degree h).trans_lt hb)
  have hz7 : (driftReader h clearMoment8KineticCoeff7).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment8KineticCoeff7_drift_degree h).trans_lt hb)
  have hz8 : (driftReader h clearMoment8KineticCoeff8).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment8KineticCoeff8_drift_degree h).trans_lt hb)
  by_cases hj : j≤8
  · interval_cases j
    · norm_num only [kineticDriftCell,kineticMoment8_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz0
    · norm_num only [kineticDriftCell,kineticMoment8_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz1
    · norm_num only [kineticDriftCell,kineticMoment8_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz2
    · norm_num only [kineticDriftCell,kineticMoment8_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz3
    · norm_num only [kineticDriftCell,kineticMoment8_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz4
    · norm_num only [kineticDriftCell,kineticMoment8_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz5
    · norm_num only [kineticDriftCell,kineticMoment8_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz6
    · norm_num only [kineticDriftCell,kineticMoment8_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz7
    · norm_num only [kineticDriftCell,kineticMoment8_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz8
  · have hp : kineticMoment8.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticMoment8_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero]


theorem kineticMoment10_drift_bound : KineticDriftBound kineticMoment10 5 := by
  intro h j b hb
  have hz0 : (driftReader h clearMoment10KineticCoeff0).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment10KineticCoeff0_drift_degree h).trans_lt hb)
  have hz1 : (driftReader h clearMoment10KineticCoeff1).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment10KineticCoeff1_drift_degree h).trans_lt hb)
  have hz2 : (driftReader h clearMoment10KineticCoeff2).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment10KineticCoeff2_drift_degree h).trans_lt hb)
  have hz3 : (driftReader h clearMoment10KineticCoeff3).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment10KineticCoeff3_drift_degree h).trans_lt hb)
  have hz4 : (driftReader h clearMoment10KineticCoeff4).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment10KineticCoeff4_drift_degree h).trans_lt hb)
  have hz5 : (driftReader h clearMoment10KineticCoeff5).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment10KineticCoeff5_drift_degree h).trans_lt hb)
  have hz6 : (driftReader h clearMoment10KineticCoeff6).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment10KineticCoeff6_drift_degree h).trans_lt hb)
  have hz7 : (driftReader h clearMoment10KineticCoeff7).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment10KineticCoeff7_drift_degree h).trans_lt hb)
  have hz8 : (driftReader h clearMoment10KineticCoeff8).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment10KineticCoeff8_drift_degree h).trans_lt hb)
  have hz9 : (driftReader h clearMoment10KineticCoeff9).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment10KineticCoeff9_drift_degree h).trans_lt hb)
  have hz10 : (driftReader h clearMoment10KineticCoeff10).coeff b=0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((clearMoment10KineticCoeff10_drift_degree h).trans_lt hb)
  by_cases hj : j≤10
  · interval_cases j
    · norm_num only [kineticDriftCell,kineticMoment10_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz0
    · norm_num only [kineticDriftCell,kineticMoment10_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz1
    · norm_num only [kineticDriftCell,kineticMoment10_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz2
    · norm_num only [kineticDriftCell,kineticMoment10_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz3
    · norm_num only [kineticDriftCell,kineticMoment10_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz4
    · norm_num only [kineticDriftCell,kineticMoment10_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz5
    · norm_num only [kineticDriftCell,kineticMoment10_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz6
    · norm_num only [kineticDriftCell,kineticMoment10_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz7
    · norm_num only [kineticDriftCell,kineticMoment10_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz8
    · norm_num only [kineticDriftCell,kineticMoment10_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz9
    · norm_num only [kineticDriftCell,kineticMoment10_coeff]
      simpa only [ite_true,ite_false,zero_add,add_zero] using hz10
  · have hp : kineticMoment10.coeff j=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (kineticMoment10_degree.trans_lt (by omega))
    simp only [kineticDriftCell,hp,map_zero,Polynomial.coeff_zero]



theorem kineticDegree_nat_mul (n : ℕ) {P : KineticPolynomial} {d : ℕ}
    (hP : P.natDegree≤d) : ((n:KineticPolynomial)*P).natDegree≤d := by
  have hn : (n:KineticPolynomial).natDegree≤0 := (Polynomial.natDegree_natCast n).le
  simpa only [zero_add] using Polynomial.natDegree_mul_le_of_le hn hP

theorem kineticDegree_sub {P Q : KineticPolynomial} {d : ℕ}
    (hP : P.natDegree≤d) (hQ : Q.natDegree≤d) : (P-Q).natDegree≤d := by
  simpa only [max_self] using Polynomial.natDegree_sub_le_of_le hP hQ

theorem kineticCof2_tensor_form : kineticCof2=-(kineticMoment6*kineticMoment10)+kineticMoment8*kineticMoment8 := by
  unfold kineticCof2 cof2_75
  ring


theorem kineticCof2_drift_bound : KineticDriftBound kineticCof2 8 := by
  have ha := kineticDriftBound_mul kineticMoment6_drift_bound kineticMoment10_drift_bound
  have hb := kineticDriftBound_mul kineticMoment8_drift_bound kineticMoment8_drift_bound
  rw [kineticCof2_tensor_form]
  exact kineticDriftBound_add (kineticDriftBound_neg ha) hb

theorem kineticCof2_drift_degree (h : ℂ) (j : ℕ) :
    (driftReader h (kineticCof2.coeff j)).natDegree≤8 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro b hb
  exact kineticCof2_drift_bound h j b hb

theorem kineticCof2_degree : kineticCof2.natDegree≤16 := by
  have ha : (kineticMoment6*kineticMoment10).natDegree≤16 :=
    Polynomial.natDegree_mul_le_of_le kineticMoment6_degree kineticMoment10_degree
  have hb : (kineticMoment8*kineticMoment8).natDegree≤16 :=
    Polynomial.natDegree_mul_le_of_le kineticMoment8_degree kineticMoment8_degree
  rw [kineticCof2_tensor_form]
  exact Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_neg_le_of_le ha) hb


theorem kineticCof4_tensor_form : kineticCof4=((2:ℕ):KineticPolynomial)*(kineticMoment4*kineticMoment10)-((2:ℕ):KineticPolynomial)*(kineticMoment6*kineticMoment8) := by
  unfold kineticCof4 cof4_75
  ring


theorem kineticCof4_drift_bound : KineticDriftBound kineticCof4 7 := by
  have ha := kineticDriftBound_mul kineticMoment4_drift_bound kineticMoment10_drift_bound
  have hb := kineticDriftBound_mul kineticMoment6_drift_bound kineticMoment8_drift_bound
  rw [kineticCof4_tensor_form]
  exact kineticDriftBound_sub (kineticDriftBound_nat_mul 2 ha) (kineticDriftBound_nat_mul 2 hb)

theorem kineticCof4_drift_degree (h : ℂ) (j : ℕ) :
    (driftReader h (kineticCof4.coeff j)).natDegree≤7 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro b hb
  exact kineticCof4_drift_bound h j b hb

theorem kineticCof4_degree : kineticCof4.natDegree≤14 := by
  have ha : (kineticMoment4*kineticMoment10).natDegree≤14 :=
    Polynomial.natDegree_mul_le_of_le kineticMoment4_degree kineticMoment10_degree
  have hb : (kineticMoment6*kineticMoment8).natDegree≤14 :=
    Polynomial.natDegree_mul_le_of_le kineticMoment6_degree kineticMoment8_degree
  rw [kineticCof4_tensor_form]
  exact kineticDegree_sub (kineticDegree_nat_mul 2 ha) (kineticDegree_nat_mul 2 hb)


theorem kineticCof6_tensor_form : kineticCof6=-(kineticMoment2*kineticMoment10)-((2:ℕ):KineticPolynomial)*(kineticMoment4*kineticMoment8)+((3:ℕ):KineticPolynomial)*(kineticMoment6*kineticMoment6) := by
  unfold kineticCof6 cof6_75
  ring


theorem kineticCof6_drift_bound : KineticDriftBound kineticCof6 6 := by
  have ha := kineticDriftBound_mul kineticMoment2_drift_bound kineticMoment10_drift_bound
  have hb := kineticDriftBound_mul kineticMoment4_drift_bound kineticMoment8_drift_bound
  have hc := kineticDriftBound_mul kineticMoment6_drift_bound kineticMoment6_drift_bound
  rw [kineticCof6_tensor_form]
  exact kineticDriftBound_add (kineticDriftBound_sub (kineticDriftBound_neg ha) (kineticDriftBound_nat_mul 2 hb)) (kineticDriftBound_nat_mul 3 hc)

theorem kineticCof6_drift_degree (h : ℂ) (j : ℕ) :
    (driftReader h (kineticCof6.coeff j)).natDegree≤6 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro b hb
  exact kineticCof6_drift_bound h j b hb

theorem kineticCof6_degree : kineticCof6.natDegree≤12 := by
  have ha : (kineticMoment2*kineticMoment10).natDegree≤12 :=
    Polynomial.natDegree_mul_le_of_le kineticMoment2_degree kineticMoment10_degree
  have hb : (kineticMoment4*kineticMoment8).natDegree≤12 :=
    Polynomial.natDegree_mul_le_of_le kineticMoment4_degree kineticMoment8_degree
  have hc : (kineticMoment6*kineticMoment6).natDegree≤12 :=
    Polynomial.natDegree_mul_le_of_le kineticMoment6_degree kineticMoment6_degree
  rw [kineticCof6_tensor_form]
  exact Polynomial.natDegree_add_le_of_degree_le (kineticDegree_sub (Polynomial.natDegree_neg_le_of_le ha) (kineticDegree_nat_mul 2 hb)) (kineticDegree_nat_mul 3 hc)


theorem kineticCof8_tensor_form : kineticCof8=((2:ℕ):KineticPolynomial)*(kineticMoment2*kineticMoment8)-((2:ℕ):KineticPolynomial)*(kineticMoment4*kineticMoment6) := by
  unfold kineticCof8 cof8_75
  ring


theorem kineticCof8_drift_bound : KineticDriftBound kineticCof8 5 := by
  have ha := kineticDriftBound_mul kineticMoment2_drift_bound kineticMoment8_drift_bound
  have hb := kineticDriftBound_mul kineticMoment4_drift_bound kineticMoment6_drift_bound
  rw [kineticCof8_tensor_form]
  exact kineticDriftBound_sub (kineticDriftBound_nat_mul 2 ha) (kineticDriftBound_nat_mul 2 hb)

theorem kineticCof8_drift_degree (h : ℂ) (j : ℕ) :
    (driftReader h (kineticCof8.coeff j)).natDegree≤5 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro b hb
  exact kineticCof8_drift_bound h j b hb

theorem kineticCof8_degree : kineticCof8.natDegree≤10 := by
  have ha : (kineticMoment2*kineticMoment8).natDegree≤10 :=
    Polynomial.natDegree_mul_le_of_le kineticMoment2_degree kineticMoment8_degree
  have hb : (kineticMoment4*kineticMoment6).natDegree≤10 :=
    Polynomial.natDegree_mul_le_of_le kineticMoment4_degree kineticMoment6_degree
  rw [kineticCof8_tensor_form]
  exact kineticDegree_sub (kineticDegree_nat_mul 2 ha) (kineticDegree_nat_mul 2 hb)


theorem kineticCof10_tensor_form : kineticCof10=-(kineticMoment2*kineticMoment6)+kineticMoment4*kineticMoment4 := by
  unfold kineticCof10 cof10_75
  ring


theorem kineticCof10_drift_bound : KineticDriftBound kineticCof10 4 := by
  have ha := kineticDriftBound_mul kineticMoment2_drift_bound kineticMoment6_drift_bound
  have hb := kineticDriftBound_mul kineticMoment4_drift_bound kineticMoment4_drift_bound
  rw [kineticCof10_tensor_form]
  exact kineticDriftBound_add (kineticDriftBound_neg ha) hb

theorem kineticCof10_drift_degree (h : ℂ) (j : ℕ) :
    (driftReader h (kineticCof10.coeff j)).natDegree≤4 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro b hb
  exact kineticCof10_drift_bound h j b hb

theorem kineticCof10_degree : kineticCof10.natDegree≤8 := by
  have ha : (kineticMoment2*kineticMoment6).natDegree≤8 :=
    Polynomial.natDegree_mul_le_of_le kineticMoment2_degree kineticMoment6_degree
  have hb : (kineticMoment4*kineticMoment4).natDegree≤8 :=
    Polynomial.natDegree_mul_le_of_le kineticMoment4_degree kineticMoment4_degree
  rw [kineticCof10_tensor_form]
  exact Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_neg_le_of_le ha) hb

end
end HTGeometry.ThetaRatioKineticContraction
