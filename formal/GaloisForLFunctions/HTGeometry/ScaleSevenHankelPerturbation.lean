import GaloisForLFunctions.HTGeometry.HankelThreePerturbation

/-!
# Entrywise cubic perturbation with the exact leading cofactor retained

The fifth-coordinate error is multiplied by the actual first leading minor.
Each other telescoping coefficient retains the cancellation between its two
nonnegative contributions.
-/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000

private theorem abs_sub_le_box {u v M : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huM : u ≤ M) (hvM : v ≤ M) : |u-v| ≤ M := by
  apply abs_le.mpr
  constructor <;> linarith

/-- The explicit scale-seven entry errors change the odd determinant by at most ten billion. -/
theorem signedEvenHankelThreeDet_scaleSeven_error
    {a b c d e A B C D E : ℝ}
    (hA : 8 ≤ A ∧ A ≤ 9) (hB : 180 ≤ B ∧ B ≤ 210)
    (hC : 7000 ≤ C ∧ C ≤ 8500) (hD : 300000 ≤ D ∧ D ≤ 500000)
    (hE : 20000000 ≤ E ∧ E ≤ 40000000)
    (hhead : |A*C-B^(2 : ℕ)| ≤ 27000)
    (ea : |a-A| ≤ 1/75000) (eb : |b-B| ≤ 1/250) (ec : |c-C| ≤ 5/4)
    (ed : |d-D| ≤ 450) (ee : |e-E| ≤ 175000) :
    |HilbertMetric.signedEvenHankelThreeDet a b c d e-
      HilbertMetric.signedEvenHankelThreeDet A B C D E| ≤ 10000000000 := by
  have ea' := abs_le.mp ea
  have eb' := abs_le.mp eb
  have ec' := abs_le.mp ec
  have ed' := abs_le.mp ed
  have ee' := abs_le.mp ee
  have hA0 : 0 ≤ A := by linarith [hA.1]
  have hB0 : 0 ≤ B := by linarith [hB.1]
  have hC0 : 0 ≤ C := by linarith [hC.1]
  have hD0 : 0 ≤ D := by linarith [hD.1]
  have ha0 : 0 ≤ a := by linarith [hA.1]
  have hb0 : 0 ≤ b := by linarith [hB.1]
  have hc0 : 0 ≤ c := by linarith [hC.1]
  have hd0 : 0 ≤ d := by linarith [hD.1]
  have he0 : 0 ≤ e := by linarith [hE.1]
  have hau : a ≤ 9001/1000 := by linarith [hA.2]
  have hbu : b ≤ 21001/100 := by linarith [hB.2]
  have hcu : c ≤ 8502 := by linarith [hC.2]
  have hdu : d ≤ 500450 := by linarith [hD.2]
  have heu : e ≤ 40175000 := by linarith [hE.2]
  have hce := mul_le_mul hC.2 heu he0 (by norm_num : (0 : ℝ) ≤ 8500)
  have hDD := pow_le_pow_left₀ hD0 hD.2 2
  have ca : |C*e-D^(2 : ℕ)| ≤ 350000000000 := by
    apply abs_sub_le_box (mul_nonneg hC0 he0) (sq_nonneg D)
    · nlinarith only [hce]
    · nlinarith only [hDD]
  have hsumB : b+B ≤ 42001/100 := by linarith [hB.2]
  have hbe := mul_le_mul hsumB heu he0 (by norm_num : (0 : ℝ) ≤ 42001/100)
  have hCD := mul_le_mul hC.2 hD.2 hD0 (by norm_num : (0 : ℝ) ≤ 8500)
  have cb : |-(b+B)*e+2*C*D| ≤ 17000000000 := by
    rw [show -(b+B)*e+2*C*D = 2*C*D-(b+B)*e by ring]
    apply abs_sub_le_box (by positivity) (by positivity)
    · nlinarith only [hCD]
    · nlinarith only [hbe]
  have hae := mul_le_mul hau heu he0 (by norm_num : (0 : ℝ) ≤ 9001/1000)
  have hbD := mul_le_mul hbu hD.2 hD0 (by norm_num : (0 : ℝ) ≤ 21001/100)
  have hcc := pow_le_pow_left₀ hc0 hcu 2
  have hcC := mul_le_mul hcu hC.2 hC0 (by norm_num : (0 : ℝ) ≤ 8502)
  have hCC := pow_le_pow_left₀ hC0 hC.2 2
  have cc : |a*e+2*b*D-(c^(2 : ℕ)+c*C+C^(2 : ℕ))| ≤ 600000000 := by
    apply abs_sub_le_box (by positivity) (by positivity)
    · nlinarith only [hae, hbD]
    · nlinarith only [hcc, hcC, hCC]
  have hsumD : d+D ≤ 1000450 := by linarith [hD.2]
  have had := mul_le_mul hau hsumD (add_nonneg hd0 hD0)
    (by norm_num : (0 : ℝ) ≤ 9001/1000)
  have hbc := mul_le_mul hbu hcu hc0 (by norm_num : (0 : ℝ) ≤ 21001/100)
  have cd : |-a*(d+D)+2*b*c| ≤ 9010000 := by
    rw [show -a*(d+D)+2*b*c = 2*b*c-a*(d+D) by ring]
    apply abs_sub_le_box (by positivity) (by positivity)
    · nlinarith only [hbc]
    · nlinarith only [had]
  have t0 : |(e-E)*(A*C-B^(2 : ℕ))| ≤ 175000*27000 := by
    rw [abs_mul]
    exact mul_le_mul ee hhead (abs_nonneg _) (by norm_num)
  have t1 : |(a-A)*(C*e-D^(2 : ℕ))| ≤ (1/75000)*350000000000 := by
    rw [abs_mul]
    exact mul_le_mul ea ca (abs_nonneg _) (by norm_num)
  have t2 : |(b-B)*(-(b+B)*e+2*C*D)| ≤ (1/250)*17000000000 := by
    rw [abs_mul]
    exact mul_le_mul eb cb (abs_nonneg _) (by norm_num)
  have t3 : |(c-C)*(a*e+2*b*D-(c^(2 : ℕ)+c*C+C^(2 : ℕ)))| ≤ (5/4)*600000000 := by
    rw [abs_mul]
    exact mul_le_mul ec cc (abs_nonneg _) (by norm_num)
  have t4 : |(d-D)*(-a*(d+D)+2*b*c)| ≤ 450*9010000 := by
    rw [abs_mul]
    exact mul_le_mul ed cd (abs_nonneg _) (by norm_num)
  have heq : HilbertMetric.signedEvenHankelThreeDet a b c d e-
      HilbertMetric.signedEvenHankelThreeDet A B C D E =
      (e-E)*(A*C-B^(2 : ℕ))+(a-A)*(C*e-D^(2 : ℕ))+(b-B)*(-(b+B)*e+2*C*D)+
      (c-C)*(a*e+2*b*D-(c^(2 : ℕ)+c*C+C^(2 : ℕ)))+(d-D)*(-a*(d+D)+2*b*c) := by
    unfold HilbertMetric.signedEvenHankelThreeDet
    ring
  have t0' := abs_le.mp t0
  have t1' := abs_le.mp t1
  have t2' := abs_le.mp t2
  have t3' := abs_le.mp t3
  have t4' := abs_le.mp t4
  rw [heq]
  apply abs_le.mpr
  constructor <;> nlinarith only [t0'.1, t0'.2, t1'.1, t1'.2, t2'.1, t2'.2,
    t3'.1, t3'.2, t4'.1, t4'.2]

/-- The same small entry errors preserve a leading-minor ceiling of twenty-eight thousand. -/
theorem signedOddHead_scaleSeven_upper {a b c A B C : ℝ}
    (hA : 8 ≤ A ∧ A ≤ 9) (hB : 180 ≤ B ∧ B ≤ 210)
    (hC : 7000 ≤ C ∧ C ≤ 8500) (hhead : A*C-B^(2 : ℕ) ≤ 27000)
    (ea : |a-A| ≤ 1/75000) (eb : |b-B| ≤ 1/250) (ec : |c-C| ≤ 5/4) :
    a*c-b^(2 : ℕ) ≤ 28000 := by
  have ea' := abs_le.mp ea
  have eb' := abs_le.mp eb
  have ec' := abs_le.mp ec
  have hA0 : 0 ≤ A := by linarith [hA.1]
  have hc0 : 0 ≤ c := by linarith [hC.1]
  have hcu : c ≤ 8502 := by linarith [hC.2]
  have hb0 : 0 ≤ b := by linarith [hB.1]
  have hB0 : 0 ≤ B := by linarith [hB.1]
  have hbB0 : 0 ≤ b+B := by positivity
  have hbBu : b+B ≤ 421 := by linarith [hB.2]
  have h1 := mul_le_mul_of_nonneg_right ea'.2 hc0
  have h2 := mul_le_mul_of_nonneg_left ec'.2 hA0
  have h3 := mul_le_mul_of_nonneg_right eb'.1 hbB0
  nlinarith only [h1, h2, h3, hcu, hA.2, hbBu, hhead]

end
end HTGeometry
