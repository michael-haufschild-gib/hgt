import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectBinaryGrowthKernel
/-!
# Dominant binary curvature-defect growth inequality

Exact polynomial-to-moment transport gives a strictly positive cooling
expression for the literal second theta component throughout the source
half-line. All growth-coefficient derivatives are verified. Complete-source
cumulant positivity still requires the higher-component and higher-grade
absorption argument. The full convolution pair adds exactly the nonnegative
term `2 M₁ T²` to the positive-composition cooling expression.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section
def reducedGrowthCoefficient (q : ℝ) : ℕ → ℝ
  | 2 => 540
  | 3 => 180*(q^2-6*(q+3/2))
  | 4 => 150*((q+3/2)*(3*(q+3/2)-2*q^2))
  | 5 => 45*((q+3/2)^2*(3*q^2-(q+3/2)))
  | 6 => -21*(q^2*(q+3/2)^3)
  | 7 => q^2*(q+3/2)^4
  | _ => 0

def reducedGrowthCoefficientJet (q : ℝ) : ℕ → ℝ
  | 2 => 0
  | 3 => 180*(2*q-6)
  | 4 => 150*((3*(q+3/2)-2*q^2)+(q+3/2)*(3-4*q))
  | 5 => 45*(2*(q+3/2)*(3*q^2-(q+3/2))+(q+3/2)^2*(6*q-1))
  | 6 => -21*(2*q*(q+3/2)^3+q^2*(3*(q+3/2)^2))
  | 7 => 2*q*(q+3/2)^4+q^2*(4*(q+3/2)^3)
  | _ => 0

theorem growthCoefficient_factor (q : ℝ) (j : ℕ) (hj : j ≤ 7) :
    growthCoefficient q j=(q+3)*reducedGrowthCoefficient q j := by
  interval_cases j <;>
    norm_num [growthCoefficient,coolingCoefficient,coolingCoefficientJet,reducedGrowthCoefficient] <;> ring

theorem growthCoefficientJet_factor (q : ℝ) (j : ℕ) (hj : j ≤ 7) :
    growthCoefficientJet q j=(q+3)*reducedGrowthCoefficientJet q j+reducedGrowthCoefficient q j := by
  interval_cases j <;>
    norm_num [growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,coolingCoefficientJetTwo,
      reducedGrowthCoefficient,reducedGrowthCoefficientJet] <;> ring

theorem hasDerivAt_reducedGrowthCoefficient (q : ℝ) (j : ℕ) (hj : j ≤ 7) :
    HasDerivAt (fun r => reducedGrowthCoefficient r j) (reducedGrowthCoefficientJet q j) q := by
  have h := hasDerivAt_id q
  have ha := h.add_const (3/2:ℝ)
  have hq := h.pow 2
  interval_cases j
  · simpa [reducedGrowthCoefficient,reducedGrowthCoefficientJet] using hasDerivAt_const q (0:ℝ)
  · simpa [reducedGrowthCoefficient,reducedGrowthCoefficientJet] using hasDerivAt_const q (0:ℝ)
  · simpa [reducedGrowthCoefficient,reducedGrowthCoefficientJet] using hasDerivAt_const q (540:ℝ)
  · exact ((hq.sub (ha.const_mul 6)).const_mul 180).congr_deriv (by
      norm_num [reducedGrowthCoefficientJet])
  · exact ((ha.mul ((ha.const_mul 3).sub (hq.const_mul 2))).const_mul 150).congr_deriv (by
      norm_num [reducedGrowthCoefficientJet]; ring_nf; simp)
  · exact (((ha.pow 2).mul ((hq.const_mul 3).sub ha)).const_mul 45).congr_deriv (by
      norm_num [reducedGrowthCoefficientJet]; ring_nf; simp)
  · exact ((hq.mul (ha.pow 3)).const_mul (-21)).congr_deriv (by
      norm_num [reducedGrowthCoefficientJet])
  · exact (hq.mul (ha.pow 4)).congr_deriv (by
      norm_num [reducedGrowthCoefficientJet])

theorem hasDerivAt_growthCoefficient (q : ℝ) (j : ℕ) (hj : j ≤ 7) :
    HasDerivAt (fun r => growthCoefficient r j) (growthCoefficientJet q j) q := by
  convert! ((hasDerivAt_id q).add_const (3:ℝ)).mul
    (hasDerivAt_reducedGrowthCoefficient q j hj) using 1
  · funext r
    exact growthCoefficient_factor r j hj
  · simpa only [one_mul,add_comm,id_eq] using growthCoefficientJet_factor q j hj


theorem bareMoment_eq_polynomial {q : ℝ} (hq : q ≠ 0) (d : ℝ) (j : ℕ) :
    bareMoment q d j=polynomialMoment q d j/q^(j+1) := by
  apply (eq_div_iff (pow_ne_zero _ hq)).mpr
  unfold bareMoment polynomialMoment
  rw [add_mul]
  congr 1
  rw [mul_assoc,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
  have he : j+1=(j-i)+(i+1) := by omega
  rw [he,pow_add]
  field_simp [hq]
  simp only [pow_add,pow_succ]
  ring

theorem growthFunctional_bare_polynomial {q : ℝ} (hq : q ≠ 0) (d : ℝ) :
    growthFunctional q (bareMoment q d)=growthNumerator q d/q^8 := by
  unfold growthFunctional growthNumerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num only [Nat.reduceAdd,Nat.reduceSub]
  simp only [bareMoment_eq_polynomial hq]
  field_simp [hq]
  ring

theorem growthSlope_bare_polynomial {q : ℝ} (hq : q ≠ 0) (d : ℝ) :
    growthSlope q (bareMoment q d)=slopeNumerator q d/q^9 := by
  unfold growthSlope slopeNumerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num only [Nat.reduceAdd,Nat.reduceSub]
  simp only [bareMoment_eq_polynomial hq]
  field_simp [hq]
  ring

theorem binaryGrowth_bare_polynomial {q : ℝ} (hq : q ≠ 0) (d e : ℝ) :
    binaryGrowth q (bareMoment q d) (bareMoment q e)=binaryGrowthNumerator q d e/q^9 := by
  unfold binaryGrowth growthFunctional binaryGrowthNumerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [binaryMoment]
  simp only [bareMoment_eq_polynomial hq]
  field_simp [hq]
  ring

theorem binaryGrowthSlope_bare_polynomial {q : ℝ} (hq : q ≠ 0) (d e : ℝ) :
    binaryGrowthSlope q (bareMoment q d) (bareMoment q e)=binarySlopeNumerator q d e/q^10 := by
  unfold binaryGrowthSlope binarySlopeNumerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [binaryMoment]
  simp only [bareMoment_eq_polynomial hq]
  field_simp [hq]
  ring

def selfGrowthCooling (q : ℝ) (m : ℕ → ℝ) : ℝ :=
  binaryGrowth q m m*growthSlope q m-binaryGrowthSlope q m m*growthFunctional q m

theorem selfGrowthCooling_bare_eq {q : ℝ} (hq : q ≠ 0) :
    selfGrowthCooling q (bareMoment q 3)=anchorCoolingNumerator q 3 3/q^18 := by
  unfold selfGrowthCooling
  rw [binaryGrowth_bare_polynomial hq,growthSlope_bare_polynomial hq,
    binaryGrowthSlope_bare_polynomial hq,growthFunctional_bare_polynomial hq]
  unfold anchorCoolingNumerator
  field_simp [hq]

theorem selfGrowthCooling_bare_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < selfGrowthCooling q (bareMoment q 3) := by
  have hq0 : 0 < q := by linarith
  rw [selfGrowthCooling_bare_eq hq0.ne']
  exact div_pos (anchorCoolingNumerator_self_pos hq) (pow_pos hq0 _)

theorem growthSlope_smul (q a : ℝ) (m : ℕ → ℝ) :
    growthSlope q (fun j => a*m j)=a*growthSlope q m := by
  unfold growthSlope
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem binaryGrowth_smul (q a b : ℝ) (m n : ℕ → ℝ) :
    binaryGrowth q (fun j => a*m j) (fun j => b*n j)=a*b*binaryGrowth q m n := by
  unfold binaryGrowth growthFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj5 : j ≤ 5 := by have := Finset.mem_range.mp hj; omega
  interval_cases j <;> norm_num [binaryMoment] <;> ring

theorem binaryGrowthSlope_smul (q a b : ℝ) (m n : ℕ → ℝ) :
    binaryGrowthSlope q (fun j => a*m j) (fun j => b*n j)=a*b*binaryGrowthSlope q m n := by
  unfold binaryGrowthSlope
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj5 : j ≤ 5 := by have := Finset.mem_range.mp hj; omega
  interval_cases j <;> norm_num [binaryMoment] <;> ring

theorem selfGrowthCooling_smul (q a : ℝ) (m : ℕ → ℝ) :
    selfGrowthCooling q (fun j => a*m j)=a^3*selfGrowthCooling q m := by
  unfold selfGrowthCooling
  rw [binaryGrowth_smul,growthSlope_smul,binaryGrowthSlope_smul,growthFunctional_smul]
  ring

theorem atom_selfGrowthCooling_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < selfGrowthCooling q (atomMoment 2 q) := by
  have hq0 : 0 < q := by linarith
  let a : ℝ := Real.exp (-(3/2)*3)*Real.exp (-q*3)*(3+1)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hgap : thetaCuspLikelihoodGap 2=3 := by norm_num [thetaCuspLikelihoodGap]
  have heq : atomMoment 2 q=fun j => a*bareMoment q 3 j := by
    funext j
    simpa only [hgap,a] using atomMoment_eq_bare (by norm_num : 2 ≤ (2:ℕ)) hq0 j
  rw [heq,selfGrowthCooling_smul]
  exact mul_pos (pow_pos ha _) (selfGrowthCooling_bare_pos hq)

theorem source_dominant_selfGrowthCooling_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < selfGrowthCooling (thetaCuspLikelihoodCoordinate x)
      (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) := by
  apply atom_selfGrowthCooling_pos
  have he := Real.one_le_exp hx
  have he2 : 1 ≤ (Real.exp x)^2 := by nlinarith [Real.exp_pos x]
  have hpi := le_mul_of_one_le_right Real.pi_pos.le he2
  unfold thetaCuspLikelihoodCoordinate
  linarith [Real.pi_gt_d2]


open MeasureTheory

def fullPairGrowth (q : ℝ) (m n : ℕ → ℝ) : ℝ :=
  growthFunctional q (momentConvolution m n)
def fullPairGrowthSlope (q : ℝ) (m n : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, (growthCoefficientJet q (j+2)*momentConvolution m n (j+2)-
    growthCoefficient q (j+2)*(momentConvolution (fun i=>m (i+1)) n (j+2)+
      momentConvolution m (fun i=>n (i+1)) (j+2)))
def fullPairGrowthCooling (q : ℝ) (m : ℕ → ℝ) : ℝ :=
  fullPairGrowth q m m*growthSlope q m-fullPairGrowthSlope q m m*growthFunctional q m

theorem fullPairGrowth_self_eq (q : ℝ) (m : ℕ → ℝ) :
    fullPairGrowth q m m=2*m 0*growthFunctional q m+binaryGrowth q m m := by
  unfold fullPairGrowth binaryGrowth growthFunctional
  norm_num [momentConvolution,binaryMoment,Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem fullPairGrowthSlope_self_eq (q : ℝ) (m : ℕ → ℝ) :
    fullPairGrowthSlope q m m=2*m 0*growthSlope q m-
      2*m 1*growthFunctional q m+binaryGrowthSlope q m m := by
  unfold fullPairGrowthSlope growthSlope growthFunctional binaryGrowthSlope
  norm_num [momentConvolution,binaryMoment,Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem fullPairGrowthCooling_self_eq (q : ℝ) (m : ℕ → ℝ) :
    fullPairGrowthCooling q m=selfGrowthCooling q m+2*m 1*(growthFunctional q m)^2 := by
  unfold fullPairGrowthCooling
  rw [fullPairGrowth_self_eq,fullPairGrowthSlope_self_eq]
  unfold selfGrowthCooling
  ring

private theorem dominantMoment_nonneg (q : ℝ) (j : ℕ) : 0 ≤ atomMoment 2 q j := by
  unfold atomMoment
  apply integral_nonneg_of_ae
  filter_upwards [ae_nonneg_thetaCuspAtomLikelihoodSpectralMeasure (by norm_num : 2 ≤ (2:ℕ))] with t ht
  exact mul_nonneg (pow_nonneg ht _) (Real.exp_pos _).le

theorem atom_fullPairGrowthCooling_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < fullPairGrowthCooling q (atomMoment 2 q) := by
  rw [fullPairGrowthCooling_self_eq]
  exact add_pos_of_pos_of_nonneg (atom_selfGrowthCooling_pos hq)
    (mul_nonneg (mul_nonneg (by norm_num) (dominantMoment_nonneg q 1)) (sq_nonneg _))

theorem source_dominant_fullPairGrowthCooling_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < fullPairGrowthCooling (thetaCuspLikelihoodCoordinate x)
      (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) := by
  rw [fullPairGrowthCooling_self_eq]
  exact add_pos_of_pos_of_nonneg (source_dominant_selfGrowthCooling_pos hx)
    (mul_nonneg (mul_nonneg (by norm_num) (dominantMoment_nonneg _ 1)) (sq_nonneg _))
end
end RHTower.ThetaCuspDefect
