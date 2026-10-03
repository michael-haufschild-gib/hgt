import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthDominantCubic
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMixedNextTransport
/-! Exact fourth convolution of the literal dominant point-and-ray source
and ninth-moment transport of every dominant sector. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open MeasureTheory Filter Set
noncomputable section
def quadrupleMomentPolynomial (q : ℝ) (j : ℕ) : ℝ :=
  256*12^j*q^(j+4)+
    1152*q^3*(∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*12^(j-i)*(i.factorial:ℝ)*q^(j-i))+
    1944*q^2*(∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*12^(j-i)*((i+1).factorial:ℝ)*q^(j-i))+
    729*q*(∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*12^(j-i)*((i+2).factorial:ℝ)*q^(j-i))+
    (2187/32)*(∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*12^(j-i)*((i+3).factorial:ℝ)*q^(j-i))

def dominantQuadruplePolynomial (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 6,
    ((growthCoefficient q (i+2)*slopeNumerator q 3-
      q*growthCoefficientJet q (i+2)*growthNumerator q 3)*q^(5-i)*quadrupleMomentPolynomial q (i+2)+
      growthCoefficient q (i+2)*growthNumerator q 3*q^(5-i)*quadrupleMomentPolynomial q (i+3))

theorem quadrupleMomentPolynomial_0 (q : ℝ) :
    momentConvolution (polynomialMoment q 3) (tripleMomentPolynomial q) 0=
      quadrupleMomentPolynomial q 0 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,quadrupleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem quadrupleMomentPolynomial_1 (q : ℝ) :
    momentConvolution (polynomialMoment q 3) (tripleMomentPolynomial q) 1=
      quadrupleMomentPolynomial q 1 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,quadrupleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem quadrupleMomentPolynomial_2 (q : ℝ) :
    momentConvolution (polynomialMoment q 3) (tripleMomentPolynomial q) 2=
      quadrupleMomentPolynomial q 2 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,quadrupleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem quadrupleMomentPolynomial_3 (q : ℝ) :
    momentConvolution (polynomialMoment q 3) (tripleMomentPolynomial q) 3=
      quadrupleMomentPolynomial q 3 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,quadrupleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem quadrupleMomentPolynomial_4 (q : ℝ) :
    momentConvolution (polynomialMoment q 3) (tripleMomentPolynomial q) 4=
      quadrupleMomentPolynomial q 4 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,quadrupleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem quadrupleMomentPolynomial_5 (q : ℝ) :
    momentConvolution (polynomialMoment q 3) (tripleMomentPolynomial q) 5=
      quadrupleMomentPolynomial q 5 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,quadrupleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem quadrupleMomentPolynomial_6 (q : ℝ) :
    momentConvolution (polynomialMoment q 3) (tripleMomentPolynomial q) 6=
      quadrupleMomentPolynomial q 6 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,quadrupleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem quadrupleMomentPolynomial_7 (q : ℝ) :
    momentConvolution (polynomialMoment q 3) (tripleMomentPolynomial q) 7=
      quadrupleMomentPolynomial q 7 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,quadrupleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem quadrupleMomentPolynomial_8 (q : ℝ) :
    momentConvolution (polynomialMoment q 3) (tripleMomentPolynomial q) 8=
      quadrupleMomentPolynomial q 8 := by
  norm_num [momentConvolution,polynomialMoment,tripleMomentPolynomial,quadrupleMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem quadrupleMomentPolynomial_eq (q : ℝ) {j : ℕ} (hj : j ≤ 8) :
    momentConvolution (polynomialMoment q 3) (tripleMomentPolynomial q) j=
      quadrupleMomentPolynomial q j := by
  interval_cases j
  · exact quadrupleMomentPolynomial_0 q
  · exact quadrupleMomentPolynomial_1 q
  · exact quadrupleMomentPolynomial_2 q
  · exact quadrupleMomentPolynomial_3 q
  · exact quadrupleMomentPolynomial_4 q
  · exact quadrupleMomentPolynomial_5 q
  · exact quadrupleMomentPolynomial_6 q
  · exact quadrupleMomentPolynomial_7 q
  · exact quadrupleMomentPolynomial_8 q

theorem spectralPowerMoment_bare_four {q : ℝ} (hq : 0 < q) {j : ℕ} (hj : j ≤ 8) :
    spectralPowerMoment (bareMoment q 3) 4 j=quadrupleMomentPolynomial q j/q^(j+4) := by
  rw [show 4=3+1 by omega,spectralPowerMoment_succ _ 3 hj,←quadrupleMomentPolynomial_eq q hj]
  unfold momentConvolution
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
  rw [bareMoment_eq_polynomial hq.ne',spectralPowerMoment_bare_three hq (by omega : j-i ≤ 8)]
  have he : q^(i+1)*q^(j-i+3)=q^(j+4) := by
    rw [←pow_add]
    congr 1
    omega
  rw [←he]
  field_simp [hq.ne']

theorem growthTransferFunctional_bare_four {q : ℝ} (hq : 0 < q) :
    growthTransferFunctional q (spectralPowerMoment (bareMoment q 3) 4)=
      dominantQuadruplePolynomial q/q^11 := by
  unfold growthTransferFunctional dominantQuadruplePolynomial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi5 : i ≤ 5 := by have := Finset.mem_range.mp hi; omega
  rw [spectralPowerMoment_bare_four hq (by omega : i+2 ≤ 8),
    spectralPowerMoment_bare_four hq (by omega : i+3 ≤ 8)]
  interval_cases i <;> norm_num only [Nat.reduceAdd,Nat.reduceSub] <;> field_simp [hq.ne']


theorem dominantPower_pairRelative_bounds {q : ℝ} (hq : 3/2 ≤ q) {k : ℕ} (hk : 3 ≤ k) :
    0 ≤ pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) k) ∧
      pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) k) ≤
        pairRelativeLeadingCoefficient q*((k:ℝ)^9*atomMoment 2 q 0^(k-1)*atomMoment 2 q 9) := by
  have hq0 : 0 < q := by linarith
  let A := componentTilt q thetaCuspSecondAtomSpectralMeasure
  have hi := integrable_pow_componentTilt q thetaCuspSecondAtomSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure j hq0)
  letI : IsFiniteMeasure A := componentTilt_finite q thetaCuspSecondAtomSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure j hq0)
  have hA : measureMoment A=atomMoment 2 q := by
    funext j
    rw [measureMoment_componentTilt]
    simp only [atomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul]
  have hsA : ∀ᵐ t ∂A, (3:ℝ) ≤ t :=
    ae_lower_componentTilt q _ (ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure.filter_mono
      (ae_mono thetaCuspSecondAtomSpectralMeasure_le))
  have hs : ∀ᵐ t ∂convolutionPower A k, (9:ℝ) ≤ t := by
    filter_upwards [ae_lower_convolutionPower A hsA k] with t ht
    have hkr : (3:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hp := integrable_pow_convolutionPower A hi k
  have hn : 0 ≤ pairRelativeTransferFunctional q (measureMoment (convolutionPower A k)) := by
    rw [←integral_pairRelativeTransferKernel q _ hp]
    apply integral_nonneg_of_ae
    filter_upwards [hs] with t ht
    exact (pairRelativeTransferKernel_pos hq ht).le
  have hu := component_pairRelativeTransfer_upper hq (convolutionPower A k) hp hs
  rw [pairRelativeTransferFunctional_convolutionPower q A hi k,hA] at hn hu
  rw [measureMoment_convolutionPower_nine A hi k (by omega : 9 ≤ 9),hA] at hu
  have hm := dominantConvolution_moment_nine_le hq0 (k-1) (by omega : 9 ≤ 9)
  rw [show k-1+1=k by omega] at hm
  exact ⟨hn,hu.trans (mul_le_mul_of_nonneg_left hm (pairRelativeLeadingCoefficient_pos hq).le)⟩

end
end RHTower.ThetaCuspDefect
