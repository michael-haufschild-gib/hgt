import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMixedPairKernel
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthNextConvolution
/-! Exact bare-moment flow identifies the pair-relative functional with its
checked single-atom and mixed-pair numerators. The coupled comparison
holds throughout the stable parameter/gap domain. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open Filter Set Topology
noncomputable section

theorem polynomialMoment_flow (q d : ℝ) (j : ℕ) (hj : j ≤ 8) :
    q*polynomialMomentJet q d j-(j+1:ℕ)*polynomialMoment q d j=
      q*d*polynomialMoment q d j-polynomialMoment q d (j+1) := by
  interval_cases j <;>
    norm_num [polynomialMoment,polynomialMomentJet,Finset.sum_range_succ,
      Nat.choose,Nat.factorial] <;> ring

theorem hasDerivAt_bareMoment {q : ℝ} (hq : 0 < q) (d : ℝ) (j : ℕ) (hj : j ≤ 8) :
    HasDerivAt (fun r => bareMoment r d j)
      (d*bareMoment q d j-bareMoment q d (j+1)) q := by
  have h := (hasDerivAt_polynomialMoment q d j).div (hasDerivAt_pow (j+1) q)
    (pow_ne_zero _ hq.ne')
  have hd : HasDerivAt (fun r => polynomialMoment r d j/r^(j+1))
      (d*bareMoment q d j-bareMoment q d (j+1)) q := h.congr_deriv (by
    rw [bareMoment_eq_polynomial hq.ne',bareMoment_eq_polynomial hq.ne']
    have hp := polynomialMoment_flow q d j hj
    have hp' : polynomialMoment q d (j+1)=
        q*d*polynomialMoment q d j-(q*polynomialMomentJet q d j-(j+1:ℕ)*polynomialMoment q d j) := by
      linarith only [hp]
    rw [hp']
    simp only [Nat.add_sub_cancel,pow_succ]
    field_simp [hq.ne']
    ring)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hq] with r hr
  exact bareMoment_eq_polynomial hr.ne' d j

theorem hasDerivAt_bareMomentConvolution {q : ℝ} (hq : 0 < q) (a b : ℝ)
    (j : ℕ) (hj : j ≤ 8) :
    HasDerivAt (fun r => momentConvolution (bareMoment r a) (bareMoment r b) j)
      ((a+b)*momentConvolution (bareMoment q a) (bareMoment q b) j-
        momentConvolution (bareMoment q a) (bareMoment q b) (j+1)) q := by
  have hs := HasDerivAt.fun_sum (u := Finset.range (j+1)) (fun i hi =>
    ((hasDerivAt_bareMoment hq a i (by have := Finset.mem_range.mp hi; omega)).mul
      (hasDerivAt_bareMoment hq b (j-i) (by omega))).const_mul (j.choose i:ℝ))
  convert! hs using 1
  · funext r
    unfold momentConvolution
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.mul_apply,mul_assoc]
  · rw [←momentConvolution_shift _ _ j hj]
    unfold momentConvolution
    simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem hasDerivAt_transferFunctional_of_momentFlow (m : ℝ → ℕ → ℝ) (q c : ℝ)
    (hm : ∀ j, j ≤ 8 → HasDerivAt (fun r => m r j) (c*m q j-m q (j+1)) q) :
    HasDerivAt (fun r => growthTransferFunctional r (m r))
      (transferFlowFunctional q (m q)+c*growthTransferFunctional q (m q)) q := by
  have hs : HasDerivAt (fun r => growthTransferFunctional r (m r))
      (∑ i ∈ Finset.range 6,
        (transferLowCoefficientJet q i*m q (i+2)+transferLowCoefficient q i*(c*m q (i+2)-m q (i+3))+
        (transferHighCoefficientJet q i*m q (i+3)+transferHighCoefficient q i*(c*m q (i+3)-m q (i+4))))) q := by
    unfold growthTransferFunctional
    apply HasDerivAt.fun_sum
    intro i hi
    have hi5 : i ≤ 5 := by have := Finset.mem_range.mp hi; omega
    exact (((hasDerivAt_transferLowCoefficient q hi5).mul (hm (i+2) (by omega))).add
      ((hasDerivAt_transferHighCoefficient q hi5).mul (hm (i+3) (by omega)))).congr_deriv
      (by norm_num only [Nat.add_assoc,Nat.reduceAdd])
  apply hs.congr_deriv
  unfold transferFlowFunctional growthTransferFunctional
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold transferLowCoefficient transferHighCoefficient
  ring

theorem pairRelativeTransferFunctional_bare_atom {q : ℝ} (hq : 0 < q) (d : ℝ) :
    pairRelativeTransferFunctional q (bareMoment q d)=atomPairTransferWronskian q d/q^8 := by
  have h := hasDerivAt_transferFunctional_of_momentFlow (fun r => bareMoment r d) q d
    (hasDerivAt_bareMoment hq d)
  have hfrac := (hasDerivAt_atomTransferNumerator q d).div (hasDerivAt_pow 8 q)
    (pow_ne_zero _ hq.ne')
  have he : (fun r => growthTransferFunctional r (bareMoment r d))=ᶠ[nhds q]
      (fun r => atomTransferNumerator r d/r^8) := by
    filter_upwards [eventually_gt_nhds hq] with r hr
    exact growthTransferFunctional_bare_atom hr d
  have hd := h.unique (hfrac.congr_of_eventuallyEq he)
  simp only [Nat.reduceSub,Nat.cast_ofNat] at hd
  rw [growthTransferFunctional_bare_atom hq d] at hd
  rw [pairRelativeTransferFunctional_flow,growthTransferFunctional_bare_atom hq d]
  unfold atomPairTransferWronskian
  have ht : transferFlowFunctional q (bareMoment q d)=
      (q*atomTransferNumeratorJet q d-(8+d*q)*atomTransferNumerator q d)/q^9 := by
    calc
      _ = (atomTransferNumeratorJet q d*q^8-atomTransferNumerator q d*(8*q^7))/(q^8)^2-
          d*(atomTransferNumerator q d/q^8) := by linarith only [hd]
      _ = _ := by field_simp [hq.ne']; ring
  rw [ht]
  field_simp [hq.ne']
  ring

theorem pairRelativeTransferFunctional_bare_mixed_pair {q : ℝ} (hq : 0 < q) (d : ℝ) :
    pairRelativeTransferFunctional q (momentConvolution (bareMoment q 3) (bareMoment q d))=
      mixedPairTransferNextNumerator q d/q^8 := by
  have h := hasDerivAt_transferFunctional_of_momentFlow
    (fun r => momentConvolution (bareMoment r 3) (bareMoment r d)) q (3+d)
    (hasDerivAt_bareMomentConvolution hq 3 d)
  have hfrac := (hasDerivAt_mixedPairTransferNumerator q d).div (hasDerivAt_pow 9 q)
    (pow_ne_zero _ hq.ne')
  have he : (fun r => growthTransferFunctional r (momentConvolution (bareMoment r 3) (bareMoment r d)))=ᶠ[nhds q]
      (fun r => mixedPairTransferNumerator r d/r^9) := by
    filter_upwards [eventually_gt_nhds hq] with r hr
    exact growthTransferFunctional_bare_mixed_pair hr d
  have hd := h.unique (hfrac.congr_of_eventuallyEq he)
  simp only [Nat.reduceSub,Nat.cast_ofNat] at hd
  rw [growthTransferFunctional_bare_mixed_pair hq d] at hd
  rw [pairRelativeTransferFunctional_flow,growthTransferFunctional_bare_mixed_pair hq d]
  unfold mixedPairTransferNextNumerator
  have ht : transferFlowFunctional q (momentConvolution (bareMoment q 3) (bareMoment q d))=
      (q*mixedPairTransferNumeratorJet q d-(9+(3+d)*q)*mixedPairTransferNumerator q d)/q^10 := by
    calc
      _ = (mixedPairTransferNumeratorJet q d*q^9-mixedPairTransferNumerator q d*(9*q^8))/(q^9)^2-
          (3+d)*(mixedPairTransferNumerator q d/q^9) := by linarith only [hd]
      _ = _ := by field_simp [hq.ne']; ring
  rw [ht]
  field_simp [hq.ne']
  ring

theorem exactMixedPair_relative_absorption {q d : ℝ} (hq : 3/2 ≤ q) (hd : 8 ≤ d) :
    pairRelativeTransferFunctional q (momentConvolution (bareMoment q 3) (bareMoment q d)) <
      256*bareMoment q 3 0*pairRelativeTransferFunctional q (bareMoment q d) := by
  have hq0 : 0 < q := by linarith
  have h := mixedPairTransferNextNumerator_absorption hq hd
  rw [pairRelativeTransferFunctional_bare_mixed_pair hq0 d,
    pairRelativeTransferFunctional_bare_atom hq0 d,bareMoment_eq_polynomial hq0.ne']
  have ht := div_lt_div_of_pos_right h (pow_pos hq0 9)
  convert! ht using 1 <;> norm_num only [Nat.zero_add,pow_one] <;> field_simp [hq0.ne']

end
end RHTower.ThetaCuspDefect
