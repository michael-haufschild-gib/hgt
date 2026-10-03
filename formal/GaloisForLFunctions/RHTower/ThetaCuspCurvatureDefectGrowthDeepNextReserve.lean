import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthDeepNextReservePolynomial
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMixedPairSource
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthNextEnvelope
/-! Deep-tail reserve for the pair-relative transfer on the actual theta ray.
The artificial q = 3/2 boundary reverses the lower estimate. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open MeasureTheory Filter Set
noncomputable section

theorem polynomialMoment_nine_gap_expansion (q v : ℝ) :
    polynomialMoment q (8+v) 9=∑ k ∈ Finset.range 11, shiftedAtomMomentCoeff q 9 k*v^k := by
  norm_num [polynomialMoment,shiftedAtomMomentCoeff,Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem deepNextReserve_numerator_shift (y v : ℝ) :
    64*atomPairTransferWronskian (3/2+y) (8+v)-
      dominantPairPolynomial (3/2+y)*growthCoefficient (3/2+y) 7*
        growthNumerator (3/2+y) 3*polynomialMoment (3/2+y) (8+v) 9=
      ∑ k ∈ Finset.range 11, deepAtomNextMonomialReserve k y*v^k := by
  rw [atomPairTransferWronskian_next_expansion,polynomialMoment_nine_gap_expansion,
    dominantPairPolynomial_gap_shift_eq]
  unfold deepAtomNextMonomialReserve
  simp only [sub_mul,mul_assoc,Finset.sum_sub_distrib,Finset.mul_sum]

theorem bareDeepPairRelativeTransfer_artificial_boundary :
    pairRelativeTransferFunctional (3/2) (bareMoment (3/2) 8) <
      (pairRelativeLeadingCoefficient (3/2)/64)*bareMoment (3/2) 8 9 := by
  have hn := deepAtomNextMonomialReserve_zero_neg
  have he := deepNextReserve_numerator_shift 0 0
  norm_num only [add_zero,Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,
    pow_zero,zero_pow (by omega : (1:ℕ)≠0),mul_one,mul_zero,add_zero] at he
  have he' : 64*atomPairTransferWronskian (3/2) 8-
      dominantPairPolynomial (3/2)*growthCoefficient (3/2) 7*
        growthNumerator (3/2) 3*polynomialMoment (3/2) 8 9=deepAtomNextMonomialReserve 0 0 := by
    simpa using he
  have h := sub_neg.mp (he'.trans_lt hn)
  rw [pairRelativeTransferFunctional_bare_atom (by norm_num : (0:ℝ)<3/2),
    bareMoment_eq_polynomial (by norm_num : (3/2:ℝ)≠0)]
  unfold pairRelativeLeadingCoefficient growthTransferLeadingCoefficient
  have ht := div_lt_div_of_pos_right h (show 0 < 64*(3/2:ℝ)^8 by positivity)
  convert! ht using 1 <;> norm_num only [Nat.reduceAdd] <;> ring

theorem deepNextReserve_numerator_pos {q d : ℝ} (hq : Real.pi-3/2 ≤ q) (hd : 8 ≤ d) :
    dominantPairPolynomial q*growthCoefficient q 7*growthNumerator q 3*polynomialMoment q d 9 <
      64*atomPairTransferWronskian q d := by
  have hy : Real.pi-3 ≤ q-3/2 := by linarith
  have hv : 0 ≤ d-8 := by linarith
  have hs : 0 < ∑ k ∈ Finset.range 11, deepAtomNextMonomialReserve k (q-3/2)*(d-8)^k := by
    apply Finset.sum_pos'
    · intro k hk
      exact mul_nonneg (deepAtomNextMonomialReserve_pos _ hy k
        (by have := Finset.mem_range.mp hk; omega)).le (pow_nonneg hv k)
    · exact ⟨0,by simp,by simpa using deepAtomNextMonomialReserve_pos _ hy 0 (by omega)⟩
  rw [←deepNextReserve_numerator_shift,
    show (3/2:ℝ)+(q-3/2)=q by ring,show (8:ℝ)+(d-8)=d by ring] at hs
  exact sub_pos.mp hs

theorem bareDeepPairRelativeTransfer_lower {q d : ℝ} (hq : Real.pi-3/2 ≤ q) (hd : 8 ≤ d) :
    (pairRelativeLeadingCoefficient q/64)*bareMoment q d 9 <
      pairRelativeTransferFunctional q (bareMoment q d) := by
  have hq0 : 0 < q := by linarith [Real.pi_gt_three]
  have h := deepNextReserve_numerator_pos hq hd
  rw [pairRelativeTransferFunctional_bare_atom hq0,bareMoment_eq_polynomial hq0.ne']
  unfold pairRelativeLeadingCoefficient growthTransferLeadingCoefficient
  have ht := div_lt_div_of_pos_right h (show 0 < 64*q^8 by positivity)
  convert! ht using 1 <;> norm_num only [Nat.reduceAdd] <;> field_simp [hq0.ne']

theorem deepAtomPairRelativeTransfer_lower {q : ℝ} (hq : Real.pi-3/2 ≤ q) {n : ℕ} (hn : 3 ≤ n) :
    (pairRelativeLeadingCoefficient q/64)*atomMoment n q 9 <
      pairRelativeTransferFunctional q (atomMoment n q) := by
  have hq0 : 0 < q := by linarith [Real.pi_gt_three]
  have hd : 8 ≤ thetaCuspLikelihoodGap n := by
    have hnr : (3:ℝ) ≤ n := by exact_mod_cast hn
    unfold thetaCuspLikelihoodGap
    nlinarith
  have he : atomMoment n q=fun j => atomScale n q*bareMoment q (thetaCuspLikelihoodGap n) j := by
    funext j
    exact atomMoment_eq_bare (by omega) hq0 j
  have ha : 0 < atomScale n q := by
    unfold atomScale
    have hg : 0 < thetaCuspLikelihoodGap n+1 := by linarith
    positivity
  have h := mul_lt_mul_of_pos_left (bareDeepPairRelativeTransfer_lower hq hd) ha
  rw [he,pairRelativeTransferFunctional_smul]
  convert! h using 1; ring

theorem deepTailPairRelativeTransfer_lower {q : ℝ} (hq : Real.pi-3/2 ≤ q) :
    (pairRelativeLeadingCoefficient q/64)*thetaCuspDeepTailMoment q 9 <
      pairRelativeTransferFunctional q (thetaCuspDeepTailMoment q) := by
  have hq0 : 0 < q := by linarith [Real.pi_gt_three]
  apply hasSum_lt (i := 0) ?_ ?_ ((hasSum_deepAtomMoment hq0 9).mul_left _)
    (hasSum_pairRelativeTransfer q (fun n => atomMoment (n+3) q)
      (thetaCuspDeepTailMoment q) (hasSum_deepAtomMoment hq0))
  · intro n
    exact (deepAtomPairRelativeTransfer_lower hq (by omega : 3 ≤ n+3)).le
  · exact deepAtomPairRelativeTransfer_lower hq (by omega : 3 ≤ 0+3)

theorem source_deepTailPairRelativeTransfer_lower {x : ℝ} (hx : 0 ≤ x) :
    (pairRelativeLeadingCoefficient (thetaCuspLikelihoodCoordinate x)/64)*
      thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) 9 <
        pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
          (thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x)) := by
  apply deepTailPairRelativeTransfer_lower
  have he := Real.one_le_exp hx
  have he2 : 1 ≤ (Real.exp x)^2 := by nlinarith [Real.exp_pos x]
  have hp := le_mul_of_one_le_right Real.pi_pos.le he2
  unfold thetaCuspLikelihoodCoordinate
  linarith

theorem deepMoment_self_convolution_le {q : ℝ} (hq : 0 < q) (j : ℕ) :
    momentConvolution (thetaCuspDeepTailMoment q) (thetaCuspDeepTailMoment q) j ≤
      2^j*thetaCuspDeepTailMoment q 0*thetaCuspDeepTailMoment q j := by
  unfold momentConvolution
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*
        (thetaCuspDeepTailMoment q 0*thetaCuspDeepTailMoment q j) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i+(j-i)=j := by have := Finset.mem_range.mp hi; omega
      have h := deepMoment_mul_le_mass_mul hq i (j-i)
      rw [hij] at h
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (show 0 ≤ (j.choose i:ℝ) by positivity)
    _ = _ := by
      have hb : (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ))=(2:ℝ)^j := by
        simpa [show (1:ℝ)+1=2 by norm_num] using (add_pow (1:ℝ) 1 j).symm
      rw [←Finset.sum_mul,hb]
      ring

theorem deepPairPairRelativeTransfer_upper {q : ℝ} (hq : 3/2 ≤ q) :
    pairRelativeTransferFunctional q (momentConvolution (thetaCuspDeepTailMoment q) (thetaCuspDeepTailMoment q)) ≤
      512*pairRelativeLeadingCoefficient q*thetaCuspDeepTailMoment q 0*thetaCuspDeepTailMoment q 9 := by
  have hq0 : 0 < q := by linarith
  let D := componentTilt q thetaCuspDeepTailSpectralMeasure
  have hi : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) D :=
    integrable_pow_componentTilt q _ (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq0)
  letI : IsFiniteMeasure D := componentTilt_finite q _
    (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq0)
  have hm : measureMoment D=thetaCuspDeepTailMoment q := by
    funext j
    exact measureMoment_componentTilt q _ j
  have hsD : ∀ᵐ t ∂D, 8 ≤ t := ae_lower_componentTilt q _ ae_eight_le_thetaCuspDeepTailSpectralMeasure
  have hs : ∀ᵐ t ∂(D ∗ D), 9 ≤ t := by
    filter_upwards [ae_add_lower_measure_conv D D hsD hsD] with t ht
    linarith
  have hu := component_pairRelativeTransfer_upper hq (D ∗ D)
    (integrable_pow_measure_conv D D hi hi) hs
  have he : measureMoment (D ∗ D)=momentConvolution (thetaCuspDeepTailMoment q) (thetaCuspDeepTailMoment q) := by
    funext j
    rw [measureMoment_conv D D hi hi,hm]
  rw [he] at hu
  have hb := mul_le_mul_of_nonneg_left (deepMoment_self_convolution_le hq0 9)
    (pairRelativeLeadingCoefficient_pos hq).le
  norm_num at hb
  nlinarith only [hu,hb]

end
end RHTower.ThetaCuspDefect
