import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthMixedPairAbsorption
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthDeepMomentOrdering
/-! Exact mixed-pair absorption for every deep atom and the complete
infinite tail. Dominant single and self-pair terms vanish; the actual
weighted mixed pair consumes less than 256/399 of the positive deep
reserve. Remaining even-sector absorption is a separate source gap. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open Filter Set Topology
noncomputable section

theorem pairRelativeTransferFunctional_smul (q a : ℝ) (m : ℕ → ℝ) :
    pairRelativeTransferFunctional q (fun j => a*m j)=a*pairRelativeTransferFunctional q m := by
  unfold pairRelativeTransferFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairRelativeTransferFunctional_add (q : ℝ) (m n : ℕ → ℝ) :
    pairRelativeTransferFunctional q (fun j => m j+n j)=
      pairRelativeTransferFunctional q m+pairRelativeTransferFunctional q n := by
  unfold pairRelativeTransferFunctional
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem momentConvolution_smul_pair (a b : ℝ) (m n : ℕ → ℝ) :
    momentConvolution (fun j => a*m j) (fun j => b*n j)=
      fun j => (a*b)*momentConvolution m n j := by
  funext j
  unfold momentConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairRelativeTransferFunctional_bare_dominant_zero {q : ℝ} (hq : 0 < q) :
    pairRelativeTransferFunctional q (bareMoment q 3)=0 := by
  rw [pairRelativeTransferFunctional_bare_atom hq]
  unfold atomPairTransferWronskian atomTransferNumerator atomTransferNumeratorJet
  ring

theorem mixedPairTransferNumerator_dominant {q : ℝ} (hq : 0 < q) :
    mixedPairTransferNumerator q 3=dominantPairPolynomial q := by
  have h := growthTransferFunctional_bare_pair hq
  rw [growthTransferFunctional_power_two,growthTransferFunctional_bare_mixed_pair hq] at h
  exact (div_left_inj' (pow_ne_zero 9 hq.ne')).mp h

theorem mixedPairTransferNumeratorJet_dominant {q : ℝ} (hq : 0 < q) :
    mixedPairTransferNumeratorJet q 3=dominantPairPolynomialJet q := by
  have he : (fun r => mixedPairTransferNumerator r 3)=ᶠ[nhds q] dominantPairPolynomial := by
    filter_upwards [eventually_gt_nhds hq] with r hr
    exact mixedPairTransferNumerator_dominant hr
  exact (hasDerivAt_mixedPairTransferNumerator q 3).unique
    ((hasDerivAt_dominantPairPolynomial q).congr_of_eventuallyEq he)

theorem pairRelativeTransferFunctional_bare_pair_zero {q : ℝ} (hq : 0 < q) :
    pairRelativeTransferFunctional q (momentConvolution (bareMoment q 3) (bareMoment q 3))=0 := by
  rw [pairRelativeTransferFunctional_bare_mixed_pair hq]
  unfold mixedPairTransferNextNumerator
  rw [mixedPairTransferNumerator_dominant hq,mixedPairTransferNumeratorJet_dominant hq]
  ring

theorem pairRelativeTransferFunctional_dominant_zero {q : ℝ} (hq : 0 < q) :
    pairRelativeTransferFunctional q (atomMoment 2 q)=0 := by
  have he : atomMoment 2 q=fun j => dominantAtomScale q*bareMoment q 3 j := by
    funext j
    exact atomMoment_two_eq_scale hq j
  rw [he,pairRelativeTransferFunctional_smul,pairRelativeTransferFunctional_bare_dominant_zero hq,mul_zero]

theorem pairRelativeTransferFunctional_dominant_pair_zero {q : ℝ} (hq : 0 < q) :
    pairRelativeTransferFunctional q (momentConvolution (atomMoment 2 q) (atomMoment 2 q))=0 := by
  have he : atomMoment 2 q=fun j => dominantAtomScale q*bareMoment q 3 j := by
    funext j
    exact atomMoment_two_eq_scale hq j
  rw [he,momentConvolution_smul_pair,pairRelativeTransferFunctional_smul,
    pairRelativeTransferFunctional_bare_pair_zero hq,mul_zero]

theorem dominantDeepAtom_relative_absorption {q : ℝ} (hq : 3/2 ≤ q) {n : ℕ} (hn : 3 ≤ n) :
    pairRelativeTransferFunctional q (momentConvolution (atomMoment 2 q) (atomMoment n q)) <
      256*atomMoment 2 q 0*pairRelativeTransferFunctional q (atomMoment n q) := by
  have hq0 : 0 < q := by linarith
  have hd : 8 ≤ thetaCuspLikelihoodGap n := by
    have hnr : (3:ℝ) ≤ n := by exact_mod_cast hn
    unfold thetaCuspLikelihoodGap
    nlinarith
  have ham : atomMoment 2 q=fun j => dominantAtomScale q*bareMoment q 3 j := by
    funext j
    exact atomMoment_two_eq_scale hq0 j
  have hbn : atomMoment n q=fun j => atomScale n q*bareMoment q (thetaCuspLikelihoodGap n) j := by
    funext j
    exact atomMoment_eq_bare (by omega) hq0 j
  have hb : 0 < atomScale n q := by
    unfold atomScale
    have hg : 0 < thetaCuspLikelihoodGap n+1 := by linarith
    positivity
  have h := mul_lt_mul_of_pos_left (exactMixedPair_relative_absorption hq hd)
    (mul_pos (dominantAtomScale_pos q) hb)
  rw [ham,hbn,momentConvolution_smul_pair,pairRelativeTransferFunctional_smul,
    pairRelativeTransferFunctional_smul]
  convert! h using 1; ring

theorem hasSum_pairRelativeTransfer (q : ℝ) (m : ℕ → ℕ → ℝ) (s : ℕ → ℝ)
    (hs : ∀ j, HasSum (fun n => m n j) (s j)) :
    HasSum (fun n => pairRelativeTransferFunctional q (m n)) (pairRelativeTransferFunctional q s) := by
  unfold pairRelativeTransferFunctional
  exact hasSum_sum (fun i _ =>
    (((hs (i+2)).mul_left _).add ((hs (i+3)).mul_left _)).add ((hs (i+4)).mul_left _))

theorem hasSum_momentConvolution_right (a : ℕ → ℝ) (m : ℕ → ℕ → ℝ) (s : ℕ → ℝ)
    (hs : ∀ j, HasSum (fun n => m n j) (s j)) (j : ℕ) :
    HasSum (fun n => momentConvolution a (m n) j) (momentConvolution a s j) := by
  unfold momentConvolution
  exact hasSum_sum (fun i _ => (hs (j-i)).mul_left _)

theorem momentConvolution_add_right (a b c : ℕ → ℝ) :
    momentConvolution a (fun j => b j+c j)=
      fun j => momentConvolution a b j+momentConvolution a c j := by
  funext j
  unfold momentConvolution
  simp only [mul_add,Finset.sum_add_distrib]

theorem hasSum_deepAtomMoment {q : ℝ} (hq : 0 < q) (j : ℕ) :
    HasSum (fun n : ℕ => atomMoment (n+3) q j) (thetaCuspDeepTailMoment q j) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_atomMoment hq j)
  simpa [fullMoment_eq_atom_add_deep hq j,Nat.add_assoc] using h

theorem hasSum_atomPairRelative_deep {q : ℝ} (hq : 0 < q) :
    HasSum (fun n : ℕ => pairRelativeTransferFunctional q (atomMoment (n+2) q))
      (pairRelativeTransferFunctional q (thetaCuspDeepTailMoment q)) := by
  have h := hasSum_pairRelativeTransfer q (fun n => atomMoment (n+2) q)
    (thetaCuspHigherLikelihoodSpectralMoment q) (hasSum_atomMoment hq)
  have he : thetaCuspHigherLikelihoodSpectralMoment q=
      fun j => atomMoment 2 q j+thetaCuspDeepTailMoment q j := by
    funext j
    exact fullMoment_eq_atom_add_deep hq j
  rw [he,pairRelativeTransferFunctional_add,pairRelativeTransferFunctional_dominant_zero hq,zero_add] at h
  exact h

theorem hasSum_dominantMixedPairRelative_deep {q : ℝ} (hq : 0 < q) :
    HasSum (fun n : ℕ => pairRelativeTransferFunctional q
      (momentConvolution (atomMoment 2 q) (atomMoment (n+2) q)))
      (pairRelativeTransferFunctional q (momentConvolution (atomMoment 2 q) (thetaCuspDeepTailMoment q))) := by
  have h := hasSum_pairRelativeTransfer q (fun n => momentConvolution (atomMoment 2 q) (atomMoment (n+2) q))
    (momentConvolution (atomMoment 2 q) (thetaCuspHigherLikelihoodSpectralMoment q))
    (hasSum_momentConvolution_right _ _ _ (hasSum_atomMoment hq))
  have he : thetaCuspHigherLikelihoodSpectralMoment q=
      fun j => atomMoment 2 q j+thetaCuspDeepTailMoment q j := by
    funext j
    exact fullMoment_eq_atom_add_deep hq j
  rw [he,momentConvolution_add_right,pairRelativeTransferFunctional_add,
    pairRelativeTransferFunctional_dominant_pair_zero hq,zero_add] at h
  exact h

theorem deepAtomPairRelativeTransfer_pos {q : ℝ} (hq : 3/2 ≤ q) {n : ℕ} (hn : 3 ≤ n) :
    0 < pairRelativeTransferFunctional q (atomMoment n q) := by
  have hq0 : 0 < q := by linarith
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
  rw [he,pairRelativeTransferFunctional_smul,pairRelativeTransferFunctional_bare_atom hq0]
  exact mul_pos ha (div_pos (atomPairTransferWronskian_pos hq hd) (pow_pos hq0 8))

theorem deepTailPairRelativeTransfer_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < pairRelativeTransferFunctional q (thetaCuspDeepTailMoment q) := by
  have hq0 : 0 < q := by linarith
  have hz : HasSum (fun _ : ℕ => (0:ℝ)) 0 := hasSum_zero
  apply hasSum_lt (i := 1) ?_ ?_ hz (hasSum_atomPairRelative_deep hq0)
  · intro n
    by_cases hn : n=0
    · subst n
      simp only [Nat.zero_add,pairRelativeTransferFunctional_dominant_zero hq0,le_refl]
    · exact (deepAtomPairRelativeTransfer_pos hq (by omega : 3 ≤ n+2)).le
  · exact deepAtomPairRelativeTransfer_pos hq (by omega : 3 ≤ 1+2)

theorem dominantDeepTail_relative_absorption {q : ℝ} (hq : 3/2 ≤ q) :
    pairRelativeTransferFunctional q (momentConvolution (atomMoment 2 q) (thetaCuspDeepTailMoment q)) <
      256*atomMoment 2 q 0*pairRelativeTransferFunctional q (thetaCuspDeepTailMoment q) := by
  have hq0 : 0 < q := by linarith
  apply hasSum_lt (i := 1) ?_ ?_ (hasSum_dominantMixedPairRelative_deep hq0)
    ((hasSum_atomPairRelative_deep hq0).mul_left _)
  · intro n
    by_cases hn : n=0
    · subst n
      simp only [Nat.zero_add,pairRelativeTransferFunctional_dominant_pair_zero hq0,
        pairRelativeTransferFunctional_dominant_zero hq0,mul_zero,le_refl]
    · exact (dominantDeepAtom_relative_absorption hq (by omega : 3 ≤ n+2)).le
  · exact dominantDeepAtom_relative_absorption hq (by omega : 3 ≤ 1+2)

theorem dominantDeepTail_weighted_relative_absorption {x : ℝ} (hx : 0 ≤ x) :
    normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) 2*
      (2*pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
        (momentConvolution (atomMoment 2 (thetaCuspLikelihoodCoordinate x))
          (thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x)))) <
      (256/399)*pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
        (thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x)) := by
  let q := thetaCuspLikelihoodCoordinate x
  have hq0 : 0 < q := thetaCuspLikelihoodCoordinate_pos hx
  have hq : (3/2:ℝ) ≤ q := by
    have hexp : 1 ≤ Real.exp x := Real.one_le_exp hx
    have hsq : 1 ≤ Real.exp x^2 := by nlinarith [Real.exp_pos x]
    dsimp only [q,thetaCuspLikelihoodCoordinate]
    nlinarith [Real.pi_gt_three,Real.pi_pos]
  have hF := deepTailPairRelativeTransfer_pos hq
  have ha0 : 0 ≤ atomMoment 2 q 0 := by
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspSecondAtomMoment_nonneg q 0
  have hM : atomMoment 2 q 0 ≤ thetaCuspHigherLikelihoodSpectralMoment q 0 := by
    rw [fullMoment_eq_atom_add_deep hq0]
    exact le_add_of_nonneg_right (thetaCuspDeepTailMoment_nonneg q 0)
  have hactivity := three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  change 399*thetaCuspHigherLikelihoodSpectralResponse q < 1 at hactivity
  rw [←thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hq0] at hactivity
  have hmass : 399*atomMoment 2 q 0 < 1 := by linarith
  have hJ := dominantDeepTail_relative_absorption hq
  have hW := normalizedTransferWeight_le hq0 (k := 2) (by omega)
  have hw0 := normalizedTransferWeight_pos hq0 (k := 2) (by omega)
  have h1 := mul_lt_mul_of_pos_left hJ (show 0 < 2*normalizedTransferWeight q 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hW
    (show 0 ≤ 512*atomMoment 2 q 0*pairRelativeTransferFunctional q (thetaCuspDeepTailMoment q) by positivity)
  have h3 := mul_lt_mul_of_pos_right hmass hF
  change normalizedTransferWeight q 2*
    (2*pairRelativeTransferFunctional q (momentConvolution (atomMoment 2 q) (thetaCuspDeepTailMoment q))) <
      (256/399)*pairRelativeTransferFunctional q (thetaCuspDeepTailMoment q)
  norm_num at h1 h2
  nlinarith only [h1,h2,h3]

end
end RHTower.ThetaCuspDefect
