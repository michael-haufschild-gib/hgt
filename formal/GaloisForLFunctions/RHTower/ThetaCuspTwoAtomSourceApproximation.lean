import GaloisForLFunctions.RHTower.ThetaCuspDeepTailCooling

/-!
# Exact two-atom source approximation with a complete controlled remainder

The first two atoms are retained literally. The n≥3 error is the first atom
times its full positive spectral remainder, at every source point and every
derivative order in the positive half-line.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology Set Polynomial
open scoped ContDiff
set_option maxHeartbeats 1500000

/-- The literal sum of the first two theta-source atoms. -/
def thetaCuspTwoAtomSource (x : ℝ) : ℝ := thetaCuspSourceTerm x 1+thetaCuspSourceTerm x 2

/-- Every individual source atom is smooth, with its original normalization. -/
theorem contDiff_thetaCuspSourceAtom (n : ℕ) :
    ContDiff ℝ ∞ (fun x : ℝ => thetaCuspSourceTerm x n) := by
  rw [thetaCuspSourceTerm_eq_polynomialAtom]
  unfold thetaCuspPolynomialAtom
  simp only [thetaCuspSeedPolynomial, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  fun_prop

/-- The two retained atoms form a globally smooth source. -/
theorem contDiff_thetaCuspTwoAtomSource : ContDiff ℝ ∞ thetaCuspTwoAtomSource :=
  (contDiff_thetaCuspSourceAtom 1).add (contDiff_thetaCuspSourceAtom 2)

/-- The second spectral component is exactly the literal second-to-first source ratio. -/
theorem thetaCuspSecondAtomMoment_zero_eq_source_ratio {x : ℝ} (hx : 0 < x) :
    thetaCuspSecondAtomMoment (thetaCuspLikelihoodCoordinate x) 0 =
      thetaCuspSourceTerm x 2/thetaCuspSourceTerm x 1 := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  unfold thetaCuspSecondAtomMoment thetaCuspSecondAtomSpectralMeasure
  simp only [pow_zero, one_mul]
  rw [integral_exp_neg_mul_thetaCuspAtomLikelihoodSpectralMeasure (by norm_num) hB,
    ← thetaCuspAtomLikelihoodRatio_eq_spectralTerm_of_coordinate_pos hB]
  rfl

/-- Exact all-atom incidence of the deep remainder, without a finite source replacement. -/
theorem thetaCuspFullSource_sub_two_eq_first_mul_deep {x : ℝ} (hx : 0 < x) :
    thetaCuspFullSource x-thetaCuspTwoAtomSource x =
      thetaCuspSourceTerm x 1*thetaCuspDeepLikelihoodRemainder x := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hs := thetaCuspSecondAtomMoment_zero_eq_source_ratio hx
  have hf := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))).ne'
  have hs' := (eq_div_iff hf).mp hs
  rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition hB,
    thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB,
    thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hB 0]
  unfold thetaCuspTwoAtomSource thetaCuspDeepLikelihoodRemainder
  nlinarith only [hs']

/-- The complete deep likelihood is smooth wherever the first source atom is positive. -/
theorem contDiffAt_thetaCuspDeepLikelihoodRemainder {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ thetaCuspDeepLikelihoodRemainder x := by
  have he : thetaCuspDeepLikelihoodRemainder =ᶠ[𝓝 x]
      (fun y => (thetaCuspFullSource y-thetaCuspTwoAtomSource y)/thetaCuspSourceTerm y 1) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [thetaCuspFullSource_sub_two_eq_first_mul_deep hy,
      mul_div_cancel_left₀ _ (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hy (by norm_num)).ne']
  exact (((contDiff_thetaCuspFullSource.sub contDiff_thetaCuspTwoAtomSource).contDiffAt).div
    (contDiff_thetaCuspSourceAtom 1).contDiffAt
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne').congr_of_eventuallyEq he

/-- Every full-source derivative retains the exact infinite deep-tail error. -/
theorem thetaCuspFullSource_derivative_sub_two_eq (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n thetaCuspFullSource x-iteratedDeriv n thetaCuspTwoAtomSource x =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
        iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x*
        iteratedDeriv (n-i) thetaCuspDeepLikelihoodRemainder x := by
  have he : (fun y => thetaCuspFullSource y-thetaCuspTwoAtomSource y) =ᶠ[𝓝 x]
      (fun y => thetaCuspSourceTerm y 1*thetaCuspDeepLikelihoodRemainder y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact thetaCuspFullSource_sub_two_eq_first_mul_deep hy
  have hf : ContDiffAt ℝ n thetaCuspFullSource x :=
    contDiff_thetaCuspFullSource.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have ht : ContDiffAt ℝ n thetaCuspTwoAtomSource x :=
    contDiff_thetaCuspTwoAtomSource.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have h1 : ContDiffAt ℝ n (fun y : ℝ => thetaCuspSourceTerm y 1) x :=
    (contDiff_thetaCuspSourceAtom 1).contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hd : ContDiffAt ℝ n thetaCuspDeepLikelihoodRemainder x :=
    (contDiffAt_thetaCuspDeepLikelihoodRemainder hx).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  rw [← iteratedDeriv_fun_sub hf ht, he.iteratedDeriv_eq, iteratedDeriv_fun_mul h1 hd]

/-- Quantitative two-atom approximation through order ten, retaining each exact first-atom jet. -/
theorem abs_thetaCuspFullSource_derivative_sub_two_le {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspFullSource x-iteratedDeriv n thetaCuspTwoAtomSource x| ≤
      thetaCuspDeepTailErrorScale x *
        ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
          |iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x| *
          (16*thetaCuspSingleAtomReflectionScale 1 x)^(n-i) := by
  rw [thetaCuspFullSource_derivative_sub_two_eq n (thetaCusp_pos_of_thirtySevenTenths_le hq),
    Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hn' : n-i ≤ 10 := (Nat.sub_le n i).trans hn
  have hb := abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le hn' hq
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (n.choose i : ℝ)*|iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x| by positivity)
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
  nlinarith only [hm]

end
end RHTower
