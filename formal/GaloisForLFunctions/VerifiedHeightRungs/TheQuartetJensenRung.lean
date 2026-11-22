import GaloisForLFunctions.FiniteFreeProbability.JensenSectorOfASymmetricQuartet
import GaloisForLFunctions.VerifiedHeightRungs.WeightedJensenRoots
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightEightyFour
import GaloisForLFunctions.RHTower.XiGaussianHeatTestPolynomialBasis
import GaloisForLFunctions.HTGeometry.HeatEscapeNonreal

/-!
# The verified Jensen rung from whole symmetric quartets and the Bohman height

Contracting the real even Hadamard polynomials of Xi to the squared coordinate
applies the quartet sector to every orbit (`31930` at height `67`); Bohman
height `169/2` (`84.5`) advances the verified Jensen rung to degree `50787`.
-/

open Polynomial Finset Filter Topology Complex RHTower RHTower.DeBruijn FiniteFreeProbability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.VerifiedHeightRungs

noncomputable section

private theorem approx_even (n : ℕ) : (xiRealApprox n).comp (-X) = xiRealApprox n := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  rw [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X, map_xiRealApprox]
  apply Polynomial.funext
  intro z
  simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C, eval_xiZeroPoly]
  apply congrArg ((XiC 0)*·)
  let S := xiPairedCopyFinset (xiConjClosedFinset n)
  calc
    _ = ∏ q ∈ S, (1-z/xiSpectralPoint (xiZeroCopyReflectEquiv q)) := by
      apply prod_congr rfl
      intro q _
      rw [xiSpectralPoint_reflect, div_neg, neg_div]
    _ = ∏ q ∈ S.image xiZeroCopyReflectEquiv, (1-z/xiSpectralPoint q) :=
      (prod_image (s := S) (f := fun q => 1-z/xiSpectralPoint q)
        xiZeroCopyReflectEquiv.injective.injOn).symm
    _ = _ := by rw [xiPairedCopyFinset_image_reflect]

private theorem recover_even (n : ℕ) :
    expand ℝ 2 (contract 2 (xiRealApprox n)) = xiRealApprox n := by
  ext j
  rw [coeff_expand (by decide : 0 < 2)]
  by_cases hj : 2 ∣ j
  · rw [if_pos hj, coeff_contract (by decide : 2 ≠ 0)]
    congr 1
    omega
  · rw [if_neg hj]
    exact (coeff_odd_eq_zero_of_even (approx_even n) (Nat.not_even_iff_odd.mp
      (by simpa only [even_iff_two_dvd] using hj))).symm

private theorem approx_root (n : ℕ) {z : ℂ} (hz : aeval z (xiRealApprox n) = 0) :
    ∃ q : XiZeroCopy, z = xiSpectralPoint q := by
  rw [← eval_map_algebraMap] at hz
  change ((xiRealApprox n).map Complex.ofRealHom).eval z = 0 at hz
  rw [map_xiRealApprox, eval_mul, eval_C, eval_xiZeroPoly, mul_eq_zero] at hz
  obtain ⟨q,-,hq⟩ := prod_eq_zero_iff.mp (hz.resolve_left RHTower.XiC_zero_ne_zero)
  exact ⟨q,(div_eq_one_iff_eq (xiSpectralPoint_ne_zero q)).mp (sub_eq_zero.mp hq).symm⟩

/-- The square-coordinate Jensen condition transfers through the full Hadamard
exhaustion of Xi. Its real-axis pairs are included in the same exhaustion. -/
theorem jensenNonrealCount_eq_zero_of_quartet_sector (k : ℕ)
    (hs : ∀ q : XiZeroCopy, InSquaredJensenSector (k+4) (xiSpectralPoint q ^ 2)) :
    jensenNonrealCount (k+4) = 0 := by
  let d := k+4
  let P (n : ℕ) := diffOp (xiRealApprox n) (X^d)
  have hsplit (n : ℕ) : (P n).Splits := by
    change (diffOp (xiRealApprox n) (X^(k+4))).Splits
    rw [← recover_even n]
    apply splits_diffOp_expand_two_of_squared_sector
    · simpa only [coeff_contract (by decide : 2 ≠ 0), zero_mul, mul_zero, coeff_zero_eq_eval_zero]
        using eval_zero_xiRealApprox n
    · intro w hw
      obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq w zero_lt_two
      have hroot : aeval z (xiRealApprox n) = 0 := by
        rw [← recover_even n, expand_eq_comp_X_pow, aeval_comp, map_pow, aeval_X]
        exact hw
      obtain ⟨q,rfl⟩ := approx_root n hroot
      exact hs q
  have hdeg (n : ℕ) : (P n).natDegree ≤ d := (natDegree_diffOp_le _ _).trans (natDegree_X_pow_le d)
  have hcoeff (j : ℕ) : Tendsto (fun n => (P n).coeff j) atTop (𝓝 ((xiJensenReal d).coeff j)) := by
    by_cases hj : j ≤ d
    · simp only [P, xiJensenReal_eq, jensenRev, coeff_diffOp_X_pow _ hj, PowerSeries.coeff_trunc,
        if_pos (by omega : d-j < d+1), PowerSeries.coeff_mk]
      have hr := (Complex.continuous_re.tendsto _).comp (tendsto_coeff_xiRealApprox (d-j))
      simp only [Function.comp_def, Complex.ofReal_re] at hr
      exact hr.mul_const _
    · simp only [coeff_eq_zero_of_natDegree_lt ((hdeg _).trans_lt (lt_of_not_ge hj)),
        coeff_eq_zero_of_natDegree_lt (by rw [natDegree_xiJensenReal]; omega : (xiJensenReal d).natDegree < j)]
      exact tendsto_const_nhds
  have hreal : (xiJensenReal d).Splits := by
    by_contra hn
    have hbad := _root_.HTGeometry.eventually_not_splits_of_coeff_limit hdeg
      (natDegree_xiJensenReal d).le (xiJensenReal_ne_zero d) hcoeff hn
    obtain ⟨n,h⟩ := hbad.exists
    exact h (hsplit n)
  rw [jensenNonrealCount_eq]
  exact Nat.sub_eq_zero_of_le hreal.natDegree_eq_card_roots.le

private theorem quartet_at_verified_height (q : XiZeroCopy) :
    InSquaredJensenSector 31930 (xiSpectralPoint q^2) := by
  let z := xiSpectralPoint q
  rw [squaredJensenSector_square]
  change z.im^2 < z.re^2 ∧ ((31930 : ℝ)-2)*(31930-3)*(z.re^2+z.im^2)^2 ≤
    31930*(31930-1)*(z.re^2-z.im^2)^2
  by_cases hv : |z.re| ≤ 67
  · have hi : z.im = 0 := im_xiSpectralPoint_eq_zero HadamardBudget.rhVerifiedThrough_sixtySeven q hv
    have hx : z.re ≠ 0 := fun he => xiSpectralPoint_ne_zero q (Complex.ext he hi)
    constructor
    · simpa only [hi, zero_pow (by decide : 2 ≠ 0)] using sq_pos_of_ne_zero hx
    · rw [hi]
      nlinarith only [sq_nonneg (z.re^2)]
  · have hi : |z.im| ≤ 8999/24000 := by
      change |(xiSpectralPoint q).im| ≤ _
      rw [im_xiSpectralPoint, abs_sub_comm]
      exact (BiScaleUncertainty.ChebyshevGauge.zetaZeroWidth_le_iff_xiZeroCopy_abs_re_sub_half_le
        (by norm_num)).mp zetaZeroWidth_le_8999_div_24000 q
    have hy : z.im^2 ≤ (8999/24000 : ℝ)^2 := by
      rw [← sq_abs z.im]
      exact pow_le_pow_left₀ (abs_nonneg _) hi 2
    have hx : (67 : ℝ)^2 ≤ z.re^2 := by
      rw [← sq_abs z.re]
      exact pow_le_pow_left₀ (by norm_num) (le_of_not_ge hv) 2
    refine ⟨by linarith only [hx,hy], ?_⟩
    change ((31930 : ℝ)-2)*(31930-3)*(z.re^2+z.im^2)^2 ≤
      31930*(31930-1)*(z.re^2-z.im^2)^2
    have hlin : 4*(31930^2-3*31930+3)*z.im^2 ≤ (4*31930-6)*z.re^2 := by
      linarith only [hx,hy]
    nlinarith only [mul_le_mul_of_nonneg_right hlin (sq_nonneg z.re), sq_nonneg (z.im^2)]

/-- The whole quartet certifies the next unshifted Xi Jensen degree beyond the conjugate-pair test. -/
theorem jensenNonrealCount_eq_zero_through_31930 (d : Fin 31931) : jensenNonrealCount d.val = 0 := by
  by_cases hd : d.val ≤ 31929
  · exact jensenNonrealCount_eq_zero_through_31929 ⟨d.val,by omega⟩
  · rw [show d.val = 31930 by omega]
    exact jensenNonrealCount_eq_zero_of_quartet_sector 31926 quartet_at_verified_height

/-- No higher universal rung follows from the same width and height even among
real even symbols. One quartet beyond the verified height fails in every higher degree. -/
theorem quartet_above_verified_height_fails_every_higher_degree :
    ∃ z : ℂ, 67 < z.re ∧ 0 < z.im ∧ z.im < 8999/24000 ∧
      ∀ n : ℕ, ¬ (diffOp (squaredPairSymbol (z^2)) (X^(31931+n))).Splits := by
  let z : ℂ := ⟨67+1/1000000, 8999/24000-1/100000000⟩
  refine ⟨z, by norm_num [z], by norm_num [z], by norm_num [z], ?_⟩
  intro n h
  have h0 : z^2 ≠ 0 := pow_ne_zero _ (fun he => by
    have := congrArg Complex.re he
    norm_num [z] at this)
  have hs := (squaredPairSymbol_splits_iff (31927+n) h0).mp
    (by simpa only [show 31927+n+4 = 31931+n by omega] using h)
  have hh := ((squaredJensenSector_square _ z).mp hs).2
  push_cast at hh
  change ((31927+(n : ℝ)+4)-2)*((31927+n+4)-3)*
      ((67+1/1000000)^2+(8999/24000-1/100000000)^2)^2 ≤
    (31927+n+4)*(31927+n+4-1)*((67+1/1000000)^2-(8999/24000-1/100000000)^2)^2 at hh
  nlinarith only [hh, Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]

/-! ## Bohman height `169/2` (`84.5`) upgrades the Jensen rung to degree `50787` -/

/-- Exact largest degree paid by width `8999/24000` at Bohman verified height `169/2`. -/
theorem jensen_sector_at_oneHundredSixtyNine_halves_iff (d : ℕ) :
    ((d : ℝ) - 1) * (8999 / 24000 : ℝ) ^ 2 ≤ (169 / 2) ^ 2 ↔ d ≤ 50787 := by
  constructor
  · intro h
    by_contra! hd
    have hn : 50788 ≤ d := by omega
    have h' : (50788 : ℝ) ≤ d := by exact_mod_cast hn
    linarith
  · intro h
    have h' : (d : ℝ) ≤ 50787 := by exact_mod_cast h
    linarith

/-- The unshifted Xi Jensen polynomial has only real zeros through degree `50787`. -/
theorem jensenNonrealCount_eq_zero_through_50787 (d : Fin 50788) :
    jensenNonrealCount d.val = 0 := by
  apply jensenNonrealCount_eq_zero_of_rhVerifiedThrough_width (T := 169 / 2) (by norm_num)
    HadamardBudget.rhVerifiedThrough_oneHundredSixtyNine_halves
  have h := (jensen_sector_at_oneHundredSixtyNine_halves_iff d).2 (by omega)
  rcases le_or_gt ((d.val : ℝ) - 1) 0 with hd | hd
  · exact (mul_nonpos_of_nonpos_of_nonneg hd (sq_nonneg _)).trans (sq_nonneg _)
  · exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ zetaZeroWidth_nonneg zetaZeroWidth_le_8999_div_24000 2) hd.le).trans h

/-- All positive-integer Euler weights preserve real-rootedness through degree `50787`. -/
theorem weightedXiJensen_splits_through_50787 (w : List ℕ) (d : Fin 50788) :
    (eulerWord w (xiJensenReal d.val)).Splits := by
  have h := weightedXiJensen_nonreal_le w d
  rw [jensenNonrealCount_eq_zero_through_50787 d, nonrealRootCount] at h
  have hc := Polynomial.card_roots' (eulerWord w (xiJensenReal d))
  rw [splits_iff_card_roots]
  omega

/-- Sharpness at Bohman height `169/2` and width `8999/24000`: one symmetric quartet just above
`169/2` fails to split in every degree `50788 + n`. -/
theorem quartet_above_bohman_height_fails_every_higher_degree :
    ∃ z : ℂ, 169 / 2 < z.re ∧ 0 < z.im ∧ z.im < 8999 / 24000 ∧
      ∀ n : ℕ, ¬ (diffOp (squaredPairSymbol (z ^ 2)) (X ^ (50788 + n))).Splits := by
  let z : ℂ := ⟨169 / 2 + 1 / 1000000, 8999 / 24000 - 1 / 100000000⟩
  refine ⟨z, by norm_num [z], by norm_num [z], by norm_num [z], ?_⟩
  intro n h
  have h0 : z ^ 2 ≠ 0 := pow_ne_zero _ (fun he => by
    have := congrArg Complex.re he
    norm_num [z] at this)
  have hs := (squaredPairSymbol_splits_iff (50784 + n) h0).mp
    (by simpa only [show 50784 + n + 4 = 50788 + n by omega] using h)
  have hh := ((squaredJensenSector_square _ z).mp hs).2
  push_cast at hh
  change ((50784 + (n : ℝ) + 4) - 2) * ((50784 + n + 4) - 3) *
      ((169 / 2 + 1 / 1000000) ^ 2 + (8999 / 24000 - 1 / 100000000) ^ 2) ^ 2 ≤
    (50784 + n + 4) * (50784 + n + 4 - 1) *
      ((169 / 2 + 1 / 1000000) ^ 2 - (8999 / 24000 - 1 / 100000000) ^ 2) ^ 2 at hh
  nlinarith only [hh, Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]

#print axioms jensenNonrealCount_eq_zero_through_50787
#print axioms weightedXiJensen_splits_through_50787
#print axioms quartet_above_bohman_height_fails_every_higher_degree

end

end GaloisForLFunctions.VerifiedHeightRungs
