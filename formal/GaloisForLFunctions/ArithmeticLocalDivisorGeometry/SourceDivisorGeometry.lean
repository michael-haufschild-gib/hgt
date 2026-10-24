import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.SourceLocalFactors
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteHeatRootBarrier

/-!
# Exact finite-source divisor geometry

The unnormalized horizontal divisor is monic, even and nonnegative, with degree counting all
retained copies. An off-real copy and its reflection give the sharp Hermite heat obstruction
at their common ordinate, including heights with central zeros.
-/

open Polynomial Complex
open GaloisForLFunctions.HTGeometry RHTower
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- The real divisor polynomial maps to the product over its exact symmetrized copy set. -/
theorem localDivisorPolynomial_map (t : ℝ) (S : Finset XiZeroCopy) :
    (localDivisorPolynomial t S).map (algebraMap ℝ ℂ) =
      ∏ q ∈ sliceTrunc S, (X + C ((xiSpectralPoint q - t) ^ 2)) := by
  apply Polynomial.funext
  intro z
  rw [eval_map, localDivisorPolynomial_eval₂]
  simp only [eval_prod, eval_add, eval_X, eval_C]

/-- Every divisor factor is monic, including the degenerate central factors. -/
theorem localDivisorPolynomial_monic (t : ℝ) (S : Finset XiZeroCopy) :
    (localDivisorPolynomial t S).Monic := by
  have hi : Function.Injective (algebraMap ℝ ℂ) := Complex.ofReal_injective
  have hm : ((localDivisorPolynomial t S).map (algebraMap ℝ ℂ)).Monic := by
    rw [localDivisorPolynomial_map]
    exact monic_prod_of_monic _ _ fun q _ => monic_X_add_C _
  change (localDivisorPolynomial t S).leadingCoeff = 1
  apply hi
  have h := hm.leadingCoeff
  rw [leadingCoeff_map_of_injective hi] at h
  simpa only [map_one] using h

/-- The degree is the exact number of retained copies, with multiplicity. -/
theorem localDivisorPolynomial_degree (t : ℝ) (S : Finset XiZeroCopy) :
    (localDivisorPolynomial t S).natDegree = (sliceTrunc S).card := by
  rw [← (localDivisorPolynomial_monic t S).natDegree_map (algebraMap ℝ ℂ),
    localDivisorPolynomial_map, natDegree_prod_of_monic _ _ (fun q _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, Finset.sum_const, nsmul_eq_mul, mul_one]
  simp

/-- The unnormalized head in horizontal displacement, retaining every central multiplicity. -/
def horizontalDivisorPolynomial (t : ℝ) (S : Finset XiZeroCopy) : ℝ[X] :=
  (localDivisorPolynomial t S).comp (X ^ 2)

theorem horizontalDivisorPolynomial_degree (t : ℝ) (S : Finset XiZeroCopy) :
    (horizontalDivisorPolynomial t S).natDegree = 2 * (sliceTrunc S).card := by
  rw [horizontalDivisorPolynomial, natDegree_comp, localDivisorPolynomial_degree,
    natDegree_pow, natDegree_X]
  omega

theorem horizontalDivisorPolynomial_monic (t : ℝ) (S : Finset XiZeroCopy) :
    (horizontalDivisorPolynomial t S).Monic := by
  exact (localDivisorPolynomial_monic t S).comp (monic_X.pow 2) (by simp)

theorem horizontalDivisorPolynomial_nonneg (t : ℝ) (S : Finset XiZeroCopy) (x : ℝ) :
    0 ≤ (horizontalDivisorPolynomial t S).eval x := by
  rw [horizontalDivisorPolynomial, eval_comp, eval_pow, eval_X]
  exact localDivisorPolynomial_eval_nonneg t S x

theorem horizontalDivisorPolynomial_even (t : ℝ) (S : Finset XiZeroCopy) (x : ℝ) :
    (horizontalDivisorPolynomial t S).eval (-x) = (horizontalDivisorPolynomial t S).eval x := by
  simp only [horizontalDivisorPolynomial, eval_comp, eval_pow, eval_X, neg_sq]

/-- At a retained copy's own ordinate the squared depth is a root of the real divisor. -/
theorem localDivisorPolynomial_own_ordinate_root {S : Finset XiZeroCopy} {q : XiZeroCopy}
    (hq : q ∈ sliceTrunc S) :
    (localDivisorPolynomial (xiSpectralPoint q).re S).eval ((xiSpectralPoint q).im ^ 2) = 0 := by
  apply Complex.ofReal_injective
  change (algebraMap ℝ ℂ) ((localDivisorPolynomial (xiSpectralPoint q).re S).eval
    ((xiSpectralPoint q).im ^ 2)) = (algebraMap ℝ ℂ) 0
  rw [← eval₂_at_apply, localDivisorPolynomial_eval₂, map_zero]
  apply Finset.prod_eq_zero hq
  have hz : xiSpectralPoint q - ((xiSpectralPoint q).re : ℂ) =
      ((xiSpectralPoint q).im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hz, mul_pow, I_sq]
  simp only [Complex.coe_algebraMap]
  push_cast
  ring

private theorem mem_own_radiusHead {q : XiZeroCopy} {R : ℝ}
    (hR : |(xiSpectralPoint q).im| ≤ R) :
    q ∈ xiSliceGaussianRadiusHead (xiSpectralPoint q).re R := by
  rw [mem_xiSliceGaussianRadiusHead]
  have hz : xiSpectralPoint q - ((xiSpectralPoint q).re : ℂ) =
      ((xiSpectralPoint q).im : ℂ) * I := by
    apply Complex.ext <;> simp
  simpa only [hz, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs] using hR

/-- A retained off-real copy brings a distinct reflected copy, without a simplicity premise. -/
theorem two_le_own_radiusHead_card {q : XiZeroCopy} (hq : (xiSpectralPoint q).im ≠ 0)
    {R : ℝ} (hR : |(xiSpectralPoint q).im| ≤ R) :
    2 ≤ (xiSliceGaussianRadiusHead (xiSpectralPoint q).re R).card := by
  have hm := mem_own_radiusHead hR
  have hm' := (mem_radiusHead_lineConj_iff (xiSpectralPoint q).re R q).mpr hm
  have hne : q ≠ xiZeroCopyLineConjEquiv q := by
    intro h
    have hi := congrArg (fun r : XiZeroCopy => (xiSpectralPoint r).im) h
    rw [im_xiSpectralPoint_lineConj] at hi
    exact hq (by linarith only [hi])
  exact Finset.one_lt_card.mpr ⟨q, hm, xiZeroCopyLineConjEquiv q, hm', hne⟩

/-- The exact unnormalized radius head obeys the sharp Hermite heat-root obstruction. -/
theorem radiusHead_depth_sq_le_hermite_edge {q : XiZeroCopy}
    (hq : (xiSpectralPoint q).im ≠ 0) {R lam : ℝ}
    (hR : |(xiSpectralPoint q).im| ≤ R) (hlam : 0 < lam)
    (hc : CoeffNonneg (forwardPolyHeat (lam / 2)
      (horizontalDivisorPolynomial (xiSpectralPoint q).re
        (xiSliceGaussianRadiusHead (xiSpectralPoint q).re R)))) :
    (xiSpectralPoint q).im ^ 2 ≤ lam *
      hermiteEdge (2 * (xiSliceGaussianRadiusHead (xiSpectralPoint q).re R).card - 2) ^ 2 := by
  have hcard := two_le_own_radiusHead_card hq hR
  have hdeg : (horizontalDivisorPolynomial (xiSpectralPoint q).re
      (xiSliceGaussianRadiusHead (xiSpectralPoint q).re R)).natDegree =
      (2 * (xiSliceGaussianRadiusHead (xiSpectralPoint q).re R).card - 2) + 2 := by
    rw [horizontalDivisorPolynomial_degree, sliceTrunc_radiusHead]
    omega
  have hm : q ∈ sliceTrunc (xiSliceGaussianRadiusHead (xiSpectralPoint q).re R) := by
    rw [sliceTrunc_radiusHead]
    exact mem_own_radiusHead hR
  have hz : (horizontalDivisorPolynomial (xiSpectralPoint q).re
      (xiSliceGaussianRadiusHead (xiSpectralPoint q).re R)).eval |(xiSpectralPoint q).im| = 0 := by
    rw [horizontalDivisorPolynomial, eval_comp, eval_pow, eval_X, sq_abs]
    exact localDivisorPolynomial_own_ordinate_root hm
  have hb := nonnegative_root_le_sqrt_mul_hermiteEdge hlam hdeg
    (horizontalDivisorPolynomial_nonneg _ _) hc hz
  have hs := mul_self_le_mul_self (abs_nonneg (xiSpectralPoint q).im) hb
  simpa only [← pow_two, mul_pow, sq_abs, Real.sq_sqrt hlam.le] using hs

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
