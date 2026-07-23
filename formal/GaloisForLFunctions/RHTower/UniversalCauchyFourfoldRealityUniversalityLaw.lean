import GaloisForLFunctions.RHTower.UniversalCauchyQuartetVarianceLaw
import GaloisForLFunctions.RHTower.UniversalCauchyRealKrylovDescentLaw

/-!
# Universal Cauchy fourfold-reality law

For a finite conjugation--negation invariant family away from the imaginary axis, one regular
non-axis Cauchy probe detects the same real form in four languages: real reciprocal-Krylov
recoverability, pointwise spectral reality, vanishing quartet variance, and vanishing total
orientation response.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Universal Cauchy fourfold-reality law.**  On a finite regular family closed under
conjugation and negation, and with no point on the imaginary axis, the exact quartet-variance
decomposition converts real-Krylov descent into a single scalar orientation test. -/
theorem universalCauchy_fourfoldRealityUniversality
    {ι : Type*} [Fintype ι]
    (z : ℂ) (a : ι → ℂ) (conjEquiv negEquiv : ι ≃ ι)
    (hconj : ∀ i, a (conjEquiv i) = (starRingEnd ℂ) (a i))
    (hneg : ∀ i, a (negEquiv i) = -a i)
    (ha : ∀ i, a i ≠ 0)
    (haz : ∀ i, a i - z ≠ 0)
    (hcaz : ∀ i, (starRingEnd ℂ) (a i) - z ≠ 0)
    (hapz : ∀ i, a i + z ≠ 0)
    (hcapz : ∀ i, (starRingEnd ℂ) (a i) + z ≠ 0)
    (hare : ∀ i, (a i).re ≠ 0)
    (hzre : z.re ≠ 0) (hzim : z.im ≠ 0) :
    (∑ i, cauchyQuartetOrientationTerm z (a i)) =
        16 * z.re * z.im * ∑ i, cauchyQuartetVariance z (a i) ∧
      (UniversalCauchyRealKrylovPointwiseRecovery z a ↔
        ∀ i, (a i).im = 0) ∧
      ((∀ i, (a i).im = 0) ↔
        ∀ i, cauchyQuartetVariance z (a i) = 0) ∧
      ((∀ i, cauchyQuartetVariance z (a i) = 0) ↔
        (∑ i, cauchyQuartetOrientationTerm z (a i)) = 0) := by
  have hsum :
      (∑ i, cauchyQuartetOrientationTerm z (a i)) =
        16 * z.re * z.im * ∑ i, cauchyQuartetVariance z (a i) := by
    have hterm : Summable (fun i => cauchyQuartetOrientationTerm z (a i)) := by
      apply summable_of_hasFiniteSupport
      exact Set.finite_univ.subset (Set.subset_univ _)
    have hvariance : Summable (fun i => cauchyQuartetVariance z (a i)) := by
      apply summable_of_hasFiniteSupport
      exact Set.finite_univ.subset (Set.subset_univ _)
    simpa only [tsum_fintype] using
      (tsum_cauchyQuartetOrientationTerm_eq_variance
        z a conjEquiv negEquiv hconj hneg ha haz hcaz hapz hcapz
        hterm hvariance)
  have hrecovery :
      UniversalCauchyRealKrylovPointwiseRecovery z a ↔
        ∀ i, (a i).im = 0 :=
    universalCauchyRealKrylovPointwiseRecovery_iff_all_real
      z a conjEquiv hconj ha haz hzim
  have hrealVariance :
      (∀ i, (a i).im = 0) ↔
        ∀ i, cauchyQuartetVariance z (a i) = 0 := by
    constructor
    · intro hreal i
      exact (cauchyQuartetVariance_eq_zero_iff
        (ha i) (haz i) (hcaz i) (hapz i) (hcapz i)).2 (Or.inr (hreal i))
    · intro hvariance i
      rcases (cauchyQuartetVariance_eq_zero_iff
        (ha i) (haz i) (hcaz i) (hapz i) (hcapz i)).1 (hvariance i) with
        hre | him
      · exact (hare i hre).elim
      · exact him
  have hscalar : (16 * z.re * z.im : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hzre) hzim
  have hvarianceResponse :
      (∀ i, cauchyQuartetVariance z (a i) = 0) ↔
        (∑ i, cauchyQuartetOrientationTerm z (a i)) = 0 := by
    constructor
    · intro hvariance
      rw [hsum]
      simp [hvariance]
    · intro hresponse
      rw [hsum] at hresponse
      have hvarianceSum : (∑ i, cauchyQuartetVariance z (a i)) = 0 :=
        (mul_eq_zero.mp hresponse).resolve_left hscalar
      have hnonneg : ∀ i ∈ Finset.univ,
          0 ≤ cauchyQuartetVariance z (a i) := by
        intro i _
        exact cauchyQuartetVariance_nonneg z (a i)
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hvarianceSum
        i (Finset.mem_univ i)
  exact ⟨hsum, hrecovery, hrealVariance, hvarianceResponse⟩

end

end RHTower
