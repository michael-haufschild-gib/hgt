import GaloisForLFunctions.HTGeometry.FAndMRieszHardyCompactness
import GaloisForLFunctions.HTGeometry.HardyProductConvolution
import GaloisForLFunctions.HTGeometry.CircleFourierDensityUniqueness

/-!
# The F. and M. Riesz vanishing-half-line theorem

The analytic Fejer polynomials of the remaining moment half-line have uniformly bounded boundary
`L¹` norm.  Hardy factorization and coefficient compactness produce two square-summable limiting
coefficient arrays.  Their Riesz--Fischer reconstructions give an integrable Hardy product whose
conjugate is the density of the original two-measure difference.  Laurent-moment uniqueness then
proves absolute continuity.
-/

open MeasureTheory Complex Filter Topology Set Polynomial PowerSeries Finset
open scoped Real ENNReal NNReal Nat ComplexConjugate lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem fAndMFejerPolynomial_coeff_zero
    (mu nu : Measure Circle) (f g : Circle → ℂ) (N : ℕ) :
    (fAndMFejerPolynomial mu nu f g N).coeff 0 = 0 := by
  rw [fAndMFejerPolynomial, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hkj : k < j
  · rw [if_pos hkj, Polynomial.coeff_monomial]
    have hne : j - k ≠ 0 := by omega
    simp [hne]
  · simp [hkj]

/-- The compact Hardy factorization can be chosen so that its zeroth convolution coefficient
vanishes, while every positive coefficient is the conjugated remaining moment. -/
theorem exists_hardy_l2_convolution_with_zero_of_equal_analytic_moments
    (mu nu : Measure Circle) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (f g : Circle → ℂ) (hf : Integrable f mu) (hg : Integrable g nu)
    (hvanish : ∀ n : ℕ,
      (∫ w, f w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂mu) =
        ∫ w, g w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂nu) :
    ∃ A B : ℕ → ℂ,
      Memℓp A 2 ∧ Memℓp B 2 ∧ A 0 * B 0 = 0 ∧
      ∀ n, 0 < n →
        (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g n) =
          ∑ i ∈ Finset.range (n + 1), A i * B (n - i) := by
  let C : ℝ := (∫ w, ‖f w‖ ∂mu) + ∫ w, ‖g w‖ ∂nu
  let p : ℕ → ℂ[X] := fun N => fAndMFejerPolynomial mu nu f g N
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpBound : ∀ N, polynomialBoundaryL1 (p N) ≤ C := by
    intro N
    exact polynomialBoundaryL1_fAndMFejerPolynomial_le mu nu f g hf hg hvanish N
  obtain ⟨A, B, subseq, hsubseq, hAmem, hBmem, hAbound, hBbound, hcoeff⟩ :=
    exists_polynomial_hardy_coefficient_limit_factorization p hC hpBound
  refine ⟨A, B, hAmem, hBmem, ?_, ?_⟩
  · have hfinite : Tendsto (fun j => (p (subseq j)).coeff 0) atTop (nhds 0) := by
      simpa only [p, fAndMFejerPolynomial_coeff_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
    have hzero := tendsto_nhds_unique (hcoeff 0) hfinite
    simpa using hzero
  · intro n hn
    have hfinite : Tendsto (fun j => (p (subseq j)).coeff n) atTop
        (nhds ((starRingEnd ℂ) (fAndMRemainingMoment mu nu f g n))) := by
      simpa only [p] using
        (tendsto_fAndMFejerPolynomial_coeff_of_pos mu nu f g n hn).comp
          hsubseq.tendsto_atTop
    exact (tendsto_nhds_unique (hcoeff n) hfinite).symm

private theorem circle_zpow_negSucc_eq_conj_pow (z : Circle) (n : ℕ) :
    (z : ℂ) ^ (Int.negSucc n) = ((starRingEnd ℂ) (z : ℂ)) ^ (n + 1) := by
  rw [zpow_negSucc, ← inv_pow, ← Complex.inv_eq_conj (Circle.norm_coe z)]

/-- The classical F. and M. Riesz vanishing-half-line conclusion for every finite circle measure,
in the exact two-density form required by the Riesz--Fischer reduction. -/
theorem hasFAndMRieszVanishingConclusion_circle
    (mu : Measure Circle) [IsFiniteMeasure mu] :
    HasFAndMRieszVanishingConclusion mu := by
  intro y h hcoeff
  have hyInt : Integrable (⇑y) mu :=
    (Lp.memLp y).integrable (by norm_num)
  have hhInt : Integrable (⇑h) circleLebesgue :=
    (Lp.memLp h).integrable (by norm_num)
  have hvanish : ∀ n : ℕ,
      (∫ w, y w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂mu) =
        ∫ w, h w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂circleLebesgue := by
    intro n
    have hc := hcoeff n
    rw [circleMonomialLp_inner, circleMonomialLp_inner] at hc
    simpa only [map_pow] using hc
  obtain ⟨A, B, hA, hB, hzero, hconv⟩ :=
    exists_hardy_l2_convolution_with_zero_of_equal_analytic_moments
      mu circleLebesgue (⇑y) (⇑h) hyInt hhInt hvanish
  let F : Lp ℂ 2 circleLebesgue := circleRieszFischerOfNat A hA
  let G : Lp ℂ 2 circleLebesgue := circleRieszFischerOfNat B hB
  let prod : Circle → ℂ := fun z => F z * G z
  let q : Circle → ℂ := fun z => (starRingEnd ℂ) (prod z)
  have hprodInt : Integrable prod circleLebesgue := by
    simpa only [prod, F, G] using integrable_hardyProduct A B hA hB
  have hqInt : Integrable q circleLebesgue := by
    exact (@RCLike.conjLIE ℂ _).toContinuousLinearMap.integrable_comp hprodInt
  have hqMoment (k : ℤ) :
      (∫ z, q z * (z : ℂ) ^ k ∂circleLebesgue) =
        (starRingEnd ℂ) (∫ z, prod z *
          (starRingEnd ℂ) ((z : ℂ) ^ k) ∂circleLebesgue) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with z
    simp [q, map_mul]
  have hmoments : ∀ k : ℤ,
      (∫ z, y z * (z : ℂ) ^ k ∂mu) -
          (∫ z, h z * (z : ℂ) ^ k ∂circleLebesgue) =
        ∫ z, q z * (z : ℂ) ^ k ∂circleLebesgue := by
    intro k
    cases k with
    | ofNat n =>
        cases n with
        | zero =>
            have hp0 := hardyProduct_moment_convolution A B hA hB 0
            have hp0' : (∫ z, prod z ∂circleLebesgue) = 0 := by
              calc
                _ = A 0 * B 0 := by
                  simpa only [prod, F, G, pow_zero, map_one, mul_one,
                    Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
                    Nat.zero_sub] using hp0
                _ = 0 := hzero
            have hq0 := hqMoment 0
            simp only [zpow_zero, map_one, mul_one] at hq0
            rw [hp0', map_zero] at hq0
            simp only [Int.ofNat_eq_natCast, zpow_natCast, pow_zero, mul_one]
            rw [hq0]
            exact sub_eq_zero.mpr (by simpa using hvanish 0)
        | succ n =>
            have hp := hardyProduct_moment_convolution A B hA hB (n + 1)
            have hqp := hqMoment (Int.ofNat (n + 1))
            simp only [Int.ofNat_eq_natCast, zpow_natCast] at hqp
            rw [show (∫ z, prod z * (starRingEnd ℂ) ((z : ℂ) ^ (n + 1))
                  ∂circleLebesgue) =
                ∑ i ∈ Finset.range (n + 1 + 1), A i * B (n + 1 - i) by
              simpa only [prod, F, G] using hp] at hqp
            rw [← hconv (n + 1) (by omega)] at hqp
            simp at hqp
            change fAndMRemainingMoment mu circleLebesgue (⇑y) (⇑h) (n + 1) = _
            exact hqp.symm
    | negSucc n =>
        have hleft :
            (∫ z, y z * (z : ℂ) ^ (Int.negSucc n) ∂mu) =
              ∫ z, h z * (z : ℂ) ^ (Int.negSucc n) ∂circleLebesgue := by
          calc
            _ = ∫ z, y z * ((starRingEnd ℂ) (z : ℂ)) ^ (n + 1) ∂mu := by
              apply integral_congr_ae
              filter_upwards with z
              rw [circle_zpow_negSucc_eq_conj_pow]
            _ = ∫ z, h z * ((starRingEnd ℂ) (z : ℂ)) ^ (n + 1)
                ∂circleLebesgue := hvanish (n + 1)
            _ = _ := by
              apply integral_congr_ae
              filter_upwards with z
              rw [circle_zpow_negSucc_eq_conj_pow]
        have hpneg := hardyProduct_moment_eq_zero_of_neg A B hA hB
          (Int.negSucc n) (by simp)
        have hqn := hqMoment (Int.negSucc n)
        rw [show (∫ z, prod z * (starRingEnd ℂ) ((z : ℂ) ^ (Int.negSucc n))
              ∂circleLebesgue) = 0 by
          simpa only [prod, F, G] using hpneg] at hqn
        simp only [map_zero] at hqn
        rw [hleft, sub_self, hqn]
  have hmeasure := withDensityV_complex_sub_eq_of_forall_zpow_integral_eq
    mu circleLebesgue circleLebesgue hyInt hhInt hqInt hmoments
  rw [hmeasure]
  exact withDensityV_absolutelyContinuous_toENNReal circleLebesgue q hqInt

end
end GaloisForLFunctions.HTGeometry
