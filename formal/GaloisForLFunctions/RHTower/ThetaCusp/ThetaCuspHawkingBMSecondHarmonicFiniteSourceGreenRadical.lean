import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicPhysicalHorizonGreenNoncollapseNoGo

/-!
# Finite-source radical of the physical BM horizon Green cut

For the exact regular/complementary Birmingham--Mokhtari horizon basis, every finite source
packet enters the ingoing-minus-outgoing right-endpoint response through one scalar moment against
the unique AdS-normalizable mode.  The connection coefficients give a nonzero universal gain.
Consequently the two physical responses agree exactly on the kernel of that moment.
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Normalizable-mode moment of a finite BM radial source packet. -/
def d4BMPlusPlusFiniteNormalizableSourceMoment
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) : ℂ :=
  ∑ i ∈ S, source i * d4BMPlusPlusAdSNormalizableSolution n chi (point i)

/-- Nonzero scalar converting normalizable source moment into physical horizon-basis Green cut. -/
def d4BMPlusPlusFiniteHorizonBasisGreenMomentGain
    (n : ℕ) (chi : ℂ) : ℂ :=
  (-4 : ℂ) * d4BMPlusPlusComplementaryFrobeniusExponent n chi /
    (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
      d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi)

theorem d4BMPlusPlusFiniteHorizonBasisGreenMomentGain_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusFiniteHorizonBasisGreenMomentGain n chi ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num)
      (d4BMPlusPlusComplementaryFrobeniusExponent_ne_zero n chi hchi)
  · exact mul_ne_zero
      (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_ne_zero n chi hchi)
      (d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient_ne_zero n chi hchi)

/-- Exact source projection is one nonzero BM gain times the normalizable-mode moment. -/
theorem d4BMPlusPlusFiniteHorizonBasisGreenSourceProjection_eq_gain_mul_moment
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    (hpoint : ∀ i ∈ S, 0 < point i ∧ point i < 1) :
    d4BMPlusPlusFiniteHorizonBasisGreenSourceProjection S point source n chi =
      d4BMPlusPlusFiniteHorizonBasisGreenMomentGain n chi *
        d4BMPlusPlusFiniteNormalizableSourceMoment S point source n chi := by
  have hR := d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_ne_zero n chi hchi
  have hC := d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient_ne_zero n chi hchi
  rw [d4BMPlusPlusFiniteHorizonBasisGreenSourceProjection,
    d4BMPlusPlusFiniteHorizonBasisGreenMomentGain,
    d4BMPlusPlusFiniteNormalizableSourceMoment]
  calc
    _ = ∑ i ∈ S,
        (((-4 : ℂ) * d4BMPlusPlusComplementaryFrobeniusExponent n chi /
          (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
            d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi)) *
          (source i * d4BMPlusPlusAdSNormalizableSolution n chi (point i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq_neg_half n chi hchi
          (hpoint i hi).1 (hpoint i hi).2,
        d4BMPlusPlusComplementaryAdSNormalizableGreenDenominator_eq_neg_half n chi hchi
          (hpoint i hi).1 (hpoint i hi).2]
      (field_simp [hR, hC]; ring)
    _ = _ := by rw [Finset.mul_sum]

/-- Physical finite-source Green cut is a nonzero gain times source moment times the unique
normalizable AdS line. -/
theorem d4BMPlusPlusFiniteIngoing_sub_outgoingRightEndpointGreenResponse_eq_gain_mul_moment
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (z : ℝ)
    (hpoint : ∀ i ∈ S, 0 < point i ∧ point i < 1) :
    d4BMPlusPlusFiniteIngoingAdSNormalizableRightEndpointGreenResponse
          S point source n chi z -
        d4BMPlusPlusFiniteOutgoingAdSNormalizableRightEndpointGreenResponse
          S point source n chi z =
      d4BMPlusPlusFiniteHorizonBasisGreenMomentGain n chi *
        d4BMPlusPlusFiniteNormalizableSourceMoment S point source n chi *
          d4BMPlusPlusAdSNormalizableSolution n chi z := by
  rw [d4BMPlusPlusFiniteIngoing_sub_outgoingRightEndpointGreenResponse
      S point source n chi hchi z hpoint,
    d4BMPlusPlusFiniteHorizonBasisGreenSourceProjection_eq_gain_mul_moment
      S point source n chi hchi hpoint]

/-- Complete finite-source dark-space classification for canonical physical BM horizon kernels. -/
theorem d4BMPlusPlusFiniteIngoing_eq_outgoing_iff_normalizableSourceMoment_eq_zero
    {ι : Type*} (S : Finset ι) (point : ι → ℝ) (source : ι → ℂ)
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    (hpoint : ∀ i ∈ S, 0 < point i ∧ point i < 1) :
    (fun z : ℝ => d4BMPlusPlusFiniteIngoingAdSNormalizableRightEndpointGreenResponse
        S point source n chi z) =
      (fun z : ℝ => d4BMPlusPlusFiniteOutgoingAdSNormalizableRightEndpointGreenResponse
        S point source n chi z) ↔
      d4BMPlusPlusFiniteNormalizableSourceMoment S point source n chi = 0 := by
  constructor
  · intro h
    obtain ⟨z, _hz0, _hz1, hzV⟩ :=
      exists_d4BMPlusPlusAdSNormalizableSolution_ne_zero n chi hchi
    have hz := congrFun h z
    have hzero :
        d4BMPlusPlusFiniteIngoingAdSNormalizableRightEndpointGreenResponse
              S point source n chi z -
            d4BMPlusPlusFiniteOutgoingAdSNormalizableRightEndpointGreenResponse
              S point source n chi z = 0 := sub_eq_zero.mpr hz
    rw [d4BMPlusPlusFiniteIngoing_sub_outgoingRightEndpointGreenResponse_eq_gain_mul_moment
      S point source n chi hchi z hpoint] at hzero
    have hgm :
        d4BMPlusPlusFiniteHorizonBasisGreenMomentGain n chi *
          d4BMPlusPlusFiniteNormalizableSourceMoment S point source n chi = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hzV
    exact (mul_eq_zero.mp hgm).resolve_left
      (d4BMPlusPlusFiniteHorizonBasisGreenMomentGain_ne_zero n chi hchi)
  · intro hm
    funext z
    apply sub_eq_zero.mp
    rw [d4BMPlusPlusFiniteIngoing_sub_outgoingRightEndpointGreenResponse_eq_gain_mul_moment
      S point source n chi hchi z hpoint, hm]
    simp

end

end RHTower
