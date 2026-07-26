import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityFourierBridge
import GaloisForLFunctions.RHTower.XiHedenmalmEigenbasis
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Symmetric source quotients force RH and simple Xi zeros

The canonical Hedenmalm divided chain turns spectral-coordinate multiplication into a Jordan
recurrence. A symmetric operator cannot contain a nontrivial Jordan step at a real eigenvalue.

Consequently, any single inner-product-space quotient which annihilates the common Xi source,
faithfully retains the first divided quotient at every Xi zero, and intertwines coordinate
multiplication on the first two divided levels with a symmetric operator forces every spectral
point to be real and every analytic multiplicity to be one. This is an unconditional carrier
theorem: no positivity, spectral-completeness, or approximation interface is assumed.
-/

open Complex

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A symmetric operator has no nonzero length-two Jordan step at a real spectral value. -/
theorem no_symmetric_jordan_step
    (S : H →ₗ[ℂ] H) (hsym : S.IsSymmetric) (alpha : ℂ)
    (halpha : (starRingEnd ℂ) alpha = alpha) (v0 v1 : H)
    (hv0 : S v0 = alpha • v0)
    (hv1 : S v1 = alpha • v1 + v0) :
    v0 = 0 := by
  have hinnerSym := hsym v1 v0
  rw [hv1, hv0] at hinnerSym
  have hscalar : inner ℂ (alpha • v1) v0 = inner ℂ v1 (alpha • v0) := by
    simp only [inner_smul_left, inner_smul_right, halpha]
  have hinner : inner ℂ v0 v0 = 0 := by
    rw [inner_add_left, hscalar] at hinnerSym
    linear_combination hinnerSym
  exact inner_self_eq_zero.mp hinner

/-- Every nonzero eigenvalue carried by a symmetric complex operator is real. -/
theorem symmetric_eigenvalue_eq_ofReal
    (S : H →ₗ[ℂ] H) (hsym : S.IsSymmetric) (alpha : ℂ) (v : H)
    (hv : S v = alpha • v) (hvne : v ≠ 0) :
    ((alpha.re : ℝ) : ℂ) = alpha := by
  have heig : Module.End.HasEigenvalue (S : Module.End ℂ H) alpha := by
    rw [Module.End.hasEigenvalue_iff]
    intro hbot
    have hmem : v ∈ Module.End.eigenspace (S : Module.End ℂ H) alpha :=
      Module.End.mem_eigenspace_iff.mpr hv
    rw [hbot] at hmem
    exact hvne hmem
  exact RCLike.conj_eq_iff_re.mp (hsym.conj_eigenvalue_eq_self heig)

/-- At one Xi support point, source annihilation, faithful retention of the first divided
quotient, and first-level intertwining already force the centered spectral point to be real. -/
theorem xiSpectralPointSupport_eq_ofReal_of_symmetric_sourceQuotient
    (rho : XiDivisorSupport)
    (J : (ℂ → ℂ) →ₗ[ℂ] H) (S : H →ₗ[ℂ] H)
    (hsym : S.IsSymmetric)
    (hsource : J XiC = 0)
    (hfaithful : J (xiThetaDividedChain (xiSpectralPointSupport rho) 1) ≠ 0)
    (hintertwine_one :
      S (J (xiThetaDividedChain (xiSpectralPointSupport rho) 1)) =
        J (xiCoordinateMultiplication
          (xiThetaDividedChain (xiSpectralPointSupport rho) 1))) :
    (((xiSpectralPointSupport rho).re : ℝ) : ℂ) = xiSpectralPointSupport rho := by
  have hk0 : 0 < xiSupportMultiplicity rho := xiSupportMultiplicity_pos rho
  have hrec0 := xiCoordinateMultiplication_dividedChain rho hk0
  have heigen :
      S (J (xiThetaDividedChain (xiSpectralPointSupport rho) 1)) =
        xiSpectralPointSupport rho •
          J (xiThetaDividedChain (xiSpectralPointSupport rho) 1) := by
    rw [hintertwine_one, hrec0, map_add, map_smul,
      xiThetaDividedChain_zero, hsource, add_zero]
  exact symmetric_eigenvalue_eq_ofReal S hsym (xiSpectralPointSupport rho)
    (J (xiThetaDividedChain (xiSpectralPointSupport rho) 1)) heigen hfaithful

/-- A multiple Xi zero would create a nonzero Jordan step in every faithful symmetric source
quotient, which is impossible. -/
theorem no_symmetric_sourceQuotient_realization_of_multiple_xi_zero
    (rho : XiDivisorSupport) (hm : 2 ≤ xiSupportMultiplicity rho)
    (J : (ℂ → ℂ) →ₗ[ℂ] H) (S : H →ₗ[ℂ] H)
    (hsym : S.IsSymmetric)
    (hsource : J XiC = 0)
    (hfaithful : J (xiThetaDividedChain (xiSpectralPointSupport rho) 1) ≠ 0)
    (hintertwine_one :
      S (J (xiThetaDividedChain (xiSpectralPointSupport rho) 1)) =
        J (xiCoordinateMultiplication
          (xiThetaDividedChain (xiSpectralPointSupport rho) 1)))
    (hintertwine_two :
      S (J (xiThetaDividedChain (xiSpectralPointSupport rho) 2)) =
        J (xiCoordinateMultiplication
          (xiThetaDividedChain (xiSpectralPointSupport rho) 2))) :
    False := by
  have hk0 : 0 < xiSupportMultiplicity rho := xiSupportMultiplicity_pos rho
  have hk1 : 1 < xiSupportMultiplicity rho := by omega
  have hreal := xiSpectralPointSupport_eq_ofReal_of_symmetric_sourceQuotient
    rho J S hsym hsource hfaithful hintertwine_one
  have hrec0 := xiCoordinateMultiplication_dividedChain rho hk0
  have hrec1 := xiCoordinateMultiplication_dividedChain rho hk1
  have hv0 :
      S (J (xiThetaDividedChain (xiSpectralPointSupport rho) 1)) =
        xiSpectralPointSupport rho •
          J (xiThetaDividedChain (xiSpectralPointSupport rho) 1) := by
    rw [hintertwine_one, hrec0, map_add, map_smul,
      xiThetaDividedChain_zero, hsource, add_zero]
  have hv1 :
      S (J (xiThetaDividedChain (xiSpectralPointSupport rho) 2)) =
        xiSpectralPointSupport rho •
          J (xiThetaDividedChain (xiSpectralPointSupport rho) 2) +
            J (xiThetaDividedChain (xiSpectralPointSupport rho) 1) := by
    rw [hintertwine_two, hrec1, map_add, map_smul]
  have hconj : (starRingEnd ℂ) (xiSpectralPointSupport rho) =
      xiSpectralPointSupport rho := by
    exact RCLike.conj_eq_iff_re.mpr hreal
  exact hfaithful (no_symmetric_jordan_step S hsym
    (xiSpectralPointSupport rho) hconj
    (J (xiThetaDividedChain (xiSpectralPointSupport rho) 1))
    (J (xiThetaDividedChain (xiSpectralPointSupport rho) 2)) hv0 hv1)

/-- Positive multiplicity law: every faithful symmetric source quotient carrying the first two
divided levels forces the local Xi multiplicity to be exactly one. -/
theorem xiSupportMultiplicity_eq_one_of_symmetric_sourceQuotient
    (rho : XiDivisorSupport)
    (J : (ℂ → ℂ) →ₗ[ℂ] H) (S : H →ₗ[ℂ] H)
    (hsym : S.IsSymmetric)
    (hsource : J XiC = 0)
    (hfaithful : J (xiThetaDividedChain (xiSpectralPointSupport rho) 1) ≠ 0)
    (hintertwine_one :
      S (J (xiThetaDividedChain (xiSpectralPointSupport rho) 1)) =
        J (xiCoordinateMultiplication
          (xiThetaDividedChain (xiSpectralPointSupport rho) 1)))
    (hintertwine_two :
      2 ≤ xiSupportMultiplicity rho →
        S (J (xiThetaDividedChain (xiSpectralPointSupport rho) 2)) =
          J (xiCoordinateMultiplication
            (xiThetaDividedChain (xiSpectralPointSupport rho) 2))) :
    xiSupportMultiplicity rho = 1 := by
  by_contra hne
  have hm : 2 ≤ xiSupportMultiplicity rho := by
    have hp := xiSupportMultiplicity_pos rho
    omega
  exact no_symmetric_sourceQuotient_realization_of_multiple_xi_zero
    rho hm J S hsym hsource hfaithful hintertwine_one (hintertwine_two hm)

/-- Global carrier theorem. A single faithful symmetric source quotient carrying the first two
canonical divided levels at every Xi zero forces both RH and simplicity. -/
theorem symmetric_xiSourceQuotient_implies_rh_and_simple
    (J : (ℂ → ℂ) →ₗ[ℂ] H) (S : H →ₗ[ℂ] H)
    (hsym : S.IsSymmetric)
    (hsource : J XiC = 0)
    (hfaithful : ∀ rho : XiDivisorSupport,
      J (xiThetaDividedChain (xiSpectralPointSupport rho) 1) ≠ 0)
    (hintertwine_one : ∀ rho : XiDivisorSupport,
      S (J (xiThetaDividedChain (xiSpectralPointSupport rho) 1)) =
        J (xiCoordinateMultiplication
          (xiThetaDividedChain (xiSpectralPointSupport rho) 1)))
    (hintertwine_two : ∀ rho : XiDivisorSupport,
      2 ≤ xiSupportMultiplicity rho →
        S (J (xiThetaDividedChain (xiSpectralPointSupport rho) 2)) =
          J (xiCoordinateMultiplication
            (xiThetaDividedChain (xiSpectralPointSupport rho) 2))) :
    RiemannHypothesis ∧ XiZerosSimple := by
  constructor
  · apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hreal := xiSpectralPointSupport_eq_ofReal_of_symmetric_sourceQuotient
      q.1 J S hsym hsource (hfaithful q.1) (hintertwine_one q.1)
    refine ⟨(xiSpectralPointSupport q.1).re, ?_⟩
    simpa only [xiSpectralPoint_eq_support] using hreal.symm
  · intro alpha halpha
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy alpha).mp halpha
    have hm := xiSupportMultiplicity_eq_one_of_symmetric_sourceQuotient
      q.1 J S hsym hsource (hfaithful q.1)
        (hintertwine_one q.1) (hintertwine_two q.1)
    have hvalue : xiThetaEigenFourier (xiSpectralPointSupport q.1)
        (xiSpectralPointSupport q.1) ≠ 0 :=
      (xiThetaEigenFourier_self_ne_zero_iff_multiplicity_one q.1).mpr hm
    have hderiv : deriv XiC (xiSpectralPointSupport q.1) ≠ 0 := by
      intro hzero
      apply hvalue
      rw [xiThetaEigenFourier_self, hzero, mul_zero]
    have hsupp : xiSpectralPointSupport q.1 = alpha := by
      simpa only [xiSpectralPoint_eq_support] using hq
    simpa only [hsupp] using hderiv

end RHTower
