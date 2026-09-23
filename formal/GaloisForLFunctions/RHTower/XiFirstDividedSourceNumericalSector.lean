import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain
import GaloisForLFunctions.RHTower.XiHedenmalmEigenbasis

/-!
# First-divided-source numerical-sector criterion

This module replaces the evaluated Hedenmalm mode by the first canonical divided source.  The
replacement removes the multiplicity blind spot of the evaluated numerical-sector criterion:
the first divided source exists and can be retained faithfully at every divisor support point,
including a multiple zero.

Let `J` be a linear source quotient.  If `J` kills the common Xi source, the exact divided-chain
recurrence makes the retained first divided source an eigenvector of coordinate multiplication.
Its numerical value therefore has imaginary part

`Im(alpha_rho) * ‖J Q_rho‖ ^ (2 : ℕ)`.

One-sided nonnegativity at both members of each functional-equation reflection pair forces
`Im(alpha_rho) = 0`.  Thus source annihilation, fiberwise faithfulness, and this static numerical
sector imply RH without a global symmetric operator or a simplicity hypothesis.
-/

open Complex

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Static numerical value of coordinate multiplication on the first Hedenmalm divided source
after applying a linear source quotient. -/
def xiFirstDividedSourceNumericalValue
    (J : (ℂ → ℂ) →ₗ[ℂ] H) (rho : XiDivisorSupport) : ℂ :=
  inner ℂ
    (J (xiThetaDividedChain (xiSpectralPointSupport rho) 1))
    (J (xiCoordinateMultiplication
      (xiThetaDividedChain (xiSpectralPointSupport rho) 1)))

/-- One-sided orientation constraint on all first-divided-source numerical values. -/
def XiFirstDividedSourceUpperNumericalSector
    (J : (ℂ → ℂ) →ₗ[ℂ] H) : Prop :=
  ∀ rho : XiDivisorSupport, 0 ≤ (xiFirstDividedSourceNumericalValue J rho).im

/-- After the quotient kills the common Xi source, the first divided source is an exact coordinate
eigenvector. -/
theorem xiFirstDividedSource_coordinate_eq_smul
    (J : (ℂ → ℂ) →ₗ[ℂ] H) (hsource : J XiC = 0)
    (rho : XiDivisorSupport) :
    J (xiCoordinateMultiplication
      (xiThetaDividedChain (xiSpectralPointSupport rho) 1)) =
      xiSpectralPointSupport rho •
        J (xiThetaDividedChain (xiSpectralPointSupport rho) 1) := by
  have hk0 : 0 < xiSupportMultiplicity rho := xiSupportMultiplicity_pos rho
  have hrec := xiCoordinateMultiplication_dividedChain rho hk0
  rw [hrec, map_add, map_smul, xiThetaDividedChain_zero, hsource, add_zero]

/-- Exact imaginary numerical value: centered spectral displacement times a positive norm square. -/
theorem xiFirstDividedSourceNumericalValue_im_eq
    (J : (ℂ → ℂ) →ₗ[ℂ] H) (hsource : J XiC = 0)
    (rho : XiDivisorSupport) :
    (xiFirstDividedSourceNumericalValue J rho).im =
      (xiSpectralPointSupport rho).im *
        ‖J (xiThetaDividedChain (xiSpectralPointSupport rho) 1)‖ ^ (2 : ℕ) := by
  rw [xiFirstDividedSourceNumericalValue,
    xiFirstDividedSource_coordinate_eq_smul J hsource rho,
    inner_smul_right, inner_self_eq_norm_sq_to_K]
  rw [← RCLike.ofReal_pow]
  rw [mul_im]
  simp [pow_two, mul_im, mul_re]

/-- Reflection squeezes a one-sided source numerical sector onto the real centered spectrum. -/
theorem xiSpectralPointSupport_im_eq_zero_of_firstDividedSourceUpperSector
    (J : (ℂ → ℂ) →ₗ[ℂ] H) (hsource : J XiC = 0)
    (hfaithful : ∀ rho : XiDivisorSupport,
      J (xiThetaDividedChain (xiSpectralPointSupport rho) 1) ≠ 0)
    (hupper : XiFirstDividedSourceUpperNumericalSector J)
    (rho : XiDivisorSupport) :
    (xiSpectralPointSupport rho).im = 0 := by
  let rr : XiDivisorSupport := xiZeroReflectEquiv rho
  have hrho := hupper rho
  have href := hupper rr
  rw [xiFirstDividedSourceNumericalValue_im_eq J hsource rho] at hrho
  rw [xiFirstDividedSourceNumericalValue_im_eq J hsource rr,
    xiSpectralPointSupport_reflect rho, neg_im] at href
  have hnrho : 0 < ‖J (xiThetaDividedChain (xiSpectralPointSupport rho) 1)‖ ^ (2 : ℕ) :=
    sq_pos_of_pos (norm_pos_iff.mpr (hfaithful rho))
  have hnref :
      0 < ‖J (xiThetaDividedChain (-xiSpectralPointSupport rho) 1)‖ ^ (2 : ℕ) := by
    simpa only [rr, xiSpectralPointSupport_reflect] using
      sq_pos_of_pos (norm_pos_iff.mpr (hfaithful rr))
  nlinarith

/-- **Static first-divided-source numerical-sector criterion.** A linear source quotient which
annihilates Xi, faithfully retains every first divided quotient, and has one-sided numerical values
on all reflected divisor fibers forces RH. -/
theorem riemannHypothesis_of_firstDividedSourceUpperNumericalSector
    (J : (ℂ → ℂ) →ₗ[ℂ] H) (hsource : J XiC = 0)
    (hfaithful : ∀ rho : XiDivisorSupport,
      J (xiThetaDividedChain (xiSpectralPointSupport rho) 1) ≠ 0)
    (hupper : XiFirstDividedSourceUpperNumericalSector J) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have him := xiSpectralPointSupport_im_eq_zero_of_firstDividedSourceUpperSector
    J hsource hfaithful hupper q.1
  refine ⟨(xiSpectralPointSupport q.1).re, ?_⟩
  rw [xiSpectralPoint_eq_support]
  apply Complex.ext <;> simp [him]

/-- Two regular source points define a static algebraic quotient which compares their evaluations
after Xi normalization. -/
def xiTwoPointSourceQuotient (u v : XiCRegularPoint) :
    (ℂ → ℂ) →ₗ[ℂ] ℂ :=
  XiC v • LinearMap.proj (R := ℂ) (φ := fun _ : ℂ => ℂ) (u : ℂ) -
    XiC u • LinearMap.proj (R := ℂ) (φ := fun _ : ℂ => ℂ) (v : ℂ)

@[simp] theorem xiTwoPointSourceQuotient_apply
    (u v : XiCRegularPoint) (F : ℂ → ℂ) :
    xiTwoPointSourceQuotient u v F = XiC v * F u - XiC u * F v := by
  simp [xiTwoPointSourceQuotient]

/-- Xi vanishes at every support point, without choosing a multiplicity copy externally. -/
theorem XiC_xiSpectralPointSupport_eq_zero (rho : XiDivisorSupport) :
    XiC (xiSpectralPointSupport rho) = 0 := by
  have hpos := xi_divisor_pos_on_support rho
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨rho, ⟨0, hn⟩⟩
  simpa only [q, xiSpectralPoint_eq_support] using XiC_xiSpectralPoint_eq_zero q

/-- Away from the removed point, the first divided chain is the ordinary Xi quotient. -/
theorem xiThetaDividedChain_one_apply_of_ne
    (alpha z : ℂ) (hz : z ≠ alpha) (halpha : XiC alpha = 0) :
    xiThetaDividedChain alpha 1 z = XiC z / (z - alpha) := by
  rw [xiThetaDividedChain]
  simp only [Function.iterate_one]
  change dslope XiC alpha z = _
  rw [dslope_of_ne XiC hz, slope_def_module, halpha, sub_zero]
  simp [div_eq_inv_mul]

/-- The two-point quotient kills the common Xi source identically. -/
theorem xiTwoPointSourceQuotient_XiC (u v : XiCRegularPoint) :
    xiTwoPointSourceQuotient u v XiC = 0 := by
  simp [xiTwoPointSourceQuotient_apply]
  ring

/-- Exact two-point Cauchy value of every first divided Xi source. -/
theorem xiTwoPointSourceQuotient_firstDivided_eq
    (u v : XiCRegularPoint) (rho : XiDivisorSupport) :
    xiTwoPointSourceQuotient u v
      (xiThetaDividedChain (xiSpectralPointSupport rho) 1) =
      XiC u * XiC v * ((v : ℂ) - u) /
        (((u : ℂ) - xiSpectralPointSupport rho) *
          ((v : ℂ) - xiSpectralPointSupport rho)) := by
  have hu : (u : ℂ) ≠ xiSpectralPointSupport rho := by
    intro h
    exact u.property (h ▸ XiC_xiSpectralPointSupport_eq_zero rho)
  have hv : (v : ℂ) ≠ xiSpectralPointSupport rho := by
    intro h
    exact v.property (h ▸ XiC_xiSpectralPointSupport_eq_zero rho)
  rw [xiTwoPointSourceQuotient_apply,
    xiThetaDividedChain_one_apply_of_ne _ _ hu
      (XiC_xiSpectralPointSupport_eq_zero rho),
    xiThetaDividedChain_one_apply_of_ne _ _ hv
      (XiC_xiSpectralPointSupport_eq_zero rho)]
  field_simp [sub_ne_zero.mpr hu, sub_ne_zero.mpr hv]
  ring

/-- Distinct regular source points retain every first divided Xi source, independently of the
zero multiplicity. -/
theorem xiTwoPointSourceQuotient_firstDivided_ne_zero
    (u v : XiCRegularPoint) (huv : (u : ℂ) ≠ v)
    (rho : XiDivisorSupport) :
    xiTwoPointSourceQuotient u v
      (xiThetaDividedChain (xiSpectralPointSupport rho) 1) ≠ 0 := by
  rw [xiTwoPointSourceQuotient_firstDivided_eq]
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero u.property v.property) (sub_ne_zero.mpr huv.symm)
  · apply mul_ne_zero <;> apply sub_ne_zero.mpr
    · intro h
      exact u.property (h ▸ XiC_xiSpectralPointSupport_eq_zero rho)
    · intro h
      exact v.property (h ▸ XiC_xiSpectralPointSupport_eq_zero rho)

/-- **Two-point source-value criterion.** For any two distinct regular source points, the quotient
and faithfulness hypotheses are automatic. Its one-sided first-divided numerical sector alone
forces RH. -/
theorem riemannHypothesis_of_twoPointFirstDividedSourceUpperNumericalSector
    (u v : XiCRegularPoint) (huv : (u : ℂ) ≠ v)
    (hupper : XiFirstDividedSourceUpperNumericalSector
      (xiTwoPointSourceQuotient u v)) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_firstDividedSourceUpperNumericalSector
    (xiTwoPointSourceQuotient u v)
    (xiTwoPointSourceQuotient_XiC u v)
    (xiTwoPointSourceQuotient_firstDivided_ne_zero u v huv)
    hupper

/-- First fixed base point in the absolutely convergent prime-source half-plane. -/
def xiPrimeSourceRegularPointOne : XiCRegularPoint :=
  ⟨-I, XiC_ne_zero_of_one_lt_centered_re (by norm_num [mul_re])⟩

/-- Second fixed base point in the absolutely convergent prime-source half-plane. -/
def xiPrimeSourceRegularPointTwo : XiCRegularPoint :=
  ⟨-2 * I, XiC_ne_zero_of_one_lt_centered_re (by norm_num [mul_re])⟩

theorem xiPrimeSourceRegularPointOne_ne_two :
    (xiPrimeSourceRegularPointOne : ℂ) ≠ xiPrimeSourceRegularPointTwo := by
  simp [xiPrimeSourceRegularPointOne, xiPrimeSourceRegularPointTwo]

/-- **Canonical two-point endpoint.** The quotient, its source-domain points, Xi annihilation, and
fiberwise faithfulness are all unconditional. The only remaining premise is the static upper
numerical-sector law for this fixed prime-source two-point quotient. -/
theorem riemannHypothesis_of_canonicalTwoPointFirstDividedSourceUpperNumericalSector
    (hupper : XiFirstDividedSourceUpperNumericalSector
      (xiTwoPointSourceQuotient
        xiPrimeSourceRegularPointOne xiPrimeSourceRegularPointTwo)) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_twoPointFirstDividedSourceUpperNumericalSector
    xiPrimeSourceRegularPointOne xiPrimeSourceRegularPointTwo
    xiPrimeSourceRegularPointOne_ne_two hupper

end RHTower
