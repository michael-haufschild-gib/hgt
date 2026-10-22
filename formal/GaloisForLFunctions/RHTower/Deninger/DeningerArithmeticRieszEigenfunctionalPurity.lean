import GaloisForLFunctions.RHTower.Deninger.DeningerClosedOperatorPolarization
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Riesz-eigenfunctional purity for Deninger cohomology

Meyer's literal zeta-zero eigenvectors occur in the strong dual of
the nuclear quotient.  A positive Hodge completion constrains such an
eigenfunctional only after it is bounded for the Hodge norm and its
Riesz representative belongs to the closed generator domain.

This file supplies the missing abstract bridge.  The weight-one
adjoint law applied to that Riesz representative forces the
transpose eigencharacter to have real part `1 / 2`.
-/

open Complex

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/--
`DAC_RIESZ_EIGENFUNCTIONAL_HODGE_PURITY`.

If a nonzero vector in the domain of a closed weight-one polarized
generator represents a transpose eigenfunctional with character
`rho`, then `rho` lies on the weight-one line.
-/
theorem deningerClosedWeightOne_rieszEigenfunctional_re_eq_half
    (P : DeningerClosedWeightOnePolarization H)
    {rho : ℂ}
    (y : P.theta.domain)
    (hy : (y : H) ≠ 0)
    (heigen :
      ∀ x : P.theta.domain,
        inner ℂ (y : H) (P.theta x) =
          rho * inner ℂ (y : H) (x : H)) :
    rho.re = 1 / 2 := by
  have hweight := P.theta_inner_sum y y
  have hright := heigen y
  have hleft :
      inner ℂ (P.theta y) (y : H) =
        (starRingEnd ℂ) rho *
          inner ℂ (y : H) (y : H) := by
    rw [← inner_conj_symm, hright, map_mul]
    simp
  rw [hleft, hright] at hweight
  have hmetric0 :
      inner ℂ (y : H) (y : H) ≠ 0 :=
    inner_self_ne_zero.mpr hy
  have hconj :
      (starRingEnd ℂ) rho + rho = 1 := by
    apply mul_right_cancel₀ hmetric0
    linear_combination hweight
  have hre := congrArg Complex.re hconj
  simp only [add_re, conj_re, one_re] at hre
  linarith

/--
One-way Riesz spectral comparison for the closed Hodge generator.

Each nontrivial Xi-divisor point supplies the order-zero transpose
eigenfunctional through a nonzero Riesz vector in the generator
domain.  No zero is used to define the Hilbert space or operator.
-/
structure DeningerClosedWeightOneRieszXiSpectrum
    (P : DeningerClosedWeightOnePolarization H) where
  representative :
    XiDivisorSupport → P.theta.domain
  representative_ne_zero :
    ∀ q : XiDivisorSupport,
      (representative q : H) ≠ 0
  transpose_eigenfunctional :
    ∀ (q : XiDivisorSupport) (x : P.theta.domain),
      inner ℂ (representative q : H) (P.theta x) =
        (1 / 2 + Complex.I * xiSpectralPointSupport q) *
          inner ℂ (representative q : H) (x : H)

/--
A closed weight-one Hodge polarization plus Riesz representation of
every order-zero Meyer/Xi eigenfunctional proves the Riemann
hypothesis.
-/
theorem riemannHypothesis_of_closedWeightOne_rieszXiSpectrum
    (P : DeningerClosedWeightOnePolarization H)
    (Spectrum : DeningerClosedWeightOneRieszXiSpectrum P) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro z hz hzero
  let q : XiDivisorSupport :=
    ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hhalf :
      (1 / 2 + Complex.I * xiSpectralPointSupport q).re = 1 / 2 :=
    deningerClosedWeightOne_rieszEigenfunctional_re_eq_half
      P (Spectrum.representative q)
      (Spectrum.representative_ne_zero q)
      (Spectrum.transpose_eigenfunctional q)
  have hzhalf : z.re = 1 / 2 := by
    dsimp only [q, xiSpectralPointSupport] at hhalf
    norm_num [Complex.mul_re] at hhalf
    linarith
  exact (ne_of_gt (mem_rightHalf.mp hz)) hzhalf

end

end RHTower
