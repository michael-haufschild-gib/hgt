import GaloisForLFunctions.RHTower.DeningerArithmeticDenseJets
import GaloisForLFunctions.RHTower.DeningerArithmeticTopologicalCohomology
import GaloisForLFunctions.RHTower.DeningerClosedOperatorPolarization

/-!
# Gelfand-triple completion of Deninger arithmetic cohomology

Deninger's positive Hodge metric is defined on middle cohomology and its completion is the
Hilbert--Pólya space.  The compact-open quotient and its strong dual therefore occur as the
distribution and test boundaries of a Gelfand triple

`H¹_c ⊂ H¹_Hilb ⊂ H¹_ent`,

not as two spaces which the Hodge star must identify directly.

This file formalizes the exact source-comparison interface for that missing Hilbert completion.
The distribution boundary is the already constructed compact-open Xi quotient; the test boundary
is its strong continuous dual.  A completed arithmetic realization must embed both around a
Hilbert middle space, carry Deninger's closed polarized Frobenius generator, and lift every
source-defined Xi eigenclass into its operator domain.

No instance of this structure is postulated.  Lean proves that constructing one is sufficient for
RH, using the source quotient eigenvectors rather than a divisor-defined Hilbert carrier.
-/

open Complex

namespace RHTower

noncomputable section

/-- Chosen source eigenclass supplied by the compact-open divided-chain construction. -/
def deningerCompactOpenThetaEigenvector
    (rho : XiDivisorSupport) :
    DeningerArithmeticCompactOpenH1 :=
  Classical.choose
    (exists_deningerCompactOpenTheta_eigenvector rho)

/-- The chosen compact-open source eigenclass is nonzero. -/
theorem deningerCompactOpenThetaEigenvector_ne_zero
    (rho : XiDivisorSupport) :
    deningerCompactOpenThetaEigenvector rho ≠ 0 :=
  (Classical.choose_spec
    (exists_deningerCompactOpenTheta_eigenvector rho)).1

/-- The chosen source class has the exact Xi Frobenius eigenvalue. -/
theorem deningerCompactOpenThetaEigenvector_eigen
    (rho : XiDivisorSupport) :
    deningerCompactOpenTheta
        (deningerCompactOpenThetaEigenvector rho) =
      (1 / 2 + Complex.I * xiSpectralPointSupport rho) •
        deningerCompactOpenThetaEigenvector rho :=
  (Classical.choose_spec
    (exists_deningerCompactOpenTheta_eigenvector rho)).2

/--
Source-defined Gelfand triple around a Hilbert middle-cohomology completion.

`testToHilbert` has dense range, `hilbertToDistribution` is injective, and the two embeddings
realize the original continuous-dual pairing as the Hilbert pairing.
-/
structure DeningerArithmeticGelfandTriple
    (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  testToHilbert :
    DeningerArithmeticTopologicalH1Compact →L[ℂ] H
  hilbertToDistribution :
    H →L[ℂ] DeningerArithmeticCompactOpenH1
  test_dense : DenseRange testToHilbert
  hilbertToDistribution_injective :
    Function.Injective hilbertToDistribution
  pairing_compatibility :
    ∀ ell x,
      ell (hilbertToDistribution x) =
        @inner ℂ H _ (testToHilbert ell) x

/--
Completed Deninger middle cohomology.

The closed polarized generator is compared to the source distributional Frobenius on its full
domain.  Every source Xi eigenclass is required to have a lift in that domain.  This is the exact
completion/spectral-survival gate: neither positivity nor zero spectrum is inserted by defining
the Hilbert carrier from a divisor.
-/
structure DeningerArithmeticHilbertCohomology
    (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  gelfand : DeningerArithmeticGelfandTriple H
  polarization : DeningerClosedWeightOnePolarization H
  theta_distribution :
    ∀ x : polarization.theta.domain,
      gelfand.hilbertToDistribution (polarization.theta x) =
        deningerCompactOpenTheta
          (gelfand.hilbertToDistribution (x : H))
  sourceEigenvector :
    (rho : XiDivisorSupport) → polarization.theta.domain
  sourceEigenvector_maps :
    ∀ rho,
      gelfand.hilbertToDistribution
          (sourceEigenvector rho : H) =
        deningerCompactOpenThetaEigenvector rho

namespace DeningerArithmeticHilbertCohomology

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Source comparison forces every lifted Xi eigenvector to remain nonzero in Hilbert cohomology. -/
theorem sourceEigenvector_ne_zero
    (R : DeningerArithmeticHilbertCohomology H)
    (rho : XiDivisorSupport) :
    (R.sourceEigenvector rho : H) ≠ 0 := by
  intro hzero
  have hmap := R.sourceEigenvector_maps rho
  rw [hzero, map_zero] at hmap
  exact
    deningerCompactOpenThetaEigenvector_ne_zero rho
      hmap.symm

/-- Intertwining with the source distribution makes every lifted class a genuine Theta eigenvector. -/
theorem sourceEigenvector_eigen
    (R : DeningerArithmeticHilbertCohomology H)
    (rho : XiDivisorSupport) :
    R.polarization.theta (R.sourceEigenvector rho) =
      (1 / 2 + Complex.I * xiSpectralPointSupport rho) •
        (R.sourceEigenvector rho : H) := by
  apply R.gelfand.hilbertToDistribution_injective
  rw [R.theta_distribution,
    R.sourceEigenvector_maps,
    deningerCompactOpenThetaEigenvector_eigen,
    map_smul,
    R.sourceEigenvector_maps]

/-- A source-complete polarized Gelfand realization proves the Riemann hypothesis. -/
theorem riemannHypothesis
    (R : DeningerArithmeticHilbertCohomology H) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hre :
      (1 / 2 + Complex.I *
        xiSpectralPointSupport q.1).re = 1 / 2 :=
    R.polarization.eigenvalue_re_eq_half
      (R.sourceEigenvector_ne_zero q.1)
      (R.sourceEigenvector_eigen q.1)
  have him :
      (xiSpectralPointSupport q.1).im = 0 := by
    norm_num [Complex.mul_re] at hre
    linarith
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · rw [xiSpectralPoint_eq_support]
    simpa using him

end DeningerArithmeticHilbertCohomology

end

end RHTower
