import GaloisForLFunctions.RHTower.CCMPrimePoleJumpBochner
import GaloisForLFunctions.RHTower.CCMPrimePoleSchurKernel

/-!
# The full Weil source in jump-energy coordinates

The exact identity retains the archimedean form norm, the Gamma constant, the
polar cross term, the normalized jump energy and the literal prime row potential.
On polar-constrained states it identifies the precise deficit at a zero of the
source. Existing two-prime rigidity strengthens an exact row comparison to strict
source positivity. That row comparison remains an explicit arithmetic hypothesis.
-/

open Complex MeasureTheory
open scoped InnerProduct
noncomputable section
namespace RHTower

theorem ccmRestrictedWeilSourceQuadratic_eq_jumpEnergy
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    ccmRestrictedWeilSourceQuadratic a u =
      ‖u.1‖ ^ 2 + (2 * gammaHardyPhaseRate 0 - 1) * ‖f‖ ^ 2 +
        (inner ℂ (ccmPolarOperator a f) f).re +
        (∫ x, ccmPrimePoleJumpEnergyDensity a f.1 x) -
        (∫ x, ∑ j ∈ ccmPrimePoleJumpIndices a, ccmPrimePoleJumpRate a j x * ‖f.1 x‖ ^ 2) := by
  dsimp only
  let f := ccmArchimedeanFormToAperture a u
  rw [integral_ccmPrimePoleJumpEnergyDensity, ← ccmPrimePoleRowPotential_eq_jumpRate_integral]
  have he := ccmPrimePoleSchurEnergy_add_prime_eq_rowPotential a f
  have hself : (ccmArchimedeanRemainderScalar * inner ℂ f f).re =
      (2 * gammaHardyPhaseRate 0 - 1) * ‖f‖ ^ 2 := by
    have hff : inner ℂ f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f]
      norm_cast
    unfold ccmArchimedeanRemainderScalar
    rw [hff, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [ccmRestrictedWeilSourceQuadratic_eq_formNorm_sq_add_boundedDiagonal]
  unfold ccmRestrictedWeilBoundedDiagonal
  rw [inner_ccmRestrictedWeilBoundedRemainder, Complex.sub_re, Complex.add_re]
  change ‖u.1‖ ^ 2 + ((ccmArchimedeanRemainderScalar * inner ℂ f f).re +
      (inner ℂ (ccmPolarOperator a f) f).re -
      (inner ℂ (ccmFinitePrimeOperator a f) f).re) = _
  rw [hself]
  linarith

theorem ccmRestrictedWeilSourceQuadratic_eq_jumpEnergy_of_polar
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (hu : IsPolarConstrained a u) :
    let f := ccmArchimedeanFormToAperture a u
    ccmRestrictedWeilSourceQuadratic a u =
      ‖u.1‖ ^ 2 + (2 * gammaHardyPhaseRate 0 - 1) * ‖f‖ ^ 2 +
        (∫ x, ccmPrimePoleJumpEnergyDensity a f.1 x) - ccmPrimePoleRowPotential a f.1 := by
  have he := ccmRestrictedWeilSourceQuadratic_eq_jumpEnergy a u
  dsimp only at he ⊢
  rw [← ccmPrimePoleRowPotential_eq_jumpRate_integral] at he
  have hp : inner ℂ (ccmPolarOperator a (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a u) = 0 := by
    rw [inner_ccmPolarOperator]
    simp only [hu.1, hu.2, mul_zero, add_zero]
  simpa only [hp, Complex.zero_re, add_zero] using he

theorem ccmJumpEnergy_at_zero_source
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (hu : IsPolarConstrained a u) (hzero : ccmRestrictedWeilSourceQuadratic a u = 0) :
    let f := ccmArchimedeanFormToAperture a u
    (∫ x, ccmPrimePoleJumpEnergyDensity a f.1 x) = ccmPrimePoleRowPotential a f.1 -
      ‖u.1‖ ^ 2 - (2 * gammaHardyPhaseRate 0 - 1) * ‖f‖ ^ 2 := by
  have he := ccmRestrictedWeilSourceQuadratic_eq_jumpEnergy_of_polar a u hu
  dsimp only at he ⊢
  linarith

theorem ccmRestrictedWeilSourceQuadratic_pos_of_exact_row_bound
    (a : SuzukiPositiveAperture) (ha : Real.log 2 + Real.log 3 ≤ 2 * a.1)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u)
    (hne : ccmArchimedeanFormToAperture a u ≠ 0)
    (hrow : ccmPrimePoleRowPotential a (ccmArchimedeanFormToAperture a u).1 ≤
      ‖u.1‖ ^ 2 + (2 * gammaHardyPhaseRate 0 - 1) *
        ‖ccmArchimedeanFormToAperture a u‖ ^ 2) :
    0 < ccmRestrictedWeilSourceQuadratic a u := by
  have he := ccmRestrictedWeilSourceQuadratic_eq_jumpEnergy_of_polar a u hu
  dsimp only at he
  rw [integral_ccmPrimePoleJumpEnergyDensity] at he
  have hpos : 0 < ccmPrimePoleSchurEnergy a (ccmArchimedeanFormToAperture a u).1 := by
    apply lt_of_le_of_ne (ccmPrimePoleSchurEnergy_nonneg a _)
    intro hz
    exact hne (eq_zero_of_ccmSchurEnergy_zero_of_polar a ha
      (ccmArchimedeanFormToAperture a u) hu.1 hu.2 hz.symm)
  linarith

end RHTower
