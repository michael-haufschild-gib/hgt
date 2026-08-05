import GaloisForLFunctions.RHTower.RouteRKummerCyclicOneCocycleDetector
import GaloisForLFunctions.RHTower.RouteRPreDivisorRationalCartierSourceFunctor

/-!
# Signed Kummer cyclic Cartier landing for Route R

The degree-one Kummer cocycle is antisymmetric.  Consequently its natural chain receiver is the
signed cyclic quotient by `tau + 1`, not the unsigned quotient by `tau - 1` used by the scalar
product trace.  This module constructs that quotient, includes genuine degree-two Hochschild
boundaries, and proves that the retained ordinary-prime chain survives with regulator
`-log p`.

Multiplication by the first nonzero Xi jet gives a coefficient-faithful source-to-Xi regulator.
Its physical prime-dilation defect is exactly `-log p` times the previously identified central
Bockstein/Cartier defect.  Thus the signed Kummer landing loses neither prime provenance nor the
Xi coefficient and is compatible with genuine Hochschild boundaries.  No vanishing of the
physical defect is assumed or asserted.
-/

open Complex
open GaloisForLFunctions.RHTower
open scoped TensorProduct

namespace RHTower

noncomputable section

/-! ## Signed cyclic and Hochschild boundary quotient -/

/-- Kummer antisymmetry as an equality of linear maps on all degree-one chains. -/
theorem ccmRationalAdelicKummerCyclicOneCocycle_comp_rotate :
    ccmRationalAdelicKummerCyclicOneCocycle.comp
        ccmRationalAdelicDegreeOneCyclicRotation =
      -ccmRationalAdelicKummerCyclicOneCocycle := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearMap.neg_apply]
  change ccmRationalAdelicKummerCyclicOneCocycle
      (cyclicBarRotate (R := ℂ)
        (A := CCMRationalAdelicCyclicSourceAlgebra) 1
        (PiTensorProduct.tprod ℂ x)) = _
  rw [cyclicBarRotate_tprod]
  rw [ccmRationalAdelicKummerCyclicOneCocycle_tprod,
    ccmRationalAdelicKummerCyclicOneCocycle_tprod]
  change ccmRationalAdelicEpsilonZero
      (x 1 * ccmRationalAdelicKummerDerivation (x 0)) =
    -ccmRationalAdelicEpsilonZero
      (x 0 * ccmRationalAdelicKummerDerivation (x 1))
  exact ccmRationalAdelicKummerCyclicOneCocycle_cyclic (x 1) (x 0)

/-- Signed degree-one cyclic relation `tau + 1`. -/
def ccmRationalAdelicDegreeOneSignedCyclicDifference :
    CCMRationalAdelicDegreeOneCyclicSource →ₗ[ℂ]
      CCMRationalAdelicDegreeOneCyclicSource :=
  ccmRationalAdelicDegreeOneCyclicRotation + LinearMap.id

/-- Genuine degree-two arithmetic cyclic tensor source. -/
abbrev CCMRationalAdelicDegreeTwoCyclicSource :=
  CyclicBarTensor ℂ CCMRationalAdelicCyclicSourceAlgebra 2

/-- Alternating degree-two Hochschild boundary `d₀ - d₁ + d₂` on the actual cyclic bar. -/
def ccmRationalAdelicHochschildBoundaryTwo :
    CCMRationalAdelicDegreeTwoCyclicSource →ₗ[ℂ]
      CCMRationalAdelicDegreeOneCyclicSource :=
  (cyclicBarFace (R := ℂ) (A := CCMRationalAdelicCyclicSourceAlgebra)
      (0 : Fin 3) -
    cyclicBarFace (R := ℂ) (A := CCMRationalAdelicCyclicSourceAlgebra)
      (1 : Fin 3)) +
  cyclicBarFace (R := ℂ) (A := CCMRationalAdelicCyclicSourceAlgebra)
    (2 : Fin 3)

/-- The Kummer cocycle annihilates the full linear degree-two Hochschild boundary. -/
theorem ccmRationalAdelicKummerCyclicOneCocycle_comp_boundaryTwo :
    ccmRationalAdelicKummerCyclicOneCocycle.comp
        ccmRationalAdelicHochschildBoundaryTwo = 0 := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    LinearMap.zero_apply]
  simp only [ccmRationalAdelicHochschildBoundaryTwo,
    LinearMap.add_apply, LinearMap.sub_apply, cyclicBarFace_tprod,
    map_add, map_sub]
  rw [ccmRationalAdelicKummerCyclicOneCocycle_tprod,
    ccmRationalAdelicKummerCyclicOneCocycle_tprod,
    ccmRationalAdelicKummerCyclicOneCocycle_tprod]
  change
    ccmRationalAdelicEpsilonZero
          ((x 0 * x 1) * ccmRationalAdelicKummerDerivation (x 2)) -
        ccmRationalAdelicEpsilonZero
          (x 0 * ccmRationalAdelicKummerDerivation (x 1 * x 2)) +
      ccmRationalAdelicEpsilonZero
        ((x 2 * x 0) * ccmRationalAdelicKummerDerivation (x 1)) = 0
  exact ccmRationalAdelicKummerCyclicOneCocycle_boundaryTwoPure
    (x 0) (x 1) (x 2)

/-- Boundary submodule generated jointly by signed cyclic relations and genuine Hochschild
degree-two boundaries. -/
def ccmRationalAdelicDegreeOneSignedKummerBoundary :
    Submodule ℂ CCMRationalAdelicDegreeOneCyclicSource :=
  LinearMap.range ccmRationalAdelicDegreeOneSignedCyclicDifference ⊔
    LinearMap.range ccmRationalAdelicHochschildBoundaryTwo

/-- Every signed cyclic/Hochschild boundary is invisible to the Kummer regulator. -/
theorem ccmRationalAdelicDegreeOneSignedKummerBoundary_le_ker :
    ccmRationalAdelicDegreeOneSignedKummerBoundary ≤
      LinearMap.ker ccmRationalAdelicKummerCyclicOneCocycle := by
  rw [ccmRationalAdelicDegreeOneSignedKummerBoundary, sup_le_iff]
  constructor
  · rintro _ ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [ccmRationalAdelicDegreeOneSignedCyclicDifference,
      LinearMap.add_apply, LinearMap.id_apply, map_add]
    have h := LinearMap.congr_fun
      ccmRationalAdelicKummerCyclicOneCocycle_comp_rotate x
    rw [LinearMap.comp_apply, LinearMap.neg_apply] at h
    rw [h]
    exact neg_add_cancel _
  · rintro _ ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    have h := LinearMap.congr_fun
      ccmRationalAdelicKummerCyclicOneCocycle_comp_boundaryTwo x
    simpa using h

/-- Signed cyclic/Hochschild degree-one chain quotient. -/
abbrev CCMRationalAdelicDegreeOneSignedKummerQuotient :=
  CCMRationalAdelicDegreeOneCyclicSource ⧸
    ccmRationalAdelicDegreeOneSignedKummerBoundary

/-- Canonical projection to the signed Kummer quotient. -/
def ccmRationalAdelicDegreeOneSignedKummerClass :
    CCMRationalAdelicDegreeOneCyclicSource →ₗ[ℂ]
      CCMRationalAdelicDegreeOneSignedKummerQuotient :=
  ccmRationalAdelicDegreeOneSignedKummerBoundary.mkQ

/-- Kummer regulator descended through both source boundary families. -/
def ccmRationalAdelicSignedKummerRegulator :
    CCMRationalAdelicDegreeOneSignedKummerQuotient →ₗ[ℂ] ℂ :=
  ccmRationalAdelicDegreeOneSignedKummerBoundary.liftQ
    ccmRationalAdelicKummerCyclicOneCocycle
    ccmRationalAdelicDegreeOneSignedKummerBoundary_le_ker

@[simp]
theorem ccmRationalAdelicSignedKummerRegulator_mk
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    ccmRationalAdelicSignedKummerRegulator
        (ccmRationalAdelicDegreeOneSignedKummerClass x) =
      ccmRationalAdelicKummerCyclicOneCocycle x := by
  exact Submodule.liftQ_apply _ _ _

/-- Retained ordinary-prime class in the boundary-compatible signed quotient. -/
def ccmRationalAdelicOrdinaryPrimeSignedKummerClass
    (p : Nat.Primes) : CCMRationalAdelicDegreeOneSignedKummerQuotient :=
  ccmRationalAdelicDegreeOneSignedKummerClass
    (ccmRationalAdelicOrdinaryPrimeCycleAtom p)

@[simp]
theorem ccmRationalAdelicSignedKummerRegulator_primeClass
    (p : Nat.Primes) :
    ccmRationalAdelicSignedKummerRegulator
        (ccmRationalAdelicOrdinaryPrimeSignedKummerClass p) =
      -(Real.log (p : ℝ) : ℂ) := by
  rw [ccmRationalAdelicOrdinaryPrimeSignedKummerClass,
    ccmRationalAdelicSignedKummerRegulator_mk,
    ccmRationalAdelicKummerCyclicOneCocycle_primeAtom]

/-- Neither signed cyclic descent nor genuine Hochschild boundaries erase the retained prime. -/
theorem ccmRationalAdelicOrdinaryPrimeSignedKummerClass_ne_zero
    (p : Nat.Primes) :
    ccmRationalAdelicOrdinaryPrimeSignedKummerClass p ≠ 0 := by
  intro hzero
  have hread := congrArg ccmRationalAdelicSignedKummerRegulator hzero
  rw [ccmRationalAdelicSignedKummerRegulator_primeClass, map_zero] at hread
  exact (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
    (Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast p.2.pos) (by exact_mod_cast p.2.ne_one)))) hread

/-! ## Coefficient-faithful Xi landing and physical defect -/

/-- Pre-divisor Xi coefficient paired with the boundary-compatible Kummer regulator. -/
def ccmRationalAdelicPreDivisorSignedKummerCartierCoefficient
    (k : ℕ) (w : ℂ) :
    CCMRationalAdelicDegreeOneSignedKummerQuotient →ₗ[ℂ] ℂ :=
  (iteratedDeriv k XiC w) • ccmRationalAdelicSignedKummerRegulator

@[simp]
theorem ccmRationalAdelicPreDivisorSignedKummerCartierCoefficient_primeClass
    (p : Nat.Primes) (k : ℕ) (w : ℂ) :
    ccmRationalAdelicPreDivisorSignedKummerCartierCoefficient k w
        (ccmRationalAdelicOrdinaryPrimeSignedKummerClass p) =
      -(Real.log (p : ℝ) : ℂ) * iteratedDeriv k XiC w := by
  rw [ccmRationalAdelicPreDivisorSignedKummerCartierCoefficient,
    LinearMap.smul_apply,
    ccmRationalAdelicSignedKummerRegulator_primeClass]
  simp only [smul_eq_mul]
  ring

/-- Boundary-compatible retained-prime landing on the first nonzero Xi jet. -/
def ccmRationalAdelicPrimeXiSignedKummerLanding
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  ccmRationalAdelicPreDivisorSignedKummerCartierCoefficient
    (xiSupportMultiplicity rho) (xiSpectralPointSupport rho)
    (ccmRationalAdelicOrdinaryPrimeSignedKummerClass p)

theorem ccmRationalAdelicPrimeXiSignedKummerLanding_eq
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSignedKummerLanding p rho =
      -(Real.log (p : ℝ) : ℂ) *
        ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  rw [ccmRationalAdelicPrimeXiSignedKummerLanding,
    ccmRationalAdelicPreDivisorSignedKummerCartierCoefficient_primeClass]
  rfl

/-- Prime logarithm and multiplicity-leading Xi coefficient are both retained. -/
theorem ccmRationalAdelicPrimeXiSignedKummerLanding_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSignedKummerLanding p rho ≠ 0 := by
  rw [ccmRationalAdelicPrimeXiSignedKummerLanding_eq]
  exact mul_ne_zero
    (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
      (Real.log_ne_zero_of_pos_of_ne_one
        (by exact_mod_cast p.2.pos) (by exact_mod_cast p.2.ne_one))))
    (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho)

/-- Physical prime-dilation defect measured by the signed Kummer landing. -/
def ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  ccmRationalAdelicPrimeXiSignedKummerLanding p rho -
    (deningerHalfDensityMateGain p (rho : ℂ) : ℂ) *
      ccmRationalAdelicPrimeXiSignedKummerLanding p rho

theorem ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect_eq
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect p rho =
      (1 - (deningerHalfDensityMateGain p (rho : ℂ) : ℂ)) *
        ccmRationalAdelicPrimeXiSignedKummerLanding p rho := by
  rw [ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect]
  ring

/-- The new boundary-compatible defect is exactly the prime-log regulator of the established
central Bockstein/Cartier defect. -/
theorem ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect_eq_log_mul_sourceDefect
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect p rho =
      -(Real.log (p : ℝ) : ℂ) *
        ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho := by
  rw [ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect_eq,
    ccmRationalAdelicPrimeXiSignedKummerLanding_eq,
    ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq]
  ring

/-- Non-erasure reduces vanishing of the physical defect to trivial mate gain. -/
theorem ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect_eq_zero_iff_gain_eq_one
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect p rho = 0 ↔
      deningerHalfDensityMateGain p (rho : ℂ) = 1 := by
  rw [ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect_eq]
  constructor
  · intro hzero
    have hfactor :
        (1 - (deningerHalfDensityMateGain p (rho : ℂ) : ℂ)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right
        (ccmRationalAdelicPrimeXiSignedKummerLanding_ne_zero p rho)
    have hgainComplex :
        (deningerHalfDensityMateGain p (rho : ℂ) : ℂ) = 1 := by
      exact (sub_eq_zero.mp hfactor).symm
    exact_mod_cast hgainComplex
  · intro hgain
    rw [hgain]
    simp

/-- Exact Route-R endpoint exposed by the boundary-compatible signed source. -/
theorem ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect_eq_zero_iff_hodgeMate
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect p rho = 0 ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  rw [ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect_eq_zero_iff_gain_eq_one,
    deningerHalfDensityMateGain_eq_one_iff_re_eq_half p.2.two_le,
    ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half]

/-- Functional-equation reflection preserves the signed Kummer landing up to exact jet parity. -/
theorem ccmRationalAdelicPrimeXiSignedKummerLanding_reflection
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSignedKummerLanding p (xiZeroReflectEquiv rho) =
      (-1 : ℂ) ^ xiSupportMultiplicity rho *
        ccmRationalAdelicPrimeXiSignedKummerLanding p rho := by
  rw [ccmRationalAdelicPrimeXiSignedKummerLanding_eq,
    ccmRationalAdelicPrimeXiSignedKummerLanding_eq,
    ccmRationalAdelicPrimeXiCartierCoefficient_reflection]
  ring

end

end RHTower
