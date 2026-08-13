import GaloisForLFunctions.RHTower.RouteRSignedKummerCyclicCartierLanding
import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Route R physical Bockstein homological non-erasure

The actual physical Bockstein class is the retained signed-Kummer prime class
multiplied by the literal half-density defect and first nonzero Xi jet.  This
module proves that its Kummer regulator is exactly the previously constructed
physical dilation defect.

More strongly, every complex-linear map out of source homology which retains
the prime class also retains this Bockstein class at every off-line fibre.
Thus no linear homological enlargement can supply Route R's missing
annihilation without erasing ordinary-prime provenance.
-/

open Complex

namespace RHTower

noncomputable section

/-- Literal scalar multiplying the retained prime homology class in the
physical central Bockstein. -/
def ccmRationalAdelicPrimeXiPhysicalBocksteinScalar
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  (1 - (deningerHalfDensityMateGain p (rho : ℂ) : ℂ)) *
    ccmRationalAdelicPrimeXiCartierCoefficient rho

/-- Physical central Bockstein class in the genuine signed
cyclic/Hochschild source quotient. -/
def ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicDegreeOneSignedKummerQuotient :=
  ccmRationalAdelicPrimeXiPhysicalBocksteinScalar p rho •
    ccmRationalAdelicOrdinaryPrimeSignedKummerClass p

/-- Literal degree-one chain representative of the physical Bockstein
homology class. -/
def ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicDegreeOneCyclicSource :=
  ccmRationalAdelicPrimeXiPhysicalBocksteinScalar p rho •
    ccmRationalAdelicOrdinaryPrimeCycleAtom p

/-- The quotient class of the literal representative is the physical
Bockstein homology class. -/
theorem ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative_class
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicDegreeOneSignedKummerClass
        (ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative p rho) =
      ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho := by
  rw [ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative,
    ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass, map_smul]
  rfl

/-- The descended Kummer regulator reads exactly the already constructed
signed-Kummer physical dilation defect. -/
theorem ccmRationalAdelicSignedKummerRegulator_physicalBocksteinClass
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicSignedKummerRegulator
        (ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho) =
      ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect p rho := by
  rw [ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass, map_smul,
    ccmRationalAdelicPrimeXiPhysicalBocksteinScalar,
    ccmRationalAdelicSignedKummerRegulator_primeClass,
    ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect_eq,
    ccmRationalAdelicPrimeXiSignedKummerLanding_eq]
  simp only [smul_eq_mul]
  ring

/-- The physical Bockstein homology class vanishes exactly when the literal
half-density character is trivial. -/
theorem ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass_eq_zero_iff_gain_eq_one
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho = 0 ↔
      deningerHalfDensityMateGain p (rho : ℂ) = 1 := by
  constructor
  · intro hzero
    have hscalar :
        ccmRationalAdelicPrimeXiPhysicalBocksteinScalar p rho = 0 :=
      (smul_eq_zero.mp hzero).resolve_right
        (ccmRationalAdelicOrdinaryPrimeSignedKummerClass_ne_zero p)
    rw [ccmRationalAdelicPrimeXiPhysicalBocksteinScalar, mul_eq_zero] at hscalar
    have hfactor :
        1 - (deningerHalfDensityMateGain p (rho : ℂ) : ℂ) = 0 :=
      hscalar.resolve_right
        (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho)
    have hcomplex :
        (deningerHalfDensityMateGain p (rho : ℂ) : ℂ) = 1 :=
      (sub_eq_zero.mp hfactor).symm
    exact_mod_cast hcomplex
  · intro hgain
    simp [ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass,
      ccmRationalAdelicPrimeXiPhysicalBocksteinScalar, hgain]

/-- Pointwise classification in the actual Xi divisor fibre. -/
theorem ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass_eq_zero_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass_eq_zero_iff_gain_eq_one,
    deningerHalfDensityMateGain_eq_one_iff_re_eq_half p.2.two_le]

/-- Null-homology of the explicit Bockstein representative is exactly the
critical-line condition; signed cyclic and Hochschild boundaries do not
annihilate it off line. -/
theorem ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative_mem_boundary_iff
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative p rho ∈
        ccmRationalAdelicDegreeOneSignedKummerBoundary ↔
      (rho : ℂ).re = 1 / 2 := by
  have hmk :
      ccmRationalAdelicDegreeOneSignedKummerClass
          (ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative p rho) = 0 ↔
        ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative p rho ∈
          ccmRationalAdelicDegreeOneSignedKummerBoundary := by
    exact Submodule.Quotient.mk_eq_zero _
  rw [← hmk,
    ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative_class,
    ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass_eq_zero_iff_re_eq_half]

/-- **Target-independent linear non-erasure.**  Every complex-linear map out
of source homology which retains the ordinary-prime class annihilates the
physical Bockstein class exactly at trivial mate gain. -/
theorem ccmRationalAdelicPrimeXiPhysicalBocksteinClass_map_eq_zero_iff_gain_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (F : CCMRationalAdelicDegreeOneSignedKummerQuotient →ₗ[ℂ] V)
    (hretain : F (ccmRationalAdelicOrdinaryPrimeSignedKummerClass p) ≠ 0) :
    F (ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho) = 0 ↔
      deningerHalfDensityMateGain p (rho : ℂ) = 1 := by
  constructor
  · intro hzero
    rw [ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass, map_smul] at hzero
    have hscalar :
        ccmRationalAdelicPrimeXiPhysicalBocksteinScalar p rho = 0 :=
      (smul_eq_zero.mp hzero).resolve_right hretain
    rw [ccmRationalAdelicPrimeXiPhysicalBocksteinScalar, mul_eq_zero] at hscalar
    have hfactor :
        1 - (deningerHalfDensityMateGain p (rho : ℂ) : ℂ) = 0 :=
      hscalar.resolve_right
        (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho)
    have hcomplex :
        (deningerHalfDensityMateGain p (rho : ℂ) : ℂ) = 1 :=
      (sub_eq_zero.mp hfactor).symm
    exact_mod_cast hcomplex
  · intro hgain
    simp [ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass,
      ccmRationalAdelicPrimeXiPhysicalBocksteinScalar, hgain]

/-- Equivalent target-independent classification by divisor grade. -/
theorem ccmRationalAdelicPrimeXiPhysicalBocksteinClass_map_eq_zero_iff_re_eq_half
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (F : CCMRationalAdelicDegreeOneSignedKummerQuotient →ₗ[ℂ] V)
    (hretain : F (ccmRationalAdelicOrdinaryPrimeSignedKummerClass p) ≠ 0) :
    F (ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [ccmRationalAdelicPrimeXiPhysicalBocksteinClass_map_eq_zero_iff_gain_eq_one
      p rho F hretain,
    deningerHalfDensityMateGain_eq_one_iff_re_eq_half p.2.two_le]

/-! ## Quadratic Kunneth non-erasure -/

/-- Ordinary Kunneth self-product of the physical Bockstein homology class. -/
def ccmRationalAdelicPrimeXiPhysicalBocksteinTensorSquare
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    TensorProduct ℂ CCMRationalAdelicDegreeOneSignedKummerQuotient
      CCMRationalAdelicDegreeOneSignedKummerQuotient :=
  ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho ⊗ₜ[ℂ]
    ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho

/-- Tensor-square Kummer readout followed by the canonical multiplication
`ℂ ⊗[ℂ] ℂ ≃ ℂ`. -/
def ccmRationalAdelicSignedKummerTensorSquareRegulator :
    TensorProduct ℂ CCMRationalAdelicDegreeOneSignedKummerQuotient
        CCMRationalAdelicDegreeOneSignedKummerQuotient →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map ccmRationalAdelicSignedKummerRegulator
      ccmRationalAdelicSignedKummerRegulator)

/-- The tensor-square regulator is the square of the literal physical
dilation defect. -/
theorem ccmRationalAdelicSignedKummerTensorSquareRegulator_bockstein
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicSignedKummerTensorSquareRegulator
        (ccmRationalAdelicPrimeXiPhysicalBocksteinTensorSquare p rho) =
      ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect p rho ^ 2 := by
  rw [ccmRationalAdelicSignedKummerTensorSquareRegulator,
    ccmRationalAdelicPrimeXiPhysicalBocksteinTensorSquare,
    LinearMap.comp_apply, TensorProduct.map_tmul]
  change
    ccmRationalAdelicSignedKummerRegulator
          (ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho) *
        ccmRationalAdelicSignedKummerRegulator
          (ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho) = _
  rw [ccmRationalAdelicSignedKummerRegulator_physicalBocksteinClass]
  ring

/-- **Quadratic homological no-go.**  The ordinary Kunneth self-product of
the retained physical Bockstein class vanishes exactly on the critical
fibre.  It is therefore not an independently source-exact relative-index
class off line. -/
theorem ccmRationalAdelicPrimeXiPhysicalBocksteinTensorSquare_eq_zero_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPhysicalBocksteinTensorSquare p rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    have hread := congrArg ccmRationalAdelicSignedKummerTensorSquareRegulator hzero
    rw [ccmRationalAdelicSignedKummerTensorSquareRegulator_bockstein,
      map_zero] at hread
    have hdefect :
        ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect p rho = 0 := by
      simpa using hread
    have hgain :=
      (ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect_eq_zero_iff_gain_eq_one
        p rho).mp hdefect
    exact (deningerHalfDensityMateGain_eq_one_iff_re_eq_half
      p.2.two_le (rho : ℂ)).mp hgain
  · intro hline
    have hclass :
        ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho = 0 :=
      (ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass_eq_zero_iff_re_eq_half
        p rho).mpr hline
    simp [ccmRationalAdelicPrimeXiPhysicalBocksteinTensorSquare, hclass]

/-! ## All finite Kunneth powers -/

/-- The `n`-fold ordinary Kunneth power of the physical Bockstein class. -/
def ccmRationalAdelicPrimeXiPhysicalBocksteinTensorPower
    (p : Nat.Primes) (rho : XiDivisorSupport) (n : ℕ) :
    TensorPower ℂ n CCMRationalAdelicDegreeOneSignedKummerQuotient :=
  PiTensorProduct.tprod ℂ
    (fun _ : Fin n =>
      ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho)

/-- Product regulator on the `n`-fold signed-Kummer tensor power. -/
def ccmRationalAdelicSignedKummerTensorPowerRegulator
    (n : ℕ) :
    TensorPower ℂ n CCMRationalAdelicDegreeOneSignedKummerQuotient →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebraFin ℂ n ℂ).compLinearMap
      (fun _ : Fin n => ccmRationalAdelicSignedKummerRegulator))

/-- Product regulator reads the corresponding power of the literal physical
dilation defect.  This includes degree zero, where both sides are one. -/
theorem ccmRationalAdelicSignedKummerTensorPowerRegulator_bockstein
    (p : Nat.Primes) (rho : XiDivisorSupport) (n : ℕ) :
    ccmRationalAdelicSignedKummerTensorPowerRegulator n
        (ccmRationalAdelicPrimeXiPhysicalBocksteinTensorPower p rho n) =
      ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect p rho ^ n := by
  rw [ccmRationalAdelicSignedKummerTensorPowerRegulator,
    ccmRationalAdelicPrimeXiPhysicalBocksteinTensorPower,
    PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply]
  simp_rw [ccmRationalAdelicSignedKummerRegulator_physicalBocksteinClass]
  exact MultilinearMap.mkPiAlgebraFin_apply_const _

/-- Every finite Kunneth power is regulator-visible at an off-line fibre.
The statement deliberately includes degree zero: its tensor unit cannot
vanish either. -/
theorem ccmRationalAdelicPrimeXiPhysicalBocksteinTensorPower_ne_zero_of_offLine
    (p : Nat.Primes) (rho : XiDivisorSupport) (n : ℕ)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ccmRationalAdelicPrimeXiPhysicalBocksteinTensorPower p rho n ≠ 0 := by
  intro hzero
  have hread := congrArg
    (ccmRationalAdelicSignedKummerTensorPowerRegulator n) hzero
  rw [ccmRationalAdelicSignedKummerTensorPowerRegulator_bockstein,
    map_zero] at hread
  have hdefect :
      ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect p rho = 0 :=
    eq_zero_of_pow_eq_zero hread
  have hgain :=
    (ccmRationalAdelicPrimeXiSignedKummerPhysicalDefect_eq_zero_iff_gain_eq_one
      p rho).mp hdefect
  exact hoff ((deningerHalfDensityMateGain_eq_one_iff_re_eq_half
    p.2.two_le (rho : ℂ)).mp hgain)

/-- **Finite Kunneth-power classification.**  For every positive degree, the
ordinary power of the retained physical Bockstein class is null exactly on
the critical fibre.  Hence passage to any finite ordinary Kunneth degree
cannot create the missing source annihilation. -/
theorem ccmRationalAdelicPrimeXiPhysicalBocksteinTensorPower_eq_zero_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) (n : ℕ) (hn : 0 < n) :
    ccmRationalAdelicPrimeXiPhysicalBocksteinTensorPower p rho n = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    by_contra hoff
    exact ccmRationalAdelicPrimeXiPhysicalBocksteinTensorPower_ne_zero_of_offLine
      p rho n hoff hzero
  · intro hline
    have hclass :
        ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass p rho = 0 :=
      (ccmRationalAdelicPrimeXiPhysicalBocksteinHomologyClass_eq_zero_iff_re_eq_half
        p rho).mpr hline
    let i : Fin n := ⟨0, hn⟩
    rw [ccmRationalAdelicPrimeXiPhysicalBocksteinTensorPower,
      PiTensorProduct.tprod_eq_tprodCoeff_one]
    exact PiTensorProduct.zero_tprodCoeff' 1 _ i hclass

/-- Proposed coefficient-faithful finite algebraic source annihilator.  Its
coefficient is required to be nonzero, so the interface cannot declare
success by erasing the retained Kunneth monomial. -/
structure RouteRFiniteKunnethPhysicalBocksteinAnnihilator where
  prime : Nat.Primes
  divisor : XiDivisorSupport
  degree : ℕ
  degree_pos : 0 < degree
  coefficient : ℂ
  coefficient_ne_zero : coefficient ≠ 0
  offLine : (divisor : ℂ).re ≠ 1 / 2
  source_exact :
    coefficient •
      ccmRationalAdelicPrimeXiPhysicalBocksteinTensorPower
        prime divisor degree = 0

/-- **Finite algebraic homological producer no-go.**  No nonzero scalar
multiple of a positive Kunneth power can be source-exact at an off-line
physical fibre.  Any surviving source relation must therefore be genuinely
non-Kunneth (or erase the retained coefficient). -/
theorem routeR_no_finiteKunnethPhysicalBocksteinAnnihilator :
    ¬ Nonempty RouteRFiniteKunnethPhysicalBocksteinAnnihilator := by
  rintro ⟨P⟩
  exact (smul_ne_zero P.coefficient_ne_zero
    (ccmRationalAdelicPrimeXiPhysicalBocksteinTensorPower_ne_zero_of_offLine
      P.prime P.divisor P.degree P.offLine)) P.source_exact

/-- At an off-line fibre the physical Bockstein class is not a signed
cyclic/Hochschild boundary. -/
theorem ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative_not_mem_boundary_of_offLine
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative p rho ∉
      ccmRationalAdelicDegreeOneSignedKummerBoundary := by
  exact (ccmRationalAdelicPrimeXiPhysicalBocksteinRepresentative_mem_boundary_iff
    p rho).not.mpr hoff

end

end RHTower
