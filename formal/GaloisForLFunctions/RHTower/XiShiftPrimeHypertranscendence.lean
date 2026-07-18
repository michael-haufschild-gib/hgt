import GaloisForLFunctions.HTGeometry.PrimeValuationLeadingEchelon
import GaloisForLFunctions.HTGeometry.PrimeClockAnalyticEulerCompletion
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure

/-!
# Hypertranscendence of the prime source exposed by the xi shift defect

The `+2` shift of `xi'/xi`, after its explicit rational correction, exposes the Dirichlet source
`Lambda(n) (1 - n^(-2))`.  Its prime coefficient is nonzero at every prime, so the
prime-dependent leading-echelon law makes the formal arithmetic source differentially
independent.  The finite-abscissa transfer then proves hypertranscendence of its actual upper-end
meromorphic carrier over the genuine rational coordinate field.
-/

namespace RHTower

open ArithmeticFunction Filter Set
open scoped Differential LSeries.notation

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiShiftPrimeUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiShiftPrimeUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiShiftPrimeUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- The filtered von Mangoldt coefficient stream as an arithmetic function. -/
def filteredVonMangoldtArithmetic : ArithmeticFunction ℂ where
  toFun := filteredVonMangoldtCoeff
  map_zero' := by simp [filteredVonMangoldtCoeff]

@[simp]
theorem filteredVonMangoldtArithmetic_apply (n : ℕ) :
    filteredVonMangoldtArithmetic n = filteredVonMangoldtCoeff n :=
  rfl

/-- The filtered von Mangoldt source has finite abscissa of absolute convergence. -/
def filteredVonMangoldtFiniteAbscissaSource :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨filteredVonMangoldtArithmetic, 1, ?_⟩
  intro y hy
  exact LSeriesSummable_filteredVonMangoldtCoeff (by simpa using hy)

@[simp]
theorem filteredVonMangoldtFiniteAbscissaSource_val :
    filteredVonMangoldtFiniteAbscissaSource.1 = filteredVonMangoldtArithmetic :=
  rfl

/-- A filtered von Mangoldt coefficient can be nonzero only on a positive prime power. -/
theorem filteredVonMangoldtArithmetic_supportedOnPositivePrimePowers :
    SupportedOnPositivePrimePowers filteredVonMangoldtArithmetic := by
  intro n hn
  have hLambda : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro hzero
    apply hn
    simp [filteredVonMangoldtArithmetic, filteredVonMangoldtCoeff, hzero]
  have hpow : IsPrimePow n :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLambda
  let x : PrimePowerClockIndex :=
    Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩
  have hx := congrArg Subtype.val
    (Nat.Primes.prodNatEquiv.apply_symm_apply ⟨n, hpow⟩)
  have hn : (x.1 : ℕ) ^ (x.2 + 1) = n := by
    simpa only [x, Nat.Primes.coe_prodNatEquiv_apply] using hx
  exact ⟨x.1, x.2, hn.symm⟩

/-- At every prime, the filtered von Mangoldt coefficient is nonzero. -/
theorem filteredVonMangoldtCoeff_prime_ne_zero (p : Nat.Primes) :
    filteredVonMangoldtCoeff p ≠ 0 := by
  rw [filteredVonMangoldtCoeff,
    ArithmeticFunction.vonMangoldt_apply_prime p.2]
  apply mul_ne_zero
  · have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
    exact_mod_cast (Real.log_pos hp).ne'
  · have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
    have hpow : ((p : ℕ) : ℝ) ^ (-(2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
    have hcpow : (p : ℂ) ^ (-(2 : ℂ)) =
        (((p : ℕ) : ℝ) ^ (-(2 : ℝ)) : ℝ) := by
      simpa using
        (Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ)) (-(2 : ℝ))).symm
    rw [hcpow]
    exact_mod_cast (sub_pos.mpr hpow).ne'

/-- The filtered von Mangoldt arithmetic source is formally differentially independent over
`C`.  Higher prime-power layers are unrestricted; the nonzero prime layer is the echelon pivot. -/
theorem filteredVonMangoldtArithmetic_differentialIndependent :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun _ : Fin 1 ↦ algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField filteredVonMangoldtArithmetic) := by
  apply primeValuationLeadingEchelon_differentialIndependent_of_primeDependent
    (fun _ : Fin 1 ↦ filteredVonMangoldtArithmetic)
    (fun _ : Fin 1 ↦ 0)
    (fun _ _ _ ↦ Subsingleton.elim _ _)
    (fun _ p ↦ filteredVonMangoldtCoeff p)
    (fun _ p ↦ filteredVonMangoldtCoeff_prime_ne_zero p)
    (fun _ ↦ filteredVonMangoldtArithmetic_supportedOnPositivePrimePowers)
  intro r s p
  have hrs : r = s := Subsingleton.elim _ _
  subst s
  simp [filteredVonMangoldtArithmetic]

/-- The actual finite-abscissa carrier of the filtered von Mangoldt source is differentially
independent over the rational upper-end coordinate field. -/
theorem filteredVonMangoldtUpperEndCarrier_differentialIndependent :
    GaloisForLFunctions.DifferentialIndependent upperEndRationalCoordinateField
      (fun _ : Fin 1 ↦ finiteAbscissaLSeriesToUpperEndMero
        filteredVonMangoldtFiniteAbscissaSource) := by
  apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
  simpa [filteredVonMangoldtFiniteAbscissaSource] using
    filteredVonMangoldtArithmetic_differentialIndependent

/-- Actual upper-end meromorphic carrier of the filtered von Mangoldt L-series. -/
def filteredVonMangoldtUpperEndCarrier : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero filteredVonMangoldtFiniteAbscissaSource

/-- **Filtered-prime hypertranscendence.**  The actual meromorphic germ exposed by the completed
`+2` xi shift is hypertranscendental over `C(z)`. -/
theorem filteredVonMangoldtUpperEndCarrier_hypertranscendentalOver :
    HypertranscendentalOver upperEndRationalCoordinateField
      filteredVonMangoldtUpperEndCarrier := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hunit := filteredVonMangoldtUpperEndCarrier_differentialIndependent.comp
    (fun _ : Unit ↦ (0 : Fin 1)) (fun _ _ _ ↦ Subsingleton.elim _ _)
  simpa [Function.comp_def, filteredVonMangoldtUpperEndCarrier] using hunit

/-- Underlying upper-end germ of the filtered von Mangoldt L-series. -/
def filteredVonMangoldtUpperEndGerm : Germ upperEndFilter ℂ :=
  finiteAbscissaLSeriesToUpperEndGerm filteredVonMangoldtFiniteAbscissaSource

@[simp]
theorem filteredVonMangoldtUpperEndGerm_eq_lSeries :
    filteredVonMangoldtUpperEndGerm =
      ((fun z : ℂ ↦ LSeries filteredVonMangoldtCoeff (-Complex.I * z)) :
        Germ upperEndFilter ℂ) := by
  rfl

/-- Upper-end germ of the rationally renormalized `+2` shift defect of `xi'/xi`. -/
def xiLogDerivShiftTwoPrimeDefectUpperEndGerm : Germ upperEndFilter ℂ :=
  ((fun z : ℂ ↦
      logDeriv xi (-Complex.I * z + 2) - logDeriv xi (-Complex.I * z) -
        (1 / (-Complex.I * z + 2) + 1 / (-Complex.I * z + 1) -
          1 / (-Complex.I * z - 1))) : Germ upperEndFilter ℂ)

/-- **Value reflection into the xi shift defect.**  The carrier proved hypertranscendental above
is exactly the rationally corrected `+2` shift defect of the actual completed logarithmic
derivative, as an upper-end germ. -/
theorem filteredVonMangoldtUpperEndGerm_eq_xiLogDerivShiftTwoPrimeDefect :
    filteredVonMangoldtUpperEndGerm =
      xiLogDerivShiftTwoPrimeDefectUpperEndGerm := by
  rw [filteredVonMangoldtUpperEndGerm_eq_lSeries]
  apply Germ.coe_eq.mpr
  have hupper : ∀ᶠ z in upperEndFilter, 1 < z.im := by
    rw [upperEndFilter_basis.eventually_iff]
    exact ⟨1, trivial, fun _ hz ↦ hz⟩
  filter_upwards [hupper] with z hz
  have hs : 1 < (-Complex.I * z).re := by
    simpa [Complex.mul_re] using hz
  have h := xi_logDeriv_shift_two_exposes_prime_source
    (s := -Complex.I * z) hs
  simpa [xiLogDerivShiftTwoPrimeDefectUpperEndGerm,
    filteredVonMangoldtCoeff] using h.symm

end

end RHTower
