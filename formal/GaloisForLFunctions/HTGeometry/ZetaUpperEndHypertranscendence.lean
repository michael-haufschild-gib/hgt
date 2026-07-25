import GaloisForLFunctions.HTGeometry.PrimeClockAnalyticEulerCompletion
import GaloisForLFunctions.HTGeometry.PrimeValuationLeadingEchelon
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.FiniteAbscissaRationalCoordinateIndependence
import GaloisForLFunctions.HTGeometry.UpperEndRationalCoordinateDifferentialAdjoin
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import Mathlib

/-!
# Hypertranscendence of the zeta germ over the rational coordinate field

The von Mangoldt source is supported on prime powers and nonzero at every prime, so the
prime-dependent leading-echelon law makes it formally differentially independent, and the
finite-abscissa transfer carries that to its analytic upper-end carrier.

The convolution identity `Lambda * zeta = log` becomes, after realization, the exact relation
`L(Lambda) = -I * (Z' / Z)` between the von Mangoldt carrier and the logarithmic derivative of the
zeta germ.  Since hypertranscendence is preserved by the algebraic logarithmic derivative, the zeta
germ itself is hypertranscendental over `C(s)`.
-/

open ArithmeticFunction Filter Set
open scoped Differential LSeries.notation

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance zetaUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance zetaUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance zetaUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance zetaUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance zetaUpperEndComplexDifferential : Differential ℂ where
  deriv := 0

local instance zetaUpperEndComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ upperEndMeroField :=
  ⟨fun c ↦ by
    rw [upperEndMero_deriv_complexConstant c]
    change (0 : upperEndMeroField) = algebraMap ℂ upperEndMeroField 0
    rw [_root_.map_zero]⟩

local instance zetaUpperEndCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance zetaUpperEndCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance zetaUpperEndCoordinateScalarTower :
    IsScalarTower ℂ upperEndRationalCoordinateField upperEndMeroField :=
  .of_algebraMap_eq fun _ ↦ rfl

local instance zetaUpperEndCoordinateCharZero :
    CharZero upperEndRationalCoordinateField :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ upperEndRationalCoordinateField).injective

/-! ## The von Mangoldt source -/

/-- The von Mangoldt coefficients, complex valued. -/
def vonMangoldtArith : ArithmeticFunction ℂ where
  toFun n := (ArithmeticFunction.vonMangoldt n : ℂ)
  map_zero' := by simp

@[simp] theorem vonMangoldtArith_apply (n : ℕ) :
    vonMangoldtArith n = (ArithmeticFunction.vonMangoldt n : ℂ) := rfl

/-- The von Mangoldt source has finite abscissa. -/
def vonMangoldtSource : finiteAbscissaArithmeticSubalgebra := by
  refine ⟨vonMangoldtArith, 1, fun y hy => ?_⟩
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)

@[simp] theorem vonMangoldtSource_val : vonMangoldtSource.1 = vonMangoldtArith := rfl

theorem vonMangoldtArith_supportedOnPositivePrimePowers :
    SupportedOnPositivePrimePowers vonMangoldtArith := by
  intro n hn
  have hLambda : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro hzero
    exact hn (by simp [vonMangoldtArith, hzero])
  have hpow : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLambda
  let x : PrimePowerClockIndex := Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩
  have hx := congrArg Subtype.val (Nat.Primes.prodNatEquiv.apply_symm_apply ⟨n, hpow⟩)
  have hnx : (x.1 : ℕ) ^ (x.2 + 1) = n := by
    simpa only [x, Nat.Primes.coe_prodNatEquiv_apply] using hx
  exact ⟨x.1, x.2, hnx.symm⟩

theorem vonMangoldtArith_prime_ne_zero (p : Nat.Primes) : vonMangoldtArith p ≠ 0 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hlog : Real.log p ≠ 0 := (Real.log_pos hp).ne'
  show ((ArithmeticFunction.vonMangoldt (p : ℕ) : ℝ) : ℂ) ≠ 0
  rw [ArithmeticFunction.vonMangoldt_apply_prime p.2]
  exact_mod_cast hlog

/-- The von Mangoldt source is formally differentially independent over `C`. -/
theorem vonMangoldtArith_differentialIndependent :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun _ : Fin 1 ↦ algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField vonMangoldtArith) := by
  apply primeValuationLeadingEchelon_differentialIndependent_of_primeDependent
    (fun _ : Fin 1 ↦ vonMangoldtArith)
    (fun _ : Fin 1 ↦ 0)
    (fun _ _ _ ↦ Subsingleton.elim _ _)
    (fun _ p ↦ vonMangoldtArith p)
    (fun _ p ↦ vonMangoldtArith_prime_ne_zero p)
    (fun _ ↦ vonMangoldtArith_supportedOnPositivePrimePowers)
  intro r s p
  have hrs : r = s := Subsingleton.elim _ _
  subst hrs
  simp

/-- The analytic upper-end carrier of the von Mangoldt L-series. -/
def vonMangoldtUpperEndMero : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero vonMangoldtSource

theorem vonMangoldtUpperEndMero_hypertranscendentalOver :
    GaloisForLFunctions.HypertranscendentalOver upperEndRationalCoordinateField
      vonMangoldtUpperEndMero := by
  rw [GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hcarrier : GaloisForLFunctions.DifferentialIndependent upperEndRationalCoordinateField
      (fun _ : Fin 1 ↦ finiteAbscissaLSeriesToUpperEndMero vonMangoldtSource) := by
    apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
    simpa [vonMangoldtSource] using vonMangoldtArith_differentialIndependent
  have hunit := hcarrier.comp (fun _ : Unit ↦ (0 : Fin 1))
    (fun _ _ _ ↦ Subsingleton.elim _ _)
  simpa [Function.comp_def, vonMangoldtUpperEndMero] using hunit

/-! ## The zeta source -/

/-- The all-ones coefficient stream. -/
def zetaArith : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else 1
  map_zero' := by simp

@[simp] theorem zetaArith_apply (n : ℕ) : zetaArith n = if n = 0 then 0 else 1 := rfl

theorem zetaArith_eq_zeta (n : ℕ) :
    zetaArith n = ((ArithmeticFunction.zeta n : ℕ) : ℂ) := by
  by_cases h : n = 0 <;> simp [h, ArithmeticFunction.zeta_apply]

/-- The zeta source has finite abscissa. -/
def zetaSource : finiteAbscissaArithmeticSubalgebra := by
  refine ⟨zetaArith, 1, fun y hy => ?_⟩
  have hre : (1 : ℝ) < ((y : ℂ)).re := by simpa using hy
  have h := LSeriesSummable_zeta_iff.mpr hre
  exact (LSeriesSummable_congr _ (fun {n} _ => (zetaArith_eq_zeta n).symm)).mp h

@[simp] theorem zetaSource_val : zetaSource.1 = zetaArith := rfl

theorem zetaSource_ne_zero : zetaSource ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : finiteAbscissaArithmeticSubalgebra => f.1 1) h
  simp only [zetaSource_val, zetaArith_apply] at h1
  norm_num at h1

/-- The zeta germ in the upper-end meromorphic field. -/
def zetaUpperEndMero : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero zetaSource

theorem zetaUpperEndMero_ne_zero : zetaUpperEndMero ≠ 0 := by
  intro h
  refine zetaSource_ne_zero (finiteAbscissaLSeriesToUpperEndMero_injective ?_)
  show finiteAbscissaLSeriesToUpperEndMero zetaSource = finiteAbscissaLSeriesToUpperEndMero 0
  rw [_root_.map_zero]
  exact h

/-- **The zeta germ is the germ of `z ↦ zeta (-I z)`.** -/
theorem zetaUpperEndGerm_eq :
    (finiteAbscissaLSeriesToUpperEndGerm zetaSource : Germ upperEndFilter ℂ)
      = ((fun z : ℂ => riemannZeta (-Complex.I * z)) : Germ upperEndFilter ℂ) := by
  refine Germ.coe_eq.mpr ?_
  show ∀ᶠ z : ℂ in upperEndFilter,
    LSeries (fun n => zetaSource.1 n) (-Complex.I * z) = riemannZeta (-Complex.I * z)
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨1, trivial, fun z hz => ?_⟩
  have hre : 1 < (-Complex.I * z).re := by
    have : (-Complex.I * z).re = z.im := by simp [Complex.mul_re]
    rw [this]
    simpa [upperTail] using hz
  have hz2 := LSeries_zeta_eq_riemannZeta hre
  rw [← hz2]
  exact LSeries_congr (fun {n} _ => zetaArith_eq_zeta n) _

/-! ## The logarithmic-derivative relation -/

theorem vonMangoldt_mul_zeta_eq_logWeight :
    vonMangoldtSource * zetaSource = finiteAbscissaLogWeight zetaSource := by
  apply Subtype.ext
  refine ArithmeticFunction.ext fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : n ≠ 0 := by omega
  show (vonMangoldtArith * zetaArith) n = (Real.log n : ℂ) * zetaArith n
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun d e => vonMangoldtArith d * zetaArith e)]
  have hsum : ∀ i ∈ n.divisors, vonMangoldtArith i * zetaArith (n / i)
      = ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) := by
    intro i hi
    obtain ⟨hid, -⟩ := Nat.mem_divisors.mp hi
    have hpos : 0 < n / i := Nat.div_pos (Nat.le_of_dvd hn hid) (Nat.pos_of_dvd_of_pos hid hn)
    have hne : n / i ≠ 0 := by omega
    simp [hne]
  rw [Finset.sum_congr rfl hsum]
  rw [show ∑ i ∈ n.divisors, ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ)
      = ((∑ i ∈ n.divisors, ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) by push_cast; ring]
  rw [ArithmeticFunction.vonMangoldt_sum]
  simp [hn0]

/-- **The von Mangoldt carrier is the rotated logarithmic derivative of the zeta germ.** -/
theorem vonMangoldtUpperEndMero_eq :
    vonMangoldtUpperEndMero
      = algebraMap ℂ upperEndMeroField (-Complex.I)
        * ((zetaUpperEndMero)′ / zetaUpperEndMero) := by
  have hderiv : (zetaUpperEndMero)′
      = algebraMap ℂ upperEndMeroField Complex.I
        * (vonMangoldtUpperEndMero * zetaUpperEndMero) := by
    rw [zetaUpperEndMero, deriv_finiteAbscissaLSeriesToUpperEndMero]
    rw [show finiteAbscissaRotatedDeriv zetaSource
        = Complex.I • finiteAbscissaLogWeight zetaSource from rfl]
    rw [map_smul, ← vonMangoldt_mul_zeta_eq_logWeight, map_mul, Algebra.smul_def]
    rfl
  rw [hderiv]
  have hz : zetaUpperEndMero ≠ 0 := zetaUpperEndMero_ne_zero
  have hI : algebraMap ℂ upperEndMeroField (-Complex.I)
      * algebraMap ℂ upperEndMeroField Complex.I = 1 := by
    rw [← map_mul]
    rw [show (-Complex.I) * Complex.I = 1 by
      rw [neg_mul, Complex.I_mul_I]; ring]
    exact map_one _
  have hcancel : (algebraMap ℂ upperEndMeroField Complex.I
        * (vonMangoldtUpperEndMero * zetaUpperEndMero)) / zetaUpperEndMero
      = algebraMap ℂ upperEndMeroField Complex.I * vonMangoldtUpperEndMero := by
    field_simp
  rw [hcancel, ← mul_assoc, hI, one_mul]

/-- **The zeta germ is hypertranscendental over the rational coordinate field.** -/
theorem zetaUpperEndMero_hypertranscendentalOver :
    GaloisForLFunctions.HypertranscendentalOver upperEndRationalCoordinateField
      zetaUpperEndMero := by
  have hconst : GaloisForLFunctions.DifferentialAlgebraicOver
      upperEndRationalCoordinateField
      (algebraMap ℂ upperEndMeroField (-Complex.I)) := by
    have h := differentialAlgebraicOver_algebraMap
      (F := upperEndRationalCoordinateField) (E := upperEndMeroField)
      (algebraMap ℂ upperEndRationalCoordinateField (-Complex.I))
    simpa using h
  have hne : algebraMap ℂ upperEndMeroField (-Complex.I) ≠ 0 := by
    intro h
    have hz : (-Complex.I : ℂ) = 0 := by
      refine upperEndComplexToMero.injective ?_
      rw [_root_.map_zero]
      exact h
    simp at hz
  have hlog : GaloisForLFunctions.HypertranscendentalOver upperEndRationalCoordinateField
      ((zetaUpperEndMero)′ / zetaUpperEndMero) := by
    have hprod : GaloisForLFunctions.HypertranscendentalOver upperEndRationalCoordinateField
        (((zetaUpperEndMero)′ / zetaUpperEndMero)
          * algebraMap ℂ upperEndMeroField (-Complex.I)) := by
      have h := vonMangoldtUpperEndMero_hypertranscendentalOver
      rw [vonMangoldtUpperEndMero_eq] at h
      rwa [mul_comm]
    exact (hypertranscendentalOver_mul_differentialAlgebraic_iff hconst hne).mp hprod
  exact (GaloisForLFunctions.hypertranscendentalOver_deriv_div_self_iff zetaUpperEndMero).mp hlog

end

end GaloisForLFunctions.HTGeometry
