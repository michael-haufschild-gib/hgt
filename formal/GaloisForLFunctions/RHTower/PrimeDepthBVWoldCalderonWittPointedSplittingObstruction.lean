import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittKoszulSource
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldPositiveStokesPolarization

/-!
# Calderón--Witt pointed splitting and its Route-R obstruction

The directed rational-Witt/Koszul source already contains two canonical
sections: the normalized Haar orientation section of its suspension center
and the center-to-degree-one section of its Koszul boundary.  Their composite
is a source-pointed degree-one class, constructed before any Xi divisor.

This module constructs a two-coordinate reporter whose horizontal coordinate
is the Meyer--Calderón defect and whose vertical coordinate is the oriented
Koszul boundary.  It sends the canonical source section exactly to `(0, c)`.
After Wold--Gamma clock normalization, it sends that section to the literal
vertical conormal used by Route R.

The comparison with resolved BV--Wold transport has one exact horizontal
defect:

`-a * theta(i,j) * lambda_j⁻¹ * c`.

Thus the rational-Witt source side of the pointed splitting is constructed,
but its singular Cartier comparison commutes on a nonzero edge exactly at
zero centered rate.  On the actual leading Xi conormal, global commutation is
equivalent to RH.  No commutation or RH premise is assumed below.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Literal rational-Witt source section and reporter -/

/-- Canonical pointed source class: normalized Haar orientation section,
followed by the exact Koszul center-to-degree-one section. -/
def deningerCalderonWittRouteRPointedSection
    (p : Nat.Primes) :
    ℂ →ₗ[ℂ] DeningerCalderonWittAlgebraicDegreeOne p :=
  (deningerCalderonWittCenterToDegreeOne p).comp
    (deningerCalderonWittAlgebraicCenterOrientationSection p)

/-- Source-native two-coordinate reporter.  It retains the Calderón defect
coordinate and the normalized Haar trace of the Koszul boundary. -/
def deningerCalderonWittRouteRScalarReporter
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ] (ℂ × ℂ) where
  toFun x :=
    (deningerMeyerPoissonCalderonQuotientEquiv (p : ℝ) x.1,
      deningerCalderonWittAlgebraicCenterTrace p
        (deningerCalderonWittKoszulBoundary p x))
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- The actual rational-Witt/Koszul source section lands exactly on the
distinguished vertical splitting. -/
theorem deningerCalderonWittRouteRScalarReporter_pointedSection
    (p : Nat.Primes) (c : ℂ) :
    deningerCalderonWittRouteRScalarReporter p
        (deningerCalderonWittRouteRPointedSection p c) =
      (0, c) := by
  change
    (deningerMeyerPoissonCalderonQuotientEquiv (p : ℝ)
        (deningerCalderonWittCenterToDegreeOne p
          (deningerCalderonWittAlgebraicCenterOrientationSection p c)).1,
      deningerCalderonWittAlgebraicCenterTrace p
        (deningerCalderonWittKoszulBoundary p
          (deningerCalderonWittCenterToDegreeOne p
            (deningerCalderonWittAlgebraicCenterOrientationSection p c)))) =
      (0, c)
  apply Prod.ext
  · rw [deningerCalderonWittCenterToDegreeOne_apply]
    simp
  · change
      deningerCalderonWittAlgebraicCenterTrace p
          (deningerCalderonWittKoszulBoundary p
            (deningerCalderonWittCenterToDegreeOne p
              (deningerCalderonWittAlgebraicCenterOrientationSection p c))) = c
    have hsection := LinearMap.congr_fun
      (deningerCalderonWittKoszulBoundary_section p)
      (deningerCalderonWittAlgebraicCenterOrientationSection p c)
    have hsection' :
        deningerCalderonWittKoszulBoundary p
            (deningerCalderonWittCenterToDegreeOne p
              (deningerCalderonWittAlgebraicCenterOrientationSection p c)) =
          deningerCalderonWittAlgebraicCenterOrientationSection p c := by
      simpa [LinearMap.comp_apply] using hsection
    calc
      _ = deningerCalderonWittAlgebraicCenterTrace p
          (deningerCalderonWittAlgebraicCenterOrientationSection p c) :=
        congrArg (deningerCalderonWittAlgebraicCenterTrace p) hsection'
      _ = c :=
        deningerCalderonWittAlgebraicCenterTrace_orientationSection p c

/-- The pointed source section is coefficient-faithful before completion or
Xi specialization. -/
theorem deningerCalderonWittRouteRPointedSection_injective
    (p : Nat.Primes) :
    Function.Injective (deningerCalderonWittRouteRPointedSection p) := by
  intro c d hcd
  have hreport := congrArg (deningerCalderonWittRouteRScalarReporter p) hcd
  rw [deningerCalderonWittRouteRScalarReporter_pointedSection,
    deningerCalderonWittRouteRScalarReporter_pointedSection] at hreport
  exact congrArg Prod.snd hreport

/-! ## Wold--Gamma clock normalization -/

/-- Literal source section normalized by the finite Wold--Gamma clock at a
prime/depth cell. -/
def deningerCalderonWittRouteRClockNormalizedPointedSection
    (p : Nat.Primes) (e : ℕ) :
    ℂ →ₗ[ℂ] DeningerCalderonWittAlgebraicDegreeOne p :=
  (deningerCalderonWittRouteRPointedSection p).comp
    (((((xiGammaEulerPrimitivePrimeDepthLogClock (p, e))⁻¹ : ℝ) : ℂ)) •
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ))

/-- The source-native reporter sends the clock-normalized rational-Witt
section to Route R's literal clock-normalized vertical conormal. -/
theorem deningerCalderonWittRouteRScalarReporter_clockNormalizedPointedSection
    (p : Nat.Primes) (e : ℕ) (c : ℂ) :
    deningerCalderonWittRouteRScalarReporter p
        (deningerCalderonWittRouteRClockNormalizedPointedSection p e c) =
      primeDepthBVWoldClockNormalizedVerticalConormal c (p, e) := by
  simpa [deningerCalderonWittRouteRClockNormalizedPointedSection,
    primeDepthBVWoldClockNormalizedVerticalConormal] using
      deningerCalderonWittRouteRScalarReporter_pointedSection p
        ((((xiGammaEulerPrimitivePrimeDepthLogClock (p, e))⁻¹ : ℝ) : ℂ) * c)

/-! ## Exact pointed-comparison obstruction -/

/-- Exact failure of the resolved Route-R transport to carry the actual
rational-Witt pointed section between same-prime depth cells. -/
theorem deningerCalderonWittRouteRPointedComparison_defect
    (p : Nat.Primes) (e f : ℕ) (a : ℝ) (c : ℂ) :
    primeDepthBVWoldResolvedTransport a (p, e) (p, f)
          (deningerCalderonWittRouteRScalarReporter p
            (deningerCalderonWittRouteRClockNormalizedPointedSection
              p f c)) -
        deningerCalderonWittRouteRScalarReporter p
          (deningerCalderonWittRouteRClockNormalizedPointedSection p e c) =
      (-(((a * primeDepthBVWoldConnection (p, e) (p, f) : ℝ) : ℂ) *
          (((xiGammaEulerPrimitivePrimeDepthLogClock (p, f))⁻¹ : ℝ) : ℂ) * c),
        0) := by
  rw [deningerCalderonWittRouteRScalarReporter_clockNormalizedPointedSection,
    deningerCalderonWittRouteRScalarReporter_clockNormalizedPointedSection]
  have he := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero (p, e)
  have hf := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero (p, f)
  apply Prod.ext
  · simp [primeDepthBVWoldResolvedTransport,
      primeDepthBVWoldClockNormalizedVerticalConormal]
    ring
  · simp [primeDepthBVWoldResolvedTransport,
      primeDepthBVWoldClockNormalizedVerticalConormal]
    field_simp [he, hf]
    ring

/-- On a nonzero source edge and nonzero pointed coefficient, commutation of
the rational-Witt source section with resolved transport is equivalent to
zero centered rate. -/
theorem deningerCalderonWittRouteRPointedComparison_flat_iff
    (p : Nat.Primes) (e f : ℕ) (a : ℝ) (c : ℂ)
    (hconn : primeDepthBVWoldConnection (p, e) (p, f) ≠ 0)
    (hc : c ≠ 0) :
    primeDepthBVWoldResolvedTransport a (p, e) (p, f)
        (deningerCalderonWittRouteRScalarReporter p
          (deningerCalderonWittRouteRClockNormalizedPointedSection p f c)) =
      deningerCalderonWittRouteRScalarReporter p
        (deningerCalderonWittRouteRClockNormalizedPointedSection p e c) ↔
      a = 0 := by
  constructor
  · intro h
    have hsub :
        primeDepthBVWoldResolvedTransport a (p, e) (p, f)
              (deningerCalderonWittRouteRScalarReporter p
                (deningerCalderonWittRouteRClockNormalizedPointedSection
                  p f c)) -
            deningerCalderonWittRouteRScalarReporter p
              (deningerCalderonWittRouteRClockNormalizedPointedSection
                p e c) = 0 :=
      sub_eq_zero.mpr h
    rw [deningerCalderonWittRouteRPointedComparison_defect] at hsub
    have hfirst := congrArg Prod.fst hsub
    simp only [Prod.fst_zero] at hfirst
    have hclock :
        (((xiGammaEulerPrimitivePrimeDepthLogClock (p, f))⁻¹ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast inv_ne_zero
        (xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero (p, f))
    have hrest :
        (((xiGammaEulerPrimitivePrimeDepthLogClock (p, f))⁻¹ : ℝ) : ℂ) * c ≠ 0 :=
      mul_ne_zero hclock hc
    have hcast :
        ((a * primeDepthBVWoldConnection (p, e) (p, f) : ℝ) : ℂ) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hrest
      simpa only [neg_eq_zero, mul_assoc] using hfirst
    have hreal := congrArg Complex.re hcast
    norm_num at hreal
    exact hreal.resolve_right hconn
  · rintro rfl
    have hdef :=
      deningerCalderonWittRouteRPointedComparison_defect p e f 0 c
    apply sub_eq_zero.mp
    change
      primeDepthBVWoldResolvedTransport 0 (p, e) (p, f)
            (deningerCalderonWittRouteRScalarReporter p
              (deningerCalderonWittRouteRClockNormalizedPointedSection
                p f c)) -
          deningerCalderonWittRouteRScalarReporter p
            (deningerCalderonWittRouteRClockNormalizedPointedSection
              p e c) = (0, 0)
    simpa using hdef

/-! ## Actual Xi landing and RH-sharp endpoint -/

/-- The literal Calderón--Witt pointed section commutes with Route-R
transport on every actual leading Xi conormal.  This is a named target, not
an assumed theorem. -/
def PrimeDepthBVWoldXiCalderonWittPointedComparisonFlat : Prop :=
  ∀ rho : XiDivisorSupport,
    primeDepthBVWoldResolvedTransport
        (primeDepthBVWoldXiCenteredRate rho)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        (deningerCalderonWittRouteRScalarReporter ⟨2, Nat.prime_two⟩
          (deningerCalderonWittRouteRClockNormalizedPointedSection
            ⟨2, Nat.prime_two⟩ 1
            (iteratedDeriv (xiSupportMultiplicity rho) XiC
              (xiSpectralPointSupport rho)))) =
      deningerCalderonWittRouteRScalarReporter ⟨2, Nat.prime_two⟩
        (deningerCalderonWittRouteRClockNormalizedPointedSection
          ⟨2, Nat.prime_two⟩ 0
          (iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho)))

/-- Pointwise pointed-comparison commutation on the actual nonzero Xi
conormal is exactly critical-line location. -/
theorem deningerCalderonWittRouteRXiPointedComparison_flat_iff
    (rho : XiDivisorSupport) :
    primeDepthBVWoldResolvedTransport
        (primeDepthBVWoldXiCenteredRate rho)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        (deningerCalderonWittRouteRScalarReporter ⟨2, Nat.prime_two⟩
          (deningerCalderonWittRouteRClockNormalizedPointedSection
            ⟨2, Nat.prime_two⟩ 1
            (iteratedDeriv (xiSupportMultiplicity rho) XiC
              (xiSpectralPointSupport rho)))) =
      deningerCalderonWittRouteRScalarReporter ⟨2, Nat.prime_two⟩
        (deningerCalderonWittRouteRClockNormalizedPointedSection
          ⟨2, Nat.prime_two⟩ 0
          (iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho))) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [show
      primeDepthBVWoldWitnessZero = (⟨2, Nat.prime_two⟩, 0) from rfl,
    show
      primeDepthBVWoldWitnessOne = (⟨2, Nat.prime_two⟩, 1) from rfl,
    deningerCalderonWittRouteRPointedComparison_flat_iff
      ⟨2, Nat.prime_two⟩ 0 1
      (primeDepthBVWoldXiCenteredRate rho)
      (iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho))
      primeDepthBVWoldConnection_witness_pos.ne'
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho),
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Global commutation of the constructed source-pointed comparison is
exactly RH.  The new construction removes source-section existence from the
frontier while exposing the singular comparison law as the RH-bearing step. -/
theorem
    primeDepthBVWoldXiCalderonWittPointedComparisonFlat_iff_riemannHypothesis :
    PrimeDepthBVWoldXiCalderonWittPointedComparisonFlat ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hline : z.re = 1 / 2 :=
      (deningerCalderonWittRouteRXiPointedComparison_flat_iff rho).mp (h rho)
    have hzgt : 1 / 2 < z.re := mem_rightHalf.mp hz
    linarith
  · intro hRH rho
    exact
      (deningerCalderonWittRouteRXiPointedComparison_flat_iff rho).mpr
        (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
