import GaloisForLFunctions.RHTower.PrimeDepthBVWoldGradedDet2StokesCartierTrivialization

/-!
# Positive Stokes polarization of the resolved BV--Wold source

The resolved determinant-one BV--Wold source frame carries a canonical
positive Hermitian polarization.  Pulling the ordinary positive form back
through the literal source frame makes every resolved transition Stokes-flat,
unconditionally and at every centered rate.

This does not turn the transported metric field into one fixed same-fibre
Cartier metric.  Freezing the source metric at zero rate and transporting the
literal clock-normalized vertical conormal produces an exact nonnegative
excess.  It is the square of the fully labelled BV--Wold mixing coefficient.
On the actual nonzero Xi conormal and explicit source edge, fixed-metric
flatness is equivalent to the critical line; globally it is equivalent to
RH.  Thus positive resolved flatness exists, while its fixed Cartier descent
is the exact remaining arithmetic selection law.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Positive resolved polarization -/

/-- Hermitian polarization pulled back through the literal resolved source
frame. -/
def primeDepthBVWoldResolvedPolarization
    (a : ℝ) (i : PrimeDepthBVWoldCell) (z w : ℂ × ℂ) : ℂ :=
  let gz := primeDepthBVWoldResolvedSourceFrame a i z
  let gw := primeDepthBVWoldResolvedSourceFrame a i w
  gz.1 * star gw.1 + gz.2 * star gw.2

/-- Positive energy of the resolved polarization. -/
def primeDepthBVWoldResolvedPolarizationEnergy
    (a : ℝ) (i : PrimeDepthBVWoldCell) (z : ℂ × ℂ) : ℝ :=
  Complex.normSq (primeDepthBVWoldResolvedSourceFrame a i z).1 +
    Complex.normSq (primeDepthBVWoldResolvedSourceFrame a i z).2

theorem primeDepthBVWoldResolvedPolarization_self
    (a : ℝ) (i : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldResolvedPolarization a i z z =
      (primeDepthBVWoldResolvedPolarizationEnergy a i z : ℂ) := by
  change
    (primeDepthBVWoldResolvedSourceFrame a i z).1 *
          star (primeDepthBVWoldResolvedSourceFrame a i z).1 +
        (primeDepthBVWoldResolvedSourceFrame a i z).2 *
          star (primeDepthBVWoldResolvedSourceFrame a i z).2 =
      ((Complex.normSq
          (primeDepthBVWoldResolvedSourceFrame a i z).1 +
        Complex.normSq
          (primeDepthBVWoldResolvedSourceFrame a i z).2 : ℝ) : ℂ)
  rw [show
      (primeDepthBVWoldResolvedSourceFrame a i z).1 *
          star (primeDepthBVWoldResolvedSourceFrame a i z).1 =
        (Complex.normSq
          (primeDepthBVWoldResolvedSourceFrame a i z).1 : ℂ) from
      Complex.mul_conj _,
    show
      (primeDepthBVWoldResolvedSourceFrame a i z).2 *
          star (primeDepthBVWoldResolvedSourceFrame a i z).2 =
        (Complex.normSq
          (primeDepthBVWoldResolvedSourceFrame a i z).2 : ℂ) from
      Complex.mul_conj _]
  push_cast
  rfl

theorem primeDepthBVWoldResolvedPolarizationEnergy_nonneg
    (a : ℝ) (i : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    0 ≤ primeDepthBVWoldResolvedPolarizationEnergy a i z := by
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- The source-frame polarization is positive definite, not merely
semidefinite. -/
theorem primeDepthBVWoldResolvedPolarizationEnergy_eq_zero_iff
    (a : ℝ) (i : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldResolvedPolarizationEnergy a i z = 0 ↔ z = 0 := by
  constructor
  · intro hzero
    change
      Complex.normSq
            (primeDepthBVWoldResolvedSourceFrame a i z).1 +
          Complex.normSq
            (primeDepthBVWoldResolvedSourceFrame a i z).2 = 0 at hzero
    have hfst :
        Complex.normSq
            (primeDepthBVWoldResolvedSourceFrame a i z).1 = 0 := by
      nlinarith [Complex.normSq_nonneg
          (primeDepthBVWoldResolvedSourceFrame a i z).1,
        Complex.normSq_nonneg
          (primeDepthBVWoldResolvedSourceFrame a i z).2]
    have hsnd :
        Complex.normSq
            (primeDepthBVWoldResolvedSourceFrame a i z).2 = 0 := by
      nlinarith [Complex.normSq_nonneg
          (primeDepthBVWoldResolvedSourceFrame a i z).1,
        Complex.normSq_nonneg
          (primeDepthBVWoldResolvedSourceFrame a i z).2]
    have hframe : primeDepthBVWoldResolvedSourceFrame a i z = 0 := by
      apply Prod.ext
      · exact Complex.normSq_eq_zero.mp hfst
      · exact Complex.normSq_eq_zero.mp hsnd
    calc
      z = primeDepthBVWoldResolvedSourceFrameInv a i
          (primeDepthBVWoldResolvedSourceFrame a i z) :=
        (primeDepthBVWoldResolvedSourceFrameInv_frame a i z).symm
      _ = 0 := by rw [hframe, map_zero]
  · rintro rfl
    simp [primeDepthBVWoldResolvedPolarizationEnergy]

/-- Frame form of the resolved transition. -/
theorem primeDepthBVWoldResolvedSourceFrame_transport
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldResolvedSourceFrame a i
        (primeDepthBVWoldResolvedTransport a i j z) =
      primeDepthBVWoldResolvedSourceFrame a j z := by
  rw [primeDepthBVWoldResolvedTransport_eq_frameTransition,
    primeDepthBVWoldResolvedSourceFrame_frameInv]

/-- Independent Stokes-flatness law for the positive resolved
polarization.  It follows from source-frame composition, not anomaly
vanishing or an Xi hypothesis. -/
theorem primeDepthBVWoldResolvedTransport_preserves_polarization
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (z w : ℂ × ℂ) :
    primeDepthBVWoldResolvedPolarization a i
        (primeDepthBVWoldResolvedTransport a i j z)
        (primeDepthBVWoldResolvedTransport a i j w) =
      primeDepthBVWoldResolvedPolarization a j z w := by
  simp only [primeDepthBVWoldResolvedPolarization,
    primeDepthBVWoldResolvedSourceFrame_transport]

theorem primeDepthBVWoldResolvedTransport_preserves_polarizationEnergy
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldResolvedPolarizationEnergy a i
        (primeDepthBVWoldResolvedTransport a i j z) =
      primeDepthBVWoldResolvedPolarizationEnergy a j z := by
  simp only [primeDepthBVWoldResolvedPolarizationEnergy,
    primeDepthBVWoldResolvedSourceFrame_transport]

/-! ## Fixed source metric and its exact Stokes excess -/

/-- Source-fixed Cartier energy: freeze the resolved polarization before
the centered deformation. -/
def primeDepthBVWoldSourcePolarizationEnergy
    (i : PrimeDepthBVWoldCell) (z : ℂ × ℂ) : ℝ :=
  primeDepthBVWoldResolvedPolarizationEnergy 0 i z

/-- Literal vertical conormal normalized by the positive Wold--Gamma clock.
Its fixed source energy is independent of the prime/depth frame. -/
def primeDepthBVWoldClockNormalizedVerticalConormal
    (c : ℂ) (i : PrimeDepthBVWoldCell) : ℂ × ℂ :=
  (0, (((xiGammaEulerPrimitivePrimeDepthLogClock i)⁻¹ : ℝ) : ℂ) * c)

theorem primeDepthBVWoldSourcePolarizationEnergy_verticalConormal
    (c : ℂ) (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldSourcePolarizationEnergy i
        (primeDepthBVWoldClockNormalizedVerticalConormal c i) =
      Complex.normSq c := by
  have hi := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero i
  rw [primeDepthBVWoldSourcePolarizationEnergy,
    primeDepthBVWoldResolvedPolarizationEnergy,
    primeDepthBVWoldClockNormalizedVerticalConormal]
  simp only [primeDepthBVWoldResolvedSourceFrame, LinearMap.coe_mk,
    AddHom.coe_mk, mul_zero, zero_add, zero_mul]
  push_cast
  field_simp [hi]
  simp

/-- Fixed-metric Stokes excess on the literal vertical conormal. -/
def primeDepthBVWoldSourcePolarizationStokesExcess
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) : ℝ :=
  primeDepthBVWoldSourcePolarizationEnergy i
      (primeDepthBVWoldResolvedTransport a i j
        (primeDepthBVWoldClockNormalizedVerticalConormal c j)) -
    primeDepthBVWoldSourcePolarizationEnergy j
      (primeDepthBVWoldClockNormalizedVerticalConormal c j)

/-- The exact excess is one norm square of the off-diagonal source mixing.
All prime/depth provenance remains explicit. -/
theorem primeDepthBVWoldSourcePolarizationStokesExcess_eq_normSq
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    primeDepthBVWoldSourcePolarizationStokesExcess a i j c =
      Complex.normSq
        ((((a * primeDepthBVWoldConnection i j /
            (xiGammaEulerPrimitivePrimeDepthLogClock i *
              xiGammaEulerPrimitivePrimeDepthLogClock j) : ℝ) : ℂ) * c)) := by
  have hi := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero i
  have hj := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero j
  rw [primeDepthBVWoldSourcePolarizationStokesExcess,
    primeDepthBVWoldSourcePolarizationEnergy_verticalConormal,
    primeDepthBVWoldSourcePolarizationEnergy,
    primeDepthBVWoldResolvedPolarizationEnergy,
    primeDepthBVWoldClockNormalizedVerticalConormal]
  simp only [primeDepthBVWoldResolvedTransport,
    primeDepthBVWoldResolvedSourceFrame, LinearMap.coe_mk,
    AddHom.coe_mk, mul_zero, zero_mul]
  push_cast
  field_simp [hi, hj]
  ring_nf
  rw [Complex.normSq_neg]

theorem primeDepthBVWoldSourcePolarizationStokesExcess_eq
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    primeDepthBVWoldSourcePolarizationStokesExcess a i j c =
      (a * primeDepthBVWoldConnection i j /
          (xiGammaEulerPrimitivePrimeDepthLogClock i *
            xiGammaEulerPrimitivePrimeDepthLogClock j)) ^ (2 : ℕ) *
        Complex.normSq c := by
  rw [primeDepthBVWoldSourcePolarizationStokesExcess_eq_normSq,
    Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem primeDepthBVWoldSourcePolarizationStokesExcess_nonneg
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    0 ≤ primeDepthBVWoldSourcePolarizationStokesExcess a i j c := by
  rw [primeDepthBVWoldSourcePolarizationStokesExcess_eq]
  exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)

/-- On any nonzero source edge and nonzero vertical conormal, fixed-metric
Stokes flatness is exactly zero centered rate. -/
theorem primeDepthBVWoldSourcePolarizationStokesExcess_eq_zero_iff
    {a : ℝ} {i j : PrimeDepthBVWoldCell} {c : ℂ}
    (hij : primeDepthBVWoldConnection i j ≠ 0) (hc : c ≠ 0) :
    primeDepthBVWoldSourcePolarizationStokesExcess a i j c = 0 ↔
      a = 0 := by
  rw [primeDepthBVWoldSourcePolarizationStokesExcess_eq,
    mul_eq_zero]
  have hi := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero i
  have hj := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero j
  have hden :
      xiGammaEulerPrimitivePrimeDepthLogClock i *
          xiGammaEulerPrimitivePrimeDepthLogClock j ≠ 0 :=
    mul_ne_zero hi hj
  simp only [Complex.normSq_eq_zero, hc, or_false, sq_eq_zero_iff,
    div_eq_zero_iff, hden]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_right hij
  · rintro rfl
    simp

/-! ## Actual Xi conormal and RH classification -/

/-- Clock-normalized actual first nonzero Xi conormal. -/
def primeDepthBVWoldXiClockNormalizedVerticalConormal
    (rho : XiDivisorSupport) (i : PrimeDepthBVWoldCell) : ℂ × ℂ :=
  primeDepthBVWoldClockNormalizedVerticalConormal
    (iteratedDeriv (xiSupportMultiplicity rho) XiC
      (xiSpectralPointSupport rho)) i

theorem primeDepthBVWoldXiSourcePolarizationStokesExcess_witness_eq_zero_iff
    (rho : XiDivisorSupport) :
    primeDepthBVWoldSourcePolarizationStokesExcess
        (primeDepthBVWoldXiCenteredRate rho)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [primeDepthBVWoldSourcePolarizationStokesExcess_eq_zero_iff
      primeDepthBVWoldConnection_witness_pos.ne'
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho),
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Global fixed-source positive Stokes flatness on the actual Xi conormal. -/
def PrimeDepthBVWoldXiSourcePolarizationStokesFlat : Prop :=
  ∀ rho : XiDivisorSupport,
    primeDepthBVWoldSourcePolarizationStokesExcess
        (primeDepthBVWoldXiCenteredRate rho)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)) = 0

/-- Exact frontier: the resolved positive metric is unconditionally flat,
but fixed-source positive Stokes flatness on the literal Xi conormal is RH. -/
theorem primeDepthBVWoldXiSourcePolarizationStokesFlat_iff_riemannHypothesis :
    PrimeDepthBVWoldXiSourcePolarizationStokesFlat ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hline : z.re = 1 / 2 :=
      (primeDepthBVWoldXiSourcePolarizationStokesExcess_witness_eq_zero_iff
        rho).mp (h rho)
    have hzgt : 1 / 2 < z.re := mem_rightHalf.mp hz
    linarith
  · intro hRH rho
    exact
      (primeDepthBVWoldXiSourcePolarizationStokesExcess_witness_eq_zero_iff
        rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
