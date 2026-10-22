import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSelfDualEinsteinDilationCarrier
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo

/-!
# Self-dual Hawking response variation and QNM-clock transgression

The normalized self-dual Einstein--AdS4 quadratic source derived from the horizon Mellin mode has
unit-amplitude coefficient

`C(rho) = (1 + rho / 2) (rho / 2)^(2 : ℕ) = rho^(2 : ℕ) (rho + 2) / 8`.

Its intensity `I(rho)=|C(rho)|^(2 : ℕ)` is not reflection invariant.  Writing
`x = Re rho - 1/2`, its exact theta-reflection variation is

`I(rho) - I(1-rho) = x S(rho) / 32`,

where

`S = 5 A^(2 : ℕ) + 2 A B + 5 x^(2 : ℕ)`,
`A = x^(2 : ℕ) + (Im rho)^(2 : ℕ) + 1/4`, and
`B = x^(2 : ℕ) + (Im rho)^(2 : ℕ) + 25/4`.

The susceptibility `S` is strictly positive.  Thus intensity equality occurs exactly on the
critical line, with no phase convention and no critical-strip restriction.

On the Xi divisor, the same horizontal charge is the Birmingham--Mokhtari frequency difference
between functional-equation-reflected and Schwarz-conjugated QNM sectors.  The final two theorems
identify response variation with that exact QNM-clock variation and with deviation from canonical
Hawking thermal splitting.
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Unit-amplitude coefficient of the normalized self-dual Einstein quadratic horizon source. -/
def d4ThetaHawkingSelfDualUnitResponse (rho : ℂ) : ℂ :=
  (1 / 8 : ℂ) * rho * rho * (rho + 2)

theorem d4ThetaHawkingSelfDualUnitResponse_eq (rho : ℂ) :
    d4ThetaHawkingSelfDualUnitResponse rho =
      (1 + rho / 2) * (rho / 2) ^ (2 : ℕ) := by
  rw [d4ThetaHawkingSelfDualUnitResponse]
  ring

/-- Squared norm of the normalized self-dual quadratic source coefficient. -/
def d4ThetaHawkingSelfDualUnitResponseIntensity (rho : ℂ) : ℝ :=
  Complex.normSq (d4ThetaHawkingSelfDualUnitResponse rho)

/-- Positive multiplier relating horizontal divisor displacement to response-intensity change. -/
def d4ThetaHawkingSelfDualResponseSusceptibility (rho : ℂ) : ℝ :=
  let x := rho.re - 1 / 2
  let a := x ^ (2 : ℕ) + rho.im ^ (2 : ℕ) + 1 / 4
  let b := x ^ (2 : ℕ) + rho.im ^ (2 : ℕ) + 25 / 4
  5 * a ^ (2 : ℕ) + 2 * a * b + 5 * x ^ (2 : ℕ)

theorem d4ThetaHawkingSelfDualUnitResponseIntensity_eq (rho : ℂ) :
    d4ThetaHawkingSelfDualUnitResponseIntensity rho =
      ((rho.re ^ (2 : ℕ) + rho.im ^ (2 : ℕ)) ^ (2 : ℕ) *
        ((rho.re + 2) ^ (2 : ℕ) + rho.im ^ (2 : ℕ))) / 64 := by
  rw [d4ThetaHawkingSelfDualUnitResponseIntensity,
    d4ThetaHawkingSelfDualUnitResponse]
  simp [Complex.normSq_apply]
  ring

theorem d4ThetaHawkingSelfDualUnitResponseIntensity_conj (rho : ℂ) :
    d4ThetaHawkingSelfDualUnitResponseIntensity ((starRingEnd ℂ) rho) =
      d4ThetaHawkingSelfDualUnitResponseIntensity rho := by
  rw [d4ThetaHawkingSelfDualUnitResponseIntensity_eq,
    d4ThetaHawkingSelfDualUnitResponseIntensity_eq]
  simp

theorem d4ThetaHawkingSelfDualResponseSusceptibility_pos (rho : ℂ) :
    0 < d4ThetaHawkingSelfDualResponseSusceptibility rho := by
  rw [d4ThetaHawkingSelfDualResponseSusceptibility]
  positivity

/-- Exact signed variation under theta functional-equation reflection. -/
theorem d4ThetaHawkingSelfDualUnitResponseIntensity_sub_reflection (rho : ℂ) :
    d4ThetaHawkingSelfDualUnitResponseIntensity rho -
        d4ThetaHawkingSelfDualUnitResponseIntensity (1 - rho) =
      (rho.re - 1 / 2) *
        d4ThetaHawkingSelfDualResponseSusceptibility rho / 32 := by
  rw [d4ThetaHawkingSelfDualUnitResponseIntensity_eq,
    d4ThetaHawkingSelfDualUnitResponseIntensity_eq,
    d4ThetaHawkingSelfDualResponseSusceptibility]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
  ring

/-- Reflection preserves self-dual response intensity exactly on the critical line. -/
theorem d4ThetaHawkingSelfDualUnitResponseIntensity_reflection_eq_iff
    (rho : ℂ) :
    d4ThetaHawkingSelfDualUnitResponseIntensity rho =
        d4ThetaHawkingSelfDualUnitResponseIntensity (1 - rho) ↔
      rho.re = 1 / 2 := by
  rw [← sub_eq_zero, d4ThetaHawkingSelfDualUnitResponseIntensity_sub_reflection]
  have hsusc := d4ThetaHawkingSelfDualResponseSusceptibility_pos rho
  constructor
  · intro h
    rcases (div_eq_zero_iff).mp h with hnum | hden
    · rcases mul_eq_zero.mp hnum with htilt | hsusc0
      · linarith
      · exact False.elim (ne_of_gt hsusc hsusc0)
    · norm_num at hden
  · intro h
    rw [h]
    norm_num

/-- Response variation is oriented by the side of the critical line. -/
theorem d4ThetaHawkingSelfDualUnitResponseIntensity_sub_reflection_pos_iff
    (rho : ℂ) :
    0 < d4ThetaHawkingSelfDualUnitResponseIntensity rho -
        d4ThetaHawkingSelfDualUnitResponseIntensity (1 - rho) ↔
      1 / 2 < rho.re := by
  rw [d4ThetaHawkingSelfDualUnitResponseIntensity_sub_reflection]
  have hsusc := d4ThetaHawkingSelfDualResponseSusceptibility_pos rho
  constructor
  · intro h
    have hnum : 0 < (rho.re - 1 / 2) *
        d4ThetaHawkingSelfDualResponseSusceptibility rho := by
      have := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mp h
      simpa using this
    rcases mul_pos_iff.mp hnum with hpos | hneg
    · linarith [hpos.1]
    · exact False.elim (not_lt_of_ge hsusc.le hneg.2)
  · intro h
    exact div_pos (mul_pos (by linarith) hsusc) (by norm_num)

/-- The polynomial coefficient is the previously derived normalized Mellin carrier on Xi. -/
theorem d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_one_eq_unitResponse
    (q : XiZeroCopy) :
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 (xiSpectralPoint q) =
      d4ThetaHawkingSelfDualUnitResponse (q.1 : ℂ) := by
  rw [d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq,
    d4ThetaHawkingSelfDualUnitResponse_eq]
  ring

/-- Xi-supported response-intensity equality is exactly the critical-line condition. -/
theorem d4ThetaHawkingSelfDualXiResponseIntensity_reflection_eq_iff
    (q : XiZeroCopy) :
    d4ThetaHawkingSelfDualUnitResponseIntensity (q.1 : ℂ) =
        d4ThetaHawkingSelfDualUnitResponseIntensity (1 - (q.1 : ℂ)) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  exact d4ThetaHawkingSelfDualUnitResponseIntensity_reflection_eq_iff (q.1 : ℂ)

/-- Signed intensity change from Schwarz/CPT partner to functional-equation partner. -/
def d4ThetaHawkingSelfDualPartnerResponseIntensityDefect (q : XiZeroCopy) : ℝ :=
  d4ThetaHawkingSelfDualUnitResponseIntensity (q.1 : ℂ) -
    d4ThetaHawkingSelfDualUnitResponseIntensity (1 - (q.1 : ℂ))

theorem d4ThetaHawkingSelfDualPartnerResponseIntensityDefect_eq (q : XiZeroCopy) :
    d4ThetaHawkingSelfDualPartnerResponseIntensityDefect q =
      ((q.1 : ℂ).re - 1 / 2) *
        d4ThetaHawkingSelfDualResponseSusceptibility (q.1 : ℂ) / 32 := by
  exact d4ThetaHawkingSelfDualUnitResponseIntensity_sub_reflection (q.1 : ℂ)

theorem d4ThetaHawkingSelfDualPartnerResponseIntensityDefect_eq_zero_iff
    (q : XiZeroCopy) :
    d4ThetaHawkingSelfDualPartnerResponseIntensityDefect q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4ThetaHawkingSelfDualPartnerResponseIntensityDefect, sub_eq_zero]
  exact d4ThetaHawkingSelfDualUnitResponseIntensity_reflection_eq_iff (q.1 : ℂ)

/-- The defect is the difference of the actual normalized Xi-carrier intensities in the
Schwarz-conjugated and functional-equation-reflected sectors. -/
def d4ThetaHawkingSelfDualActualPartnerResponseIntensityDefect (q : XiZeroCopy) : ℝ :=
  Complex.normSq
      (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1
        (xiSpectralPoint (xiZeroCopyConjEquiv q))) -
    Complex.normSq
      (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)))

theorem d4ThetaHawkingSelfDualActualPartnerResponseIntensityDefect_eq
    (q : XiZeroCopy) :
    d4ThetaHawkingSelfDualActualPartnerResponseIntensityDefect q =
      d4ThetaHawkingSelfDualPartnerResponseIntensityDefect q := by
  rw [d4ThetaHawkingSelfDualActualPartnerResponseIntensityDefect,
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_one_eq_unitResponse,
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_one_eq_unitResponse,
    d4ThetaHawkingSelfDualPartnerResponseIntensityDefect]
  change d4ThetaHawkingSelfDualUnitResponseIntensity
      ((starRingEnd ℂ) (q.1 : ℂ)) -
        d4ThetaHawkingSelfDualUnitResponseIntensity (1 - (q.1 : ℂ)) = _
  rw [d4ThetaHawkingSelfDualUnitResponseIntensity_conj]

/-- Nonlinear response variation is a positive-susceptibility multiple of the exact
Birmingham--Mokhtari reflected-versus-conjugated QNM frequency variation. -/
theorem d4ThetaHawkingSelfDualPartnerResponseIntensityDefect_frequencyTransgression
    (n : ℕ) (q : XiZeroCopy) :
    (d4ThetaHawkingSelfDualPartnerResponseIntensityDefect q : ℂ) =
      (-Complex.I *
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n
              (xiSpectralPoint (xiZeroCopyReflectEquiv q)) -
            thetaCuspHawkingTopologicalBlackHoleQNMPlus n
              (xiSpectralPoint (xiZeroCopyConjEquiv q)))) *
        (d4ThetaHawkingSelfDualResponseSusceptibility (q.1 : ℂ) / 32 : ℝ) := by
  rw [d4ThetaHawkingSelfDualPartnerResponseIntensityDefect_eq,
    d4BMXiReflected_sub_conjugateQNMPlus_eq_tilt]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Equivalent thermal form: response variation measures deviation from canonical Hawking QNM
splitting, multiplied by the same strictly positive susceptibility. -/
theorem d4ThetaHawkingSelfDualPartnerResponseIntensityDefect_thermalTransgression
    (n : ℕ) (q : XiZeroCopy) :
    d4ThetaHawkingSelfDualPartnerResponseIntensityDefect q =
      -(thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting n
          (xiSpectralPoint q) - 1 / 2) *
        d4ThetaHawkingSelfDualResponseSusceptibility (q.1 : ℂ) / 32 := by
  rw [d4ThetaHawkingSelfDualPartnerResponseIntensityDefect_eq,
    thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting_eq]
  simp [xiSpectralPoint, Complex.mul_im]

end

end RHTower
