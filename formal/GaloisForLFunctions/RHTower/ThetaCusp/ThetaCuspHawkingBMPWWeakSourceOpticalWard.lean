import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalAngularWeakResponse
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint

/-!
# Source-normalized weak optical Ward identity for PW-B

Testing the actual finite-energy weak response against itself gives an exact
imaginary forcing-flux law. Combining the two physical branch parameters
produces the same centered Xi displacement as the fixed-grade PW imbalance.
The identity retains the complete forcing vector and response mass. It does
not identify this weak optical flux with the literal ordered CTP cap/lift
current, prove either response mass positive, or prove an all-divisor
extinction law.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMQuadraticMixedSource
noncomputable section
set_option autoImplicit false

/-- Actual finite-energy mass of one physical forced response. -/
def weakSourceMass (q : XiZeroCopy) (b : Bool) : ℝ :=
  ‖embedding (weakResponse q b)‖ ^ (2 : ℕ)

/-- Imaginary Hilbert pairing of the actual response with its full forcing. -/
def weakSourceFlux (q : XiZeroCopy) (b : Bool) : ℝ :=
  (inner ℂ (embedding (weakResponse q b)) (forcingVector q b)).im

/-- Exact optical identity on each of the two source-fixed weak responses. -/
theorem weakSourceFlux_eq (q : XiZeroCopy) (b : Bool) :
    weakSourceFlux q b = -(parameter q b).im * weakSourceMass q b := by
  let h := weakResponse q b
  have he := weakResponse_spec q b h
  have hh : (inner ℂ h h).im = 0 := by
    simpa using! inner_self_im (𝕜 := ℂ) h
  have hj : (inner ℂ (embedding h) (embedding h)).im = 0 := by
    simpa using! inner_self_im (𝕜 := ℂ) (embedding h)
  have hjr : (inner ℂ (embedding h) (embedding h)).re = ‖embedding h‖ ^ (2 : ℕ) := by
    simpa using! inner_self_eq_norm_sq (𝕜 := ℂ) (embedding h)
  have hi := congrArg Complex.im he
  rw [Complex.sub_im, Complex.mul_im, Complex.neg_im, hh, hj, hjr] at hi
  simp only [Complex.sub_im, Complex.one_im, zero_sub, mul_zero, zero_add] at hi
  dsimp [weakSourceFlux, weakSourceMass, h]
  linarith

/-- Cross-multiplication removes branch-dependent response masses without
assuming either is nonzero. The surviving coefficient is exact, not fitted. -/
theorem weakSourceFlux_pair (q : XiZeroCopy) :
    weakSourceFlux q true * weakSourceMass q false +
        weakSourceFlux q false * weakSourceMass q true =
      -16 * (((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) *
        (weakSourceMass q true * weakSourceMass q false) := by
  have hp := D4BMQuadraticMixedSource.physical_parameter_im (q.1 : ℂ)
  have ht : (parameter q true).im =
      (8 * (q.1 : ℂ).re - 10) * (q.1 : ℂ).im := by
    exact hp.1
  have hf : (parameter q false).im =
      (8 * (q.1 : ℂ).re + 2) * (q.1 : ℂ).im := by
    exact hp.2
  rw [weakSourceFlux_eq, weakSourceFlux_eq, ht, hf]
  ring

/-- Fixed-grade PW partner imbalance equals the crossed source optical flux
after the forced ordinate/response-mass normalization. No denominator or
positivity premise is introduced. -/
theorem pwImbalance_weakSourceFlux_cross (q : XiZeroCopy) (k : ℕ) :
    4 * (k + 1 : ℝ) ^ (2 : ℕ) *
        ((schwarzschildParikhWilczekFirstWindingBorelGrowthRatio (q.1 : ℂ) k).re -
          (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio (1 - (q.1 : ℂ)) k).re) *
        (q.1 : ℂ).im *
          (weakSourceMass q true * weakSourceMass q false) =
      -(2 * (k : ℝ) + 1) *
        (weakSourceFlux q true * weakSourceMass q false +
          weakSourceFlux q false * weakSourceMass q true) := by
  rw [schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_re_sub_partner,
    weakSourceFlux_pair]
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end
end RHTower.D4BMModularCore
