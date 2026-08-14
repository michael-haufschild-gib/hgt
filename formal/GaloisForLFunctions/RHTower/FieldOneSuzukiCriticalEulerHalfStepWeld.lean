import GaloisForLFunctions.RHTower.FieldOneFiniteStageThetaSourceNormalization
import GaloisForLFunctions.RHTower.SuzukiCriticalApertureQuarterShiftCurrent
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinDeterminantTransgression

/-!
# Field-one/Suzuki critical Euler half-step weld

The Suzuki critical quarter-shift is the spectral multiplier of a literal
square-root dilation of the field-one Euler step. This module retains both
reflection orientations, source prime labels, divisor depth, literal
even-Schwartz action, and the horizontal Gamma Bockstein energy imbalance.
-/

noncomputable section

open MeasureTheory

namespace RHTower

/-- Quarter-density coefficient underlying the critical wall field. -/
def suzukiCriticalEulerHalfCoefficient (p : Nat.Primes) : ℝ :=
  Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ))

theorem suzukiCriticalEulerHalfCoefficient_pos (p : Nat.Primes) :
    0 < suzukiCriticalEulerHalfCoefficient p := Real.exp_pos _

theorem sq_suzukiCriticalEulerHalfCoefficient (p : Nat.Primes) :
    suzukiCriticalEulerHalfCoefficient p ^ 2 = (Real.sqrt (p : ℝ))⁻¹ := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hsqrt : Real.sqrt (p : ℝ) = Real.exp (Real.log (p : ℝ) / 2) := by
    rw [← Real.log_sqrt hp.le, Real.exp_log (Real.sqrt_pos.2 hp)]
  rw [suzukiCriticalEulerHalfCoefficient, pow_two, ← Real.exp_add, hsqrt,
    ← Real.exp_neg]
  congr 1
  ring

theorem suzukiCriticalEulerHalfCoefficient_mul_mellinCharacter
    (p : Nat.Primes) (t : ℝ) :
    (suzukiCriticalEulerHalfCoefficient p : ℂ) *
        MellinL2.mellinCharacter (Real.sqrt (p : ℝ)) t =
      suzukiCriticalGammaDepthRatio t p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [suzukiCriticalEulerHalfCoefficient, suzukiCriticalGammaDepthRatio,
    MellinL2.mellinCharacter, Complex.ofReal_exp, ← Complex.exp_add,
    Real.log_sqrt hp.le]
  push_cast
  ring
  rw [Complex.exp_add]

theorem suzukiCriticalEulerHalfCoefficient_mul_mellinCharacter_inv
    (p : Nat.Primes) (t : ℝ) :
    (suzukiCriticalEulerHalfCoefficient p : ℂ) *
        (MellinL2.mellinCharacter (Real.sqrt (p : ℝ)) t)⁻¹ =
      suzukiCriticalGammaDepthRatio (-t) p := by
  rw [← suzukiCriticalEulerHalfCoefficient_mul_mellinCharacter p (-t)]
  congr 1
  unfold MellinL2.mellinCharacter
  rw [show Real.log (Real.sqrt (p : ℝ)) * -t =
      -(Real.log (Real.sqrt (p : ℝ)) * t) by ring]
  push_cast
  rw [show -(↑(Real.log (Real.sqrt (p : ℝ))) * ↑t) * Complex.I =
      -(↑(Real.log (Real.sqrt (p : ℝ))) * ↑t * Complex.I) by ring,
    Complex.exp_neg]

/-- Forward critical half-step. Its spectral multiplier is the Suzuki `+t` ratio. -/
def suzukiCriticalEulerForwardHalfStep (p : Nat.Primes) :
    evenSubspace →L[ℂ] evenSubspace :=
  (suzukiCriticalEulerHalfCoefficient p : ℂ) •
    (evenDilationUnitary (Real.sqrt (p : ℝ))
      (Real.sqrt_pos.2 (by exact_mod_cast p.prop.pos)) :
        evenSubspace →L[ℂ] evenSubspace)

/-- Reflected critical half-step. Its spectral multiplier is the Suzuki `-t` ratio. -/
def suzukiCriticalEulerBackwardHalfStep (p : Nat.Primes) :
    evenSubspace →L[ℂ] evenSubspace :=
  (suzukiCriticalEulerHalfCoefficient p : ℂ) •
    ((evenDilationUnitary (Real.sqrt (p : ℝ))
      (Real.sqrt_pos.2 (by exact_mod_cast p.prop.pos))).symm :
        evenSubspace →L[ℂ] evenSubspace)

/-- Geometric step deleted by the local Hardy--Titchmarsh Euler factor. -/
def evenPrimeEulerGeometricStep (p : Nat.Primes) :
    evenSubspace →L[ℂ] evenSubspace :=
  ((Real.sqrt (p : ℝ) : ℂ)⁻¹) •
    ((evenDilationUnitary (p : ℝ) (by exact_mod_cast p.prop.pos)).symm :
      evenSubspace →L[ℂ] evenSubspace)

/-- Adjoint geometric Euler step. -/
def evenPrimeEulerGeometricAdjointStep (p : Nat.Primes) :
    evenSubspace →L[ℂ] evenSubspace :=
  ((Real.sqrt (p : ℝ) : ℂ)⁻¹) •
    (evenDilationUnitary (p : ℝ) (by exact_mod_cast p.prop.pos) :
      evenSubspace →L[ℂ] evenSubspace)

theorem evenPrimeLocalFactor_eq_one_sub_geometricStep (p : Nat.Primes) :
    evenPrimeLocalFactor (p : ℝ) (by exact_mod_cast p.prop.one_lt) =
      1 - evenPrimeEulerGeometricStep p := by
  rfl

theorem suzukiCriticalEulerBackwardHalfStep_sq (p : Nat.Primes) :
    suzukiCriticalEulerBackwardHalfStep p ^ 2 = evenPrimeEulerGeometricStep p := by
  let r : ℝ := Real.sqrt (p : ℝ)
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hr : 0 < r := Real.sqrt_pos.2 hp
  have hr2 : r * r = (p : ℝ) := Real.mul_self_sqrt hp.le
  have hinv2 : r⁻¹ * r⁻¹ = ((p : ℝ))⁻¹ := by rw [← mul_inv, hr2]
  have hsymm :
      ((evenDilationUnitary r hr).symm : evenSubspace →L[ℂ] evenSubspace) =
        evenDilationCLM r⁻¹ (inv_pos.mpr hr) := by rfl
  rw [suzukiCriticalEulerBackwardHalfStep, evenPrimeEulerGeometricStep]
  change (((suzukiCriticalEulerHalfCoefficient p : ℂ) •
      ((evenDilationUnitary r hr).symm : evenSubspace →L[ℂ] evenSubspace)) ^ 2) = _
  rw [hsymm, pow_two, smul_mul_smul_comm, evenDilationCLM_mul]
  have hc :
      (suzukiCriticalEulerHalfCoefficient p : ℂ) *
          (suzukiCriticalEulerHalfCoefficient p : ℂ) =
        (Real.sqrt (p : ℝ) : ℂ)⁻¹ := by
    norm_cast
    simpa [pow_two] using sq_suzukiCriticalEulerHalfCoefficient p
  rw [hc]
  apply congrArg (fun T : evenSubspace →L[ℂ] evenSubspace =>
    (Real.sqrt (p : ℝ) : ℂ)⁻¹ • T)
  rw [evenDilationCLM_congr (mul_pos (inv_pos.mpr hr) (inv_pos.mpr hr)) hinv2]
  rfl

theorem suzukiCriticalEulerForwardHalfStep_sq (p : Nat.Primes) :
    suzukiCriticalEulerForwardHalfStep p ^ 2 =
      evenPrimeEulerGeometricAdjointStep p := by
  let r : ℝ := Real.sqrt (p : ℝ)
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hr : 0 < r := Real.sqrt_pos.2 hp
  have hr2 : r * r = (p : ℝ) := Real.mul_self_sqrt hp.le
  rw [suzukiCriticalEulerForwardHalfStep, evenPrimeEulerGeometricAdjointStep]
  change (((suzukiCriticalEulerHalfCoefficient p : ℂ) •
      (evenDilationUnitary r hr : evenSubspace →L[ℂ] evenSubspace)) ^ 2) = _
  change (((suzukiCriticalEulerHalfCoefficient p : ℂ) •
      evenDilationCLM r hr) ^ 2) = _
  rw [pow_two]
  calc
    ((suzukiCriticalEulerHalfCoefficient p : ℂ) • evenDilationCLM r hr) *
          ((suzukiCriticalEulerHalfCoefficient p : ℂ) • evenDilationCLM r hr) =
        ((suzukiCriticalEulerHalfCoefficient p : ℂ) *
          (suzukiCriticalEulerHalfCoefficient p : ℂ)) •
            (evenDilationCLM r hr * evenDilationCLM r hr) := by
      apply ContinuousLinearMap.ext
      intro x
      change (suzukiCriticalEulerHalfCoefficient p : ℂ) •
          evenDilationCLM r hr
            ((suzukiCriticalEulerHalfCoefficient p : ℂ) •
              evenDilationCLM r hr x) =
        ((suzukiCriticalEulerHalfCoefficient p : ℂ) *
          (suzukiCriticalEulerHalfCoefficient p : ℂ)) •
            evenDilationCLM r hr (evenDilationCLM r hr x)
      rw [map_smul, smul_smul]
    _ = ((suzukiCriticalEulerHalfCoefficient p : ℂ) *
          (suzukiCriticalEulerHalfCoefficient p : ℂ)) •
            evenDilationCLM (r * r) (mul_pos hr hr) := by
      rw [evenDilationCLM_mul]
    _ = _ := by
      have hc :
          (suzukiCriticalEulerHalfCoefficient p : ℂ) *
              (suzukiCriticalEulerHalfCoefficient p : ℂ) =
            (Real.sqrt (p : ℝ) : ℂ)⁻¹ := by
        norm_cast
        simpa [pow_two] using sq_suzukiCriticalEulerHalfCoefficient p
      rw [hc]
      apply congrArg (fun T : evenSubspace →L[ℂ] evenSubspace =>
        (Real.sqrt (p : ℝ) : ℂ)⁻¹ • T)
      rw [evenDilationCLM_congr (mul_pos hr hr) hr2]
      rfl

theorem evenPrimeLocalFactor_eq_reflected_halfStep_factorization (p : Nat.Primes) :
    evenPrimeLocalFactor (p : ℝ) (by exact_mod_cast p.prop.one_lt) =
      (1 - suzukiCriticalEulerBackwardHalfStep p) *
        (1 + suzukiCriticalEulerBackwardHalfStep p) := by
  rw [evenPrimeLocalFactor_eq_one_sub_geometricStep,
    ← suzukiCriticalEulerBackwardHalfStep_sq]
  simp only [pow_two, sub_mul, mul_add, one_mul, mul_one]
  abel

theorem evenPrimeLocalFactor_adjoint_eq_forward_halfStep_factorization
    (p : Nat.Primes) :
    ContinuousLinearMap.adjoint
        (evenPrimeLocalFactor (p : ℝ) (by exact_mod_cast p.prop.one_lt)) =
      (1 - suzukiCriticalEulerForwardHalfStep p) *
        (1 + suzukiCriticalEulerForwardHalfStep p) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hcoeff :
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ =
        (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) := by
    norm_cast
  rw [evenPrimeLocalFactor, hcoeff]
  change ContinuousLinearMap.adjoint
      (1 - (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) •
        ((evenDilationUnitary (p : ℝ) (zero_lt_one.trans hp)).symm :
          evenSubspace →L[ℂ] evenSubspace)) = _
  rw [adjoint_one_sub_real_smul_unitary_symm
    (evenDilationUnitary (p : ℝ) (zero_lt_one.trans hp))
    (Real.sqrt (p : ℝ))⁻¹]
  rw [← hcoeff]
  change 1 - evenPrimeEulerGeometricAdjointStep p = _
  rw [← suzukiCriticalEulerForwardHalfStep_sq]
  simp only [pow_two, sub_mul, mul_add, one_mul, mul_one]
  abel

theorem evenPositiveEulerOperator_eq_critical_fourHalfSteps (p : Nat.Primes) :
    evenPositiveEulerOperator (p : ℝ) (by exact_mod_cast p.prop.one_lt) =
      ((1 - suzukiCriticalEulerForwardHalfStep p) *
          (1 + suzukiCriticalEulerForwardHalfStep p)) *
        ((1 - suzukiCriticalEulerBackwardHalfStep p) *
          (1 + suzukiCriticalEulerBackwardHalfStep p)) := by
  rw [← evenPrimeLocalFactor_adjoint_comp_self,
    evenPrimeLocalFactor_adjoint_eq_forward_halfStep_factorization,
    evenPrimeLocalFactor_eq_reflected_halfStep_factorization]

theorem suzukiCriticalEulerBackwardHalfStep_ccmEvenSchwartzSource
    (p : Nat.Primes) (f : SchwartzMap ℝ ℂ) :
    suzukiCriticalEulerBackwardHalfStep p (ccmEvenSchwartzSource f) =
      (suzukiCriticalEulerHalfCoefficient p : ℂ) •
        ccmEvenSchwartzSource
          (ccmNormalizedSchwartzDilation (Real.sqrt (p : ℝ))⁻¹
            (inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast p.prop.pos))) f) := by
  let r : ℝ := Real.sqrt (p : ℝ)
  have hr : 0 < r := Real.sqrt_pos.2 (by exact_mod_cast p.prop.pos)
  rw [ccmEvenSchwartzSource_normalizedDilation]
  rfl

theorem norm_suzukiCriticalEulerForwardHalfStep_apply
    (p : Nat.Primes) (x : evenSubspace) :
    ‖suzukiCriticalEulerForwardHalfStep p x‖ =
      suzukiCriticalEulerHalfCoefficient p * ‖x‖ := by
  let U := evenDilationUnitary (Real.sqrt (p : ℝ))
    (Real.sqrt_pos.2 (by exact_mod_cast p.prop.pos))
  rw [suzukiCriticalEulerForwardHalfStep, smul_apply, norm_smul]
  change ‖(suzukiCriticalEulerHalfCoefficient p : ℂ)‖ * ‖U x‖ = _
  rw [U.norm_map, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (suzukiCriticalEulerHalfCoefficient_pos p)]

theorem norm_suzukiCriticalEulerBackwardHalfStep_apply
    (p : Nat.Primes) (x : evenSubspace) :
    ‖suzukiCriticalEulerBackwardHalfStep p x‖ =
      suzukiCriticalEulerHalfCoefficient p * ‖x‖ := by
  let U := (evenDilationUnitary (Real.sqrt (p : ℝ))
    (Real.sqrt_pos.2 (by exact_mod_cast p.prop.pos))).symm
  rw [suzukiCriticalEulerBackwardHalfStep, smul_apply, norm_smul]
  change ‖(suzukiCriticalEulerHalfCoefficient p : ℂ)‖ * ‖U x‖ = _
  rw [U.norm_map, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (suzukiCriticalEulerHalfCoefficient_pos p)]

/-- Before horizontal dressing, the two critical orientations have equal
source energy on every vector. -/
theorem norm_suzukiCriticalEulerForwardHalfStep_apply_eq_backward
    (p : Nat.Primes) (x : evenSubspace) :
    ‖suzukiCriticalEulerForwardHalfStep p x‖ =
      ‖suzukiCriticalEulerBackwardHalfStep p x‖ := by
  rw [norm_suzukiCriticalEulerForwardHalfStep_apply,
    norm_suzukiCriticalEulerBackwardHalfStep_apply]

theorem suzukiCriticalEulerHalfCoefficient_pow_four (p : Nat.Primes) :
    suzukiCriticalEulerHalfCoefficient p ^ 4 = ((p : ℝ))⁻¹ := by
  calc
    suzukiCriticalEulerHalfCoefficient p ^ 4 =
        (suzukiCriticalEulerHalfCoefficient p ^ 2) ^ 2 := by ring
    _ = ((Real.sqrt (p : ℝ))⁻¹) ^ 2 := by
      rw [sq_suzukiCriticalEulerHalfCoefficient]
    _ = ((p : ℝ))⁻¹ := by
      rw [pow_two, ← mul_inv, Real.mul_self_sqrt]
      exact_mod_cast p.prop.pos.le

/-- Horizontal nonunitary dressing of the forward quarter-shift response. -/
def suzukiCriticalEulerHorizontalForwardResponse
    (t : ℝ) (p : Nat.Primes) (x : evenSubspace) : evenSubspace :=
  (((p : ℝ) ^ (t / 2) : ℝ) : ℂ) •
    suzukiCriticalEulerForwardHalfStep p x

/-- Horizontal nonunitary dressing of the reflected quarter-shift response. -/
def suzukiCriticalEulerHorizontalBackwardResponse
    (t : ℝ) (p : Nat.Primes) (x : evenSubspace) : evenSubspace :=
  (((p : ℝ) ^ (-t / 2) : ℝ) : ℂ) •
    suzukiCriticalEulerBackwardHalfStep p x

theorem prime_rpow_half_sq (t : ℝ) (p : Nat.Primes) :
    ((p : ℝ) ^ (t / 2)) ^ 2 = (p : ℝ) ^ t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact_mod_cast p.prop.pos.le)]
  congr 1
  ring

theorem norm_suzukiCriticalEulerHorizontalForwardResponse
    (t : ℝ) (p : Nat.Primes) (x : evenSubspace) :
    ‖suzukiCriticalEulerHorizontalForwardResponse t p x‖ =
      (p : ℝ) ^ (t / 2) *
        suzukiCriticalEulerHalfCoefficient p * ‖x‖ := by
  rw [suzukiCriticalEulerHorizontalForwardResponse, norm_smul,
    norm_suzukiCriticalEulerForwardHalfStep_apply,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _)]
  ring

theorem norm_suzukiCriticalEulerHorizontalBackwardResponse
    (t : ℝ) (p : Nat.Primes) (x : evenSubspace) :
    ‖suzukiCriticalEulerHorizontalBackwardResponse t p x‖ =
      (p : ℝ) ^ (-t / 2) *
        suzukiCriticalEulerHalfCoefficient p * ‖x‖ := by
  rw [suzukiCriticalEulerHorizontalBackwardResponse, norm_smul,
    norm_suzukiCriticalEulerBackwardHalfStep_apply,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _)]
  ring

/-- The Gamma Bockstein is exactly the Fisher-weighted energy imbalance of
the two horizontally dressed quarter-shift responses on the same carrier. -/
theorem primeGammaCofinalBocksteinCoefficient_mul_critical_energy
    (t : ℝ) (p : Nat.Primes) (x : evenSubspace) :
    primeGammaCofinalBocksteinCoefficient t p *
        (suzukiCriticalEulerHalfCoefficient p ^ 2 * ‖x‖ ^ 2) =
      primeActivationOccupancyFisherDensity p *
        (‖suzukiCriticalEulerHorizontalBackwardResponse t p x‖ ^ 2 -
          ‖suzukiCriticalEulerHorizontalForwardResponse t p x‖ ^ 2) := by
  rw [primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist,
    norm_suzukiCriticalEulerHorizontalBackwardResponse,
    norm_suzukiCriticalEulerHorizontalForwardResponse,
    mul_pow, mul_pow, mul_pow, mul_pow,
    prime_rpow_half_sq, prime_rpow_half_sq]
  ring

/-- Same-fibre equality of the dressed responses is exactly neutral
horizontal grade; the critical half-step weld is a faithful detector, not by
itself an annihilating producer. -/
theorem norm_horizontalForwardResponse_eq_backward_iff
    (t : ℝ) (p : Nat.Primes) {x : evenSubspace} (hx : x ≠ 0) :
    ‖suzukiCriticalEulerHorizontalForwardResponse t p x‖ =
        ‖suzukiCriticalEulerHorizontalBackwardResponse t p x‖ ↔
      t = 0 := by
  constructor
  · intro henergy
    have hzero :
        primeGammaCofinalBocksteinCoefficient t p *
            (suzukiCriticalEulerHalfCoefficient p ^ 2 * ‖x‖ ^ 2) = 0 := by
      rw [primeGammaCofinalBocksteinCoefficient_mul_critical_energy,
        henergy, sub_self, mul_zero]
    have hmass :
        suzukiCriticalEulerHalfCoefficient p ^ 2 * ‖x‖ ^ 2 ≠ 0 := by
      apply mul_ne_zero
      · exact pow_ne_zero _ (ne_of_gt (suzukiCriticalEulerHalfCoefficient_pos p))
      · exact pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    exact (primeGammaCofinalBocksteinCoefficient_eq_zero_iff t p).mp
      ((mul_eq_zero.mp hzero).resolve_right hmass)
  · rintro rfl
    rw [norm_suzukiCriticalEulerHorizontalForwardResponse,
      norm_suzukiCriticalEulerHorizontalBackwardResponse]
    simp

theorem unitaryPush_suzukiCriticalEulerForwardHalfStep (p : Nat.Primes) :
    unitaryPush archimedeanDualHardyTitchmarshUnitary
        (suzukiCriticalEulerForwardHalfStep p) =
      (suzukiCriticalEulerHalfCoefficient p : ℂ) •
        (weightedMellinCharacterMulUnitary (Real.sqrt (p : ℝ)) :
          ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) := by
  rw [suzukiCriticalEulerForwardHalfStep, unitaryPush_smul,
    unitaryPush_archimedean_evenDilation]

theorem unitaryPush_suzukiCriticalEulerBackwardHalfStep (p : Nat.Primes) :
    unitaryPush archimedeanDualHardyTitchmarshUnitary
        (suzukiCriticalEulerBackwardHalfStep p) =
      (suzukiCriticalEulerHalfCoefficient p : ℂ) •
        ((weightedMellinCharacterMulUnitary (Real.sqrt (p : ℝ))).symm :
          ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) := by
  rw [suzukiCriticalEulerBackwardHalfStep, unitaryPush_smul,
    unitaryPush_archimedean_evenDilation_symm]

theorem unitaryPush_suzukiCriticalEulerForwardHalfStep_ae
    (p : Nat.Primes) (g : ArchimedeanWeightedL2) :
    unitaryPush archimedeanDualHardyTitchmarshUnitary
        (suzukiCriticalEulerForwardHalfStep p) g =ᵐ[archimedeanWeightedMeasure]
      fun t => suzukiCriticalGammaDepthRatio t p * g t := by
  rw [unitaryPush_suzukiCriticalEulerForwardHalfStep]
  change ((suzukiCriticalEulerHalfCoefficient p : ℂ) •
      (weightedMellinCharacterMulUnitary (Real.sqrt (p : ℝ)) g) :
        ArchimedeanWeightedL2) =ᵐ[archimedeanWeightedMeasure] _
  filter_upwards [Lp.coeFn_smul (suzukiCriticalEulerHalfCoefficient p : ℂ)
      (weightedMellinCharacterMulUnitary (Real.sqrt (p : ℝ)) g),
    weightedMellinCharacterMulUnitary_ae (Real.sqrt (p : ℝ)) g] with t hsmul hphase
  rw [hsmul]
  change (suzukiCriticalEulerHalfCoefficient p : ℂ) *
      (weightedMellinCharacterMulUnitary (Real.sqrt (p : ℝ)) g) t = _
  rw [hphase, ← mul_assoc,
    suzukiCriticalEulerHalfCoefficient_mul_mellinCharacter]

theorem unitaryPush_suzukiCriticalEulerBackwardHalfStep_ae
    (p : Nat.Primes) (g : ArchimedeanWeightedL2) :
    unitaryPush archimedeanDualHardyTitchmarshUnitary
        (suzukiCriticalEulerBackwardHalfStep p) g =ᵐ[archimedeanWeightedMeasure]
      fun t => suzukiCriticalGammaDepthRatio (-t) p * g t := by
  rw [unitaryPush_suzukiCriticalEulerBackwardHalfStep]
  change ((suzukiCriticalEulerHalfCoefficient p : ℂ) •
      ((weightedMellinCharacterMulUnitary (Real.sqrt (p : ℝ))).symm g) :
        ArchimedeanWeightedL2) =ᵐ[archimedeanWeightedMeasure] _
  filter_upwards [Lp.coeFn_smul (suzukiCriticalEulerHalfCoefficient p : ℂ)
      ((weightedMellinCharacterMulUnitary (Real.sqrt (p : ℝ))).symm g),
    weightedMellinCharacterMulUnitary_symm_ae (Real.sqrt (p : ℝ)) g]
      with t hsmul hphase
  rw [hsmul]
  change (suzukiCriticalEulerHalfCoefficient p : ℂ) *
      ((weightedMellinCharacterMulUnitary (Real.sqrt (p : ℝ))).symm g) t = _
  rw [hphase, ← mul_assoc,
    suzukiCriticalEulerHalfCoefficient_mul_mellinCharacter_inv]

theorem suzukiCriticalEulerHalfCoefficient_lt_one (p : Nat.Primes) :
    suzukiCriticalEulerHalfCoefficient p < 1 := by
  rw [suzukiCriticalEulerHalfCoefficient, Real.exp_lt_one_iff]
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  nlinarith

theorem norm_suzukiCriticalEulerForwardHalfStep_le (p : Nat.Primes) :
    ‖suzukiCriticalEulerForwardHalfStep p‖ ≤
      suzukiCriticalEulerHalfCoefficient p := by
  let U := evenDilationUnitary (Real.sqrt (p : ℝ))
    (Real.sqrt_pos.2 (by exact_mod_cast p.prop.pos))
  have hU : ‖(U : evenSubspace →L[ℂ] evenSubspace)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖U x‖ ≤ 1 * ‖x‖
    rw [U.norm_map]
    simp
  rw [suzukiCriticalEulerForwardHalfStep]
  calc
    ‖(suzukiCriticalEulerHalfCoefficient p : ℂ) •
        (U : evenSubspace →L[ℂ] evenSubspace)‖ ≤
        ‖(suzukiCriticalEulerHalfCoefficient p : ℂ)‖ *
          ‖(U : evenSubspace →L[ℂ] evenSubspace)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖(suzukiCriticalEulerHalfCoefficient p : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left hU (norm_nonneg _)
    _ = suzukiCriticalEulerHalfCoefficient p := by
      rw [mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (suzukiCriticalEulerHalfCoefficient_pos p)]

theorem norm_suzukiCriticalEulerBackwardHalfStep_le (p : Nat.Primes) :
    ‖suzukiCriticalEulerBackwardHalfStep p‖ ≤
      suzukiCriticalEulerHalfCoefficient p := by
  let U := (evenDilationUnitary (Real.sqrt (p : ℝ))
    (Real.sqrt_pos.2 (by exact_mod_cast p.prop.pos))).symm
  have hU : ‖(U : evenSubspace →L[ℂ] evenSubspace)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖U x‖ ≤ 1 * ‖x‖
    rw [U.norm_map]
    simp
  rw [suzukiCriticalEulerBackwardHalfStep]
  calc
    ‖(suzukiCriticalEulerHalfCoefficient p : ℂ) •
        (U : evenSubspace →L[ℂ] evenSubspace)‖ ≤
        ‖(suzukiCriticalEulerHalfCoefficient p : ℂ)‖ *
          ‖(U : evenSubspace →L[ℂ] evenSubspace)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖(suzukiCriticalEulerHalfCoefficient p : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left hU (norm_nonneg _)
    _ = suzukiCriticalEulerHalfCoefficient p := by
      rw [mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (suzukiCriticalEulerHalfCoefficient_pos p)]

theorem norm_suzukiCriticalEulerForwardHalfStep_lt_one (p : Nat.Primes) :
    ‖suzukiCriticalEulerForwardHalfStep p‖ < 1 := by
  exact lt_of_le_of_lt (norm_suzukiCriticalEulerForwardHalfStep_le p)
    (suzukiCriticalEulerHalfCoefficient_lt_one p)

theorem norm_suzukiCriticalEulerBackwardHalfStep_lt_one (p : Nat.Primes) :
    ‖suzukiCriticalEulerBackwardHalfStep p‖ < 1 := by
  exact lt_of_le_of_lt (norm_suzukiCriticalEulerBackwardHalfStep_le p)
    (suzukiCriticalEulerHalfCoefficient_lt_one p)

theorem isUnit_one_sub_suzukiCriticalEulerForwardHalfStep (p : Nat.Primes) :
    IsUnit (1 - suzukiCriticalEulerForwardHalfStep p) :=
  isUnit_one_sub_of_norm_lt_one (x := suzukiCriticalEulerForwardHalfStep p)
    (norm_suzukiCriticalEulerForwardHalfStep_lt_one p)

theorem isUnit_one_add_suzukiCriticalEulerForwardHalfStep (p : Nat.Primes) :
    IsUnit (1 + suzukiCriticalEulerForwardHalfStep p) := by
  have hn : ‖-suzukiCriticalEulerForwardHalfStep p‖ < 1 := by
    rw [ContinuousLinearMap.opNorm_neg]
    exact norm_suzukiCriticalEulerForwardHalfStep_lt_one p
  simpa only [sub_neg_eq_add] using
    (isUnit_one_sub_of_norm_lt_one
      (x := -suzukiCriticalEulerForwardHalfStep p) hn)

theorem isUnit_one_sub_suzukiCriticalEulerBackwardHalfStep (p : Nat.Primes) :
    IsUnit (1 - suzukiCriticalEulerBackwardHalfStep p) :=
  isUnit_one_sub_of_norm_lt_one (x := suzukiCriticalEulerBackwardHalfStep p)
    (norm_suzukiCriticalEulerBackwardHalfStep_lt_one p)

theorem isUnit_one_add_suzukiCriticalEulerBackwardHalfStep (p : Nat.Primes) :
    IsUnit (1 + suzukiCriticalEulerBackwardHalfStep p) := by
  have hn : ‖-suzukiCriticalEulerBackwardHalfStep p‖ < 1 := by
    rw [ContinuousLinearMap.opNorm_neg]
    exact norm_suzukiCriticalEulerBackwardHalfStep_lt_one p
  simpa only [sub_neg_eq_add] using
    (isUnit_one_sub_of_norm_lt_one
      (x := -suzukiCriticalEulerBackwardHalfStep p) hn)

/-- The four critical quarter-shift factors are literal units, not merely a
formal algebraic splitting of the positive Euler Gram. -/
theorem suzukiCriticalEuler_fourHalfStep_isUnit (p : Nat.Primes) :
    IsUnit (1 - suzukiCriticalEulerForwardHalfStep p) ∧
    IsUnit (1 + suzukiCriticalEulerForwardHalfStep p) ∧
    IsUnit (1 - suzukiCriticalEulerBackwardHalfStep p) ∧
    IsUnit (1 + suzukiCriticalEulerBackwardHalfStep p) :=
  ⟨isUnit_one_sub_suzukiCriticalEulerForwardHalfStep p,
    isUnit_one_add_suzukiCriticalEulerForwardHalfStep p,
    isUnit_one_sub_suzukiCriticalEulerBackwardHalfStep p,
    isUnit_one_add_suzukiCriticalEulerBackwardHalfStep p⟩

/-- Even half-step depth retains the exact divisor multiplicity `e`. -/
theorem suzukiCriticalEulerBackwardHalfStep_even_pow
    (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalEulerBackwardHalfStep p ^ (2 * e) =
      evenPrimeEulerGeometricStep p ^ e := by
  rw [pow_mul, suzukiCriticalEulerBackwardHalfStep_sq]

/-- The reflected orientation has the same coefficient-faithful depth law. -/
theorem suzukiCriticalEulerForwardHalfStep_even_pow
    (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalEulerForwardHalfStep p ^ (2 * e) =
      evenPrimeEulerGeometricAdjointStep p ^ e := by
  rw [pow_mul, suzukiCriticalEulerForwardHalfStep_sq]

end RHTower

namespace GaloisForLFunctions.RHTower

open IsDedekindDomain

/-- The place label determines the prime half-step without forgetting the
source finite place. -/
def fieldOneFiniteStageThetaEulerPrime
    {S : Finset (HeightOneSpectrum ℤ)} (v : ↥S) : Nat.Primes :=
  ⟨fieldOneFinitePlacePrime v.1, fieldOneFinitePlacePrime_prime v.1⟩

/-- One literal field-one Euler term is exactly the product of its two
reflected Suzuki quarter-shift transports. -/
theorem fieldOneFiniteStageThetaEulerTerm_eq_critical_reflected_halfSteps
    (S : Finset (HeightOneSpectrum ℤ)) (v : ↥S) :
    fieldOneFiniteStageThetaEulerTerm S v =
      (1 - _root_.RHTower.suzukiCriticalEulerBackwardHalfStep
        (fieldOneFiniteStageThetaEulerPrime v)) *
      (1 + _root_.RHTower.suzukiCriticalEulerBackwardHalfStep
        (fieldOneFiniteStageThetaEulerPrime v)) := by
  unfold fieldOneFiniteStageThetaEulerTerm fieldOneFiniteStageThetaEulerPrime
  exact _root_.RHTower.evenPrimeLocalFactor_eq_reflected_halfStep_factorization _

/-- Coefficient-faithful source action of the place-labelled square-root
factorization on the literal even-Schwartz carrier. -/
theorem fieldOneFiniteStageThetaEulerTerm_ccmEvenSchwartzSource_eq_critical_halfSteps
    (S : Finset (HeightOneSpectrum ℤ)) (v : ↥S)
    (f : SchwartzMap ℝ ℂ) :
    fieldOneFiniteStageThetaEulerTerm S v
        (_root_.RHTower.ccmEvenSchwartzSource f) =
      ((1 - _root_.RHTower.suzukiCriticalEulerBackwardHalfStep
          (fieldOneFiniteStageThetaEulerPrime v)) *
        (1 + _root_.RHTower.suzukiCriticalEulerBackwardHalfStep
          (fieldOneFiniteStageThetaEulerPrime v)))
        (_root_.RHTower.ccmEvenSchwartzSource f) := by
  rw [fieldOneFiniteStageThetaEulerTerm_eq_critical_reflected_halfSteps]

end GaloisForLFunctions.RHTower
