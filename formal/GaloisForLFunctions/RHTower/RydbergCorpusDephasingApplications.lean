import GaloisForLFunctions.HTGeometry.RydbergClockDephasing
import GaloisForLFunctions.HTGeometry.RydbergSymmetricFrozenNoise
import GaloisForLFunctions.RHTower.SoninLogClockDephasing
import GaloisForLFunctions.RHTower.SoninLudersPinching
import GaloisForLFunctions.RHTower.PrimeHodgePoissonTwoChannelIntegralSplit

noncomputable section

namespace RHTower

/-- Sonin logarithmic-scattering projector dephasing is the same generator as the established
relational-clock double commutator, with exact factor `-1/8`. -/
theorem soninLogFourier_projectorDephasing_eq
    (X : SoninL2 →L[ℂ] SoninL2) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
        (HTGeometry.finiteCyclicGaugeAverage soninLogFourierScattering 2) X =
      -(8 : ℂ)⁻¹ • soninLogFourierDoubleCommutator X := by
  simpa only [soninLogFourierDoubleCommutator] using
    HTGeometry.projectorDephasingGenerator_finiteInvolutiveGaugeAverage_eq
      soninLogFourierScattering X soninLogFourierScattering_sq_eq_one

/-- Exact Sonin immunity criterion for the projector dissipator. -/
theorem soninLogFourier_projectorDephasing_eq_zero_iff
    (X : SoninL2 →L[ℂ] SoninL2) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
        (HTGeometry.finiteCyclicGaugeAverage soninLogFourierScattering 2) X = 0 ↔
      soninLogFourierScattering * X = X * soninLogFourierScattering := by
  exact HTGeometry.projectorDephasingGenerator_finiteInvolutiveGaugeAverage_eq_zero_iff
    soninLogFourierScattering X soninLogFourierScattering_sq_eq_one

/-- A Sonin observable already coarse-grained by the scattering clock is immune to the
associated projector dephasing. -/
theorem soninLogFourier_twirl_projectorDephasing_eq_zero
    (X : SoninL2 →L[ℂ] SoninL2) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
        (HTGeometry.finiteCyclicGaugeAverage soninLogFourierScattering 2)
        (soninLogFourierObservableTwirl X) = 0 := by
  rw [soninLogFourier_projectorDephasing_eq_zero_iff]
  simpa only [soninLogFourierObservableTwirl] using
    HTGeometry.finiteCyclicObservableTwirl_commutes
      soninLogFourierScattering X 2 soninLogFourierScattering_sq_eq_one

theorem primeHodgeHistoryTailProjection_isIdempotentElem (n : ℕ) :
    IsIdempotentElem (primeHodgeHistoryTailProjection n) := by
  change primeHodgeHistoryTailProjection n ∘L primeHodgeHistoryTailProjection n =
    primeHodgeHistoryTailProjection n
  exact primeHodgeHistoryTailProjection_idempotent n

/-- Prime-history tail cutoffs commute with the existing visibility multiplier. -/
theorem primeHodgeHistoryTailProjection_commutes_visibility (a : ℝ) (n : ℕ) :
    primeHodgeHistoryTailProjection n * primeHodgeVisibilityOp a =
      primeHodgeVisibilityOp a * primeHodgeHistoryTailProjection n := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext np
  simp only [mul_apply_eq_comp, primeHodgeHistoryTailProjection_apply,
    primeHodgeVisibilityOp_apply]
  ring

/-- Prime-history tail cutoffs commute with the existing contrast multiplier. -/
theorem primeHodgeHistoryTailProjection_commutes_contrast (a : ℝ) (n : ℕ) :
    primeHodgeHistoryTailProjection n * primeHodgeContrastOp a =
      primeHodgeContrastOp a * primeHodgeHistoryTailProjection n := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext np
  simp only [mul_apply_eq_comp, primeHodgeHistoryTailProjection_apply,
    primeHodgeContrastOp_apply]
  ring

/-- Existing prime-history visibility scores are immune to tail-sector dephasing. -/
theorem primeHodgeVisibilityOp_tailDephasing_eq_zero (a : ℝ) (n : ℕ) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
      (primeHodgeHistoryTailProjection n) (primeHodgeVisibilityOp a) = 0 := by
  exact (HTGeometry.projectorDephasingGenerator_eq_zero_iff_commute
    (k := ℂ) (primeHodgeHistoryTailProjection n) (primeHodgeVisibilityOp a)
    (primeHodgeHistoryTailProjection_isIdempotentElem n)).2
      (primeHodgeHistoryTailProjection_commutes_visibility a n)

/-- Existing prime-history contrast scores are immune to tail-sector dephasing. -/
theorem primeHodgeContrastOp_tailDephasing_eq_zero (a : ℝ) (n : ℕ) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
      (primeHodgeHistoryTailProjection n) (primeHodgeContrastOp a) = 0 := by
  exact (HTGeometry.projectorDephasingGenerator_eq_zero_iff_commute
    (k := ℂ) (primeHodgeHistoryTailProjection n) (primeHodgeContrastOp a)
    (primeHodgeHistoryTailProjection_isIdempotentElem n)).2
      (primeHodgeHistoryTailProjection_commutes_contrast a n)

/-- Tail-sector dephasing of the visible trace-class marginal is exactly half its block-pinching
disturbance. -/
theorem primeHodgeVisibleMarginal_tailDephasing_eq (a : ℝ) (n : ℕ) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
        (primeHodgeHistoryTailProjection n) (primeHodgeVisibleMarginal a) =
      (2 : ℂ)⁻¹ •
        (ludersPinching (primeHodgeHistoryTailProjection n)
          (primeHodgeVisibleMarginal a) - primeHodgeVisibleMarginal a) := by
  simpa only [ludersPinching_eq_twoOutcomePinching] using
    HTGeometry.projectorDephasingGenerator_eq_half_pinching_sub (k := ℂ)
      (primeHodgeHistoryTailProjection n) (primeHodgeVisibleMarginal a)
      (primeHodgeHistoryTailProjection_isIdempotentElem n)

/-- Same exact tail-sector law for the contrast trace-class marginal. -/
theorem primeHodgeContrastMarginal_tailDephasing_eq (a : ℝ) (n : ℕ) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
        (primeHodgeHistoryTailProjection n) (primeHodgeContrastMarginal a) =
      (2 : ℂ)⁻¹ •
        (ludersPinching (primeHodgeHistoryTailProjection n)
          (primeHodgeContrastMarginal a) - primeHodgeContrastMarginal a) := by
  simpa only [ludersPinching_eq_twoOutcomePinching] using
    HTGeometry.projectorDephasingGenerator_eq_half_pinching_sub (k := ℂ)
      (primeHodgeHistoryTailProjection n) (primeHodgeContrastMarginal a)
      (primeHodgeHistoryTailProjection_isIdempotentElem n)

/-- Tail dephasing of the visible marginal is precisely the negative half-sum of the corpus's
two oriented cutoff-boundary channels. -/
theorem primeHodgeVisibleMarginal_tailDephasing_eq_boundaries (a : ℝ) (n : ℕ) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
        (primeHodgeHistoryTailProjection n) (primeHodgeVisibleMarginal a) =
      -(2 : ℂ)⁻¹ •
        (crossBoundary (primeHodgeHistoryTailProjection n) (primeHodgeVisibleMarginal a) +
          upperBoundary (primeHodgeHistoryTailProjection n) (primeHodgeVisibleMarginal a)) := by
  rw [primeHodgeVisibleMarginal_tailDephasing_eq,
    ← sub_ludersPinching_eq_crossBoundary_add_upperBoundary]
  module

/-- Tail dephasing of the contrast marginal has the same exact boundary-channel decomposition. -/
theorem primeHodgeContrastMarginal_tailDephasing_eq_boundaries (a : ℝ) (n : ℕ) :
    HTGeometry.projectorDephasingGenerator (k := ℂ)
        (primeHodgeHistoryTailProjection n) (primeHodgeContrastMarginal a) =
      -(2 : ℂ)⁻¹ •
        (crossBoundary (primeHodgeHistoryTailProjection n) (primeHodgeContrastMarginal a) +
          upperBoundary (primeHodgeHistoryTailProjection n) (primeHodgeContrastMarginal a)) := by
  rw [primeHodgeContrastMarginal_tailDephasing_eq,
    ← sub_ludersPinching_eq_crossBoundary_add_upperBoundary]
  module

/-! ## Symmetric frozen-offset applications -/

/-- Symmetric rapidity disorder leaves the even visibility channel unchanged. -/
theorem primeHodgeVisibility_symmetricFrozenAverage (a : ℝ) (p : Nat.Primes) :
    HTGeometry.symmetricFrozenAverage (fun ε => primeHodgeVisibility ε p) a =
      primeHodgeVisibility a p := by
  rw [HTGeometry.symmetricFrozenAverage, primeHodgeVisibility_neg]
  ring

/-- The same disorder cancels the odd contrast channel exactly. -/
theorem primeHodgeContrast_symmetricFrozenAverage (a : ℝ) (p : Nat.Primes) :
    HTGeometry.symmetricFrozenAverage (fun ε => primeHodgeContrast ε p) a = 0 := by
  rw [HTGeometry.symmetricFrozenAverage, primeHodgeContrast_neg]
  ring

/-- Symmetric frozen rapidity offsets preserve the full visibility operator. -/
theorem primeHodgeVisibilityOp_symmetricFrozenAverage (a : ℝ) :
    (2 : ℂ)⁻¹ • (primeHodgeVisibilityOp a + primeHodgeVisibilityOp (-a)) =
      primeHodgeVisibilityOp a := by
  rw [primeHodgeVisibilityOp_neg]
  module

/-- Symmetric frozen rapidity offsets erase the full contrast operator. -/
theorem primeHodgeContrastOp_symmetricFrozenAverage (a : ℝ) :
    (2 : ℂ)⁻¹ • (primeHodgeContrastOp a + primeHodgeContrastOp (-a)) = 0 := by
  rw [primeHodgeContrastOp_neg]
  module

/-- Both quadratic trace-class marginals are even, so symmetric offsets preserve them. -/
theorem primeHodgeVisibleMarginal_symmetricFrozenAverage (a : ℝ) :
    (2 : ℂ)⁻¹ • (primeHodgeVisibleMarginal a + primeHodgeVisibleMarginal (-a)) =
      primeHodgeVisibleMarginal a := by
  rw [primeHodgeVisibleMarginal_neg]
  module

theorem primeHodgeContrastMarginal_symmetricFrozenAverage (a : ℝ) :
    (2 : ℂ)⁻¹ • (primeHodgeContrastMarginal a + primeHodgeContrastMarginal (-a)) =
      primeHodgeContrastMarginal a := by
  rw [primeHodgeContrastMarginal_neg]
  module

/-- Symmetry forces zero first-order frozen-offset response of both corpus charges. -/
theorem primeHodgeVisibleCharge_deriv_zero : deriv primeHodgeVisibleCharge 0 = 0 := by
  have heven : (fun a : ℝ => primeHodgeVisibleCharge (-a)) = primeHodgeVisibleCharge := by
    funext a
    exact primeHodgeVisibleCharge_neg a
  have hcomp := deriv_comp_neg primeHodgeVisibleCharge 0
  rw [heven] at hcomp
  simp only [neg_zero] at hcomp
  linarith

theorem primeHodgeContrastCharge_deriv_zero : deriv primeHodgeContrastCharge 0 = 0 := by
  have heven : (fun a : ℝ => primeHodgeContrastCharge (-a)) = primeHodgeContrastCharge := by
    funext a
    exact primeHodgeContrastCharge_neg a
  have hcomp := deriv_comp_neg primeHodgeContrastCharge 0
  rw [heven] at hcomp
  simp only [neg_zero] at hcomp
  linarith

end RHTower
