import GaloisForLFunctions.RHTower.ConstrainedProlateOperator
import GaloisForLFunctions.LidskiiSelfAdjoint

/-!
# Signed spectrum of the concrete prolate Fourier block

This module applies the project's signed compact self-adjoint exhaustion to the actual
`Pₐ F Pₐ` operator.  It supplies signed eigenvalues and modes unconditionally and relates their
squares to the concentration and leakage operators.

The classical identification of the positive signed subsequence with the `4j` prolate modes and
its Fuchs asymptotics remains a separate analytic theorem.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The signed greedy eigenvalues of the actual self-adjoint block `Pₐ F Pₐ`. -/
noncomputable def evenProlateSignedValue (a : ℝ) (n : ℕ) : ℝ :=
  ContinuousLinearMap.sgVal (evenTimeBandFourier a) n

noncomputable def evenProlateSignedMode (a : ℝ) (n : ℕ) : evenSubspace :=
  ContinuousLinearMap.sgVec (evenTimeBandFourier a) n

/-- The unconditional signed prolate eigen-equation. -/
theorem evenTimeBandFourier_apply_signedMode (a : ℝ) (n : ℕ) :
    evenTimeBandFourier a (evenProlateSignedMode a n) =
      (evenProlateSignedValue a n : ℂ) • evenProlateSignedMode a n :=
  ContinuousLinearMap.apply_sgVec _ n

theorem evenProlateSignedMode_orthogonal_of_ne (a : ℝ)
    {m n : ℕ} (hmn : m ≠ n) :
    inner ℂ (evenProlateSignedMode a m) (evenProlateSignedMode a n) = 0 :=
  ContinuousLinearMap.inner_sgVec_sgVec_of_ne _ hmn

theorem evenProlateSignedMode_norm_zero_or_one (a : ℝ) (n : ℕ) :
    evenProlateSignedMode a n = 0 ∨ ‖evenProlateSignedMode a n‖ = 1 :=
  ContinuousLinearMap.norm_sgVec_zero_or_one _ n

/-- The signed eigenvalues vanish in absolute value. -/
theorem evenProlateSignedAbsValue_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun n => |evenProlateSignedValue a n|) Filter.atTop (nhds 0) := by
  have habs := ContinuousLinearMap.abs_sgVal
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_evenTimeBandFourier a))
  have hlim := ContinuousLinearMap.sgOrthSup_tendsto_zero
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_evenTimeBandFourier a))
  exact hlim.congr' (Filter.Eventually.of_forall fun n => (habs n).symm)

theorem evenProlateSignedMode_mem_timeLimited_of_value_ne_zero
    (a : ℝ) {n : ℕ} (hn : evenProlateSignedValue a n ≠ 0) :
    evenProlateSignedMode a n ∈ evenTimeLimitedSubspace a := by
  let μ : ℂ := (evenProlateSignedValue a n : ℂ)
  have hμ : μ ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hout := evenTimeBandFourier_mem_timeLimited a (evenProlateSignedMode a n)
  have heig := evenTimeBandFourier_apply_signedMode a n
  have hscaled : μ⁻¹ • evenTimeBandFourier a (evenProlateSignedMode a n) ∈
      evenTimeLimitedSubspace a := (evenTimeLimitedSubspace a).smul_mem μ⁻¹ hout
  rw [heig] at hscaled
  change μ⁻¹ • μ • evenProlateSignedMode a n ∈ evenTimeLimitedSubspace a at hscaled
  rw [inv_smul_smul₀ hμ] at hscaled
  exact hscaled

/-- Squaring the signed eigen-equation gives the corresponding concentration value. -/
theorem evenProlateConcentration_apply_signedMode (a : ℝ) (n : ℕ) :
    evenProlateConcentration a (evenProlateSignedMode a n) =
      ((evenProlateSignedValue a n ^ 2 : ℝ) : ℂ) • evenProlateSignedMode a n := by
  rw [evenProlateConcentration_eq_sq, ContinuousLinearMap.mul_apply,
    evenTimeBandFourier_apply_signedMode, map_smul,
    evenTimeBandFourier_apply_signedMode, smul_smul]
  congr 1
  push_cast
  ring

theorem evenProlateLeakage_apply_signedMode (a : ℝ) (n : ℕ) :
    evenProlateLeakage a (evenProlateSignedMode a n) =
      ((1 - evenProlateSignedValue a n ^ 2 : ℝ) : ℂ) • evenProlateSignedMode a n := by
  rw [evenProlateLeakage, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, evenProlateConcentration_apply_signedMode]
  push_cast
  module

end RHTower

