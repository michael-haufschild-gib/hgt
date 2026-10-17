import GaloisForLFunctions.RHTower.EvenSectorBlindMinimumSmallAperturePositivity
import GaloisForLFunctions.RHTower.OddSectorFiniteGroundReduction

/-!
# Shift-gauge invariance of the EWU and OWU blind ground-state apparatus

Avenue B of the EWU review asks whether transporting the OWU finite-dimensional dual multiplier and
paired root-division apparatus (`OddSectorExactDualAttainment`, `OddSectorArithmeticGroundOperator`,
`OddSectorFiniteGroundReduction`, `OddSectorPairedGroundDivision`,
`OddSectorGroundPolynomialStructure`) to the even polar sector can determine the sign of
`evenBlindMinimum a` for all apertures `a > 0`.

This file proves the exact **shift-gauge invariance obstruction**:

1. **Constant symbol shift on the form domain** (`shiftedSourceQuadratic`,
   `shiftedRestrictedWeilForm`):
   Replacing the archimedean symbol by a constant shift corresponds on the form domain to
   `Q_{a,C}(u) = Q_a(u) - C ‖J_a u‖²`.
2. **Exact invariance of blind minimizers under arbitrary shifts `C ∈ ℝ`**
   (`shiftedSourceQuadratic_blindUnit`, `isMin_shiftedSourceQuadratic_iff`,
   `shifted_evenBlindMinimum_neg_of_gt`):
   Because every `u : BlindUnitSource a` has unit physical norm `‖J_a u‖ = 1`, shifting `Q_a` by
   `-C ‖J_a u‖²` shifts the objective on `BlindUnitSource a` by the constant `-C`.  Thus the set of
   blind minimizers is **identically unchanged** for every `C ∈ ℝ`, while the minimum value shifts
   to `evenBlindMinimum a - C` (which is strictly negative whenever `C > evenBlindMinimum a`).
3. **Exact cancellation of the shift `C` in the subtracted residual form**
   (`shiftedSourceQuadratic_sub_shiftedEvenBlindMinimum_eq`,
   `shiftedRestrictedWeilForm_sub_shiftedEvenBlindMinimum_eq`,
   `oddSector_shifted_arithmeticForm_sub_shiftedBlindMinimum_eq`):
   When forming the nonnegative residual quadratic/sesquilinear form by subtracting
   `(m(a) - C) ‖J_a u‖²` from `Q_{a,C}(u) - Σ_j λ_{a,j} Tr_j(u)`, the shift `C` cancels
   identically on the entire form domain `CCMArchimedeanFormDomain a`.  Consequently, the Farkas
   multiplier inequalities, the nonnegative shifted form, its kernel (the ground eigenspace), its
   paired-division closure, and its canonical real/cross-rooted polynomial generator are invariant
   under arbitrary constant shifts `C ∈ ℝ` and cannot distinguish `m(a) ≥ 0` from `m(a) < 0`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

/-! ## Constant-shifted restricted Weil quadratic and sesquilinear forms -/

/-- The restricted Weil quadratic form shifted by `-C ‖J_a u‖²`, corresponding to a constant shift
`2 γ_Hardy(2πξ) ↦ 2 γ_Hardy(2πξ) - C` of the archimedean symbol. -/
def shiftedSourceQuadratic (a : SuzukiPositiveAperture) (C : ℝ)
    (u : CCMArchimedeanFormDomain a) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a u - C * ‖ccmArchimedeanFormToAperture a u‖ ^ 2

/-- The restricted Weil sesquilinear form shifted by `-C ⟨J_a u, J_a v⟩`. -/
def shiftedRestrictedWeilForm (a : SuzukiPositiveAperture) (C : ℝ)
    (u v : CCMArchimedeanFormDomain a) : ℂ :=
  ccmRestrictedWeilForm a u v -
    (C : ℂ) * inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v)

theorem shiftedRestrictedWeilForm_self_re_eq (a : SuzukiPositiveAperture) (C : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    (shiftedRestrictedWeilForm a C u u).re = shiftedSourceQuadratic a C u := by
  rw [shiftedRestrictedWeilForm, shiftedSourceQuadratic, Complex.sub_re,
    ccmRestrictedWeilForm_self_re_eq_source,
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ccmArchimedeanFormToAperture a u)]
  have hreal (r : ℝ) : ((C : ℂ) * (r : ℂ) ^ 2).re = C * r ^ 2 := by
    simp [pow_two, Complex.mul_re]
  exact congrArg (fun t : ℝ => ccmRestrictedWeilSourceQuadratic a u - t)
    (hreal ‖ccmArchimedeanFormToAperture a u‖)

/-! ## Invariance of blind minimizers and shift of the blind minimum -/

/-- On `BlindUnitSource a`, the shifted quadratic form differs from the unshifted form by `-C`. -/
theorem shiftedSourceQuadratic_blindUnit (a : SuzukiPositiveAperture) (C : ℝ)
    (u : BlindUnitSource a) :
    shiftedSourceQuadratic a C u.1 = ccmRestrictedWeilSourceQuadratic a u.1 - C := by
  simp only [shiftedSourceQuadratic, u.2.2.2.1, one_pow, mul_one]

/-- On `BlindUnitSource a`, `shiftedSourceQuadratic a C` is the shifted gamma-rate integral. -/
theorem shiftedSourceQuadratic_blindUnit_eq_gamma_sub (a : SuzukiPositiveAperture) (C : ℝ)
    (u : BlindUnitSource a) :
    shiftedSourceQuadratic a C u.1 =
      (∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖(u.1.1 : ℝ → ℂ) ξ‖ ^ 2) - C := by
  rw [shiftedSourceQuadratic_blindUnit, sourceQuadratic_blind_eq_gamma]

/-- **Minimizer invariance.**  A normalized blind source minimizes `shiftedSourceQuadratic a C` on
`BlindUnitSource a` if and only if it minimizes the unshifted `ccmRestrictedWeilSourceQuadratic a`. -/
theorem isMin_shiftedSourceQuadratic_iff (a : SuzukiPositiveAperture) (C : ℝ)
    (u : BlindUnitSource a) :
    (∀ v : BlindUnitSource a, shiftedSourceQuadratic a C u.1 ≤ shiftedSourceQuadratic a C v.1) ↔
      ∀ v : BlindUnitSource a,
        ccmRestrictedWeilSourceQuadratic a u.1 ≤ ccmRestrictedWeilSourceQuadratic a v.1 := by
  simp only [shiftedSourceQuadratic_blindUnit, sub_le_sub_iff_right]

/-- `evenBlindMinimizer a` is a global minimizer of `shiftedSourceQuadratic a C` on
`BlindUnitSource a` for every `C ∈ ℝ`, with minimum value `evenBlindMinimum a - C`. -/
theorem shiftedSourceQuadratic_evenBlindMinimizer_le (a : SuzukiPositiveAperture) (C : ℝ)
    (v : BlindUnitSource a) :
    evenBlindMinimum a - C ≤ shiftedSourceQuadratic a C v.1 := by
  rw [shiftedSourceQuadratic_blindUnit]
  exact sub_le_sub_right (evenBlindMinimum_le a v) C

theorem shiftedSourceQuadratic_evenBlindMinimizer_eq (a : SuzukiPositiveAperture) (C : ℝ) :
    shiftedSourceQuadratic a C (evenBlindMinimizer a).1 = evenBlindMinimum a - C := by
  rw [shiftedSourceQuadratic_blindUnit, evenBlindMinimum]

/-- For every `C > evenBlindMinimum a`, the shifted blind minimum is strictly negative while
`evenBlindMinimizer a` remains an exact global minimizer on `BlindUnitSource a`. -/
theorem shifted_evenBlindMinimum_neg_of_gt (a : SuzukiPositiveAperture) {C : ℝ}
    (hC : evenBlindMinimum a < C) :
    shiftedSourceQuadratic a C (evenBlindMinimizer a).1 < 0 ∧
      ∀ v : BlindUnitSource a,
        shiftedSourceQuadratic a C (evenBlindMinimizer a).1 ≤ shiftedSourceQuadratic a C v.1 := by
  rw [shiftedSourceQuadratic_evenBlindMinimizer_eq]
  exact ⟨sub_neg.mpr hC, shiftedSourceQuadratic_evenBlindMinimizer_le a C⟩

/-! ## Exact cancellation of `C` in the subtracted ground residual form -/

/-- **Quadratic shift-gauge cancellation.**  Subtracting the shifted blind minimum
`(evenBlindMinimum a - C) ‖J_a u‖²` from `shiftedSourceQuadratic a C u - L u` cancels `C`
identically on the entire form domain `CCMArchimedeanFormDomain a` for any arithmetic trace
correction `L`. -/
theorem shiftedSourceQuadratic_sub_shiftedEvenBlindMinimum_eq (a : SuzukiPositiveAperture) (C : ℝ)
    (L : CCMArchimedeanFormDomain a → ℝ) (u : CCMArchimedeanFormDomain a) :
    shiftedSourceQuadratic a C u - L u -
        (evenBlindMinimum a - C) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 =
      ccmRestrictedWeilSourceQuadratic a u - L u -
        evenBlindMinimum a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  unfold shiftedSourceQuadratic
  ring

/-- **Sesquilinear shift-gauge cancellation.**  Subtracting the shifted minimum inner product from
`shiftedRestrictedWeilForm a C` reproduces the unshifted subtracted form identically. -/
theorem shiftedRestrictedWeilForm_sub_shiftedEvenBlindMinimum_eq (a : SuzukiPositiveAperture)
    (C : ℝ) (u v : CCMArchimedeanFormDomain a) :
    shiftedRestrictedWeilForm a C u v -
        ((evenBlindMinimum a - C : ℝ) : ℂ) *
          inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) =
      ccmRestrictedWeilForm a u v -
        (evenBlindMinimum a : ℂ) *
          inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) := by
  unfold shiftedRestrictedWeilForm
  push_cast
  ring

/-- **OWU shift-gauge cancellation.**  In the odd sector, shifting `OddSector.arithmeticForm a` by
`-C ⟨J_a u, J_a v⟩` and subtracting the correspondingly shifted odd blind minimum
`(OddSector.blindMinimum a - C) ⟨J_a u, J_a v⟩` leaves `OddSector.arithmeticShiftedForm a` (and
therefore `OddSector.groundSubmodule a` and its canonical polynomial generator) identically
unchanged for every `C ∈ ℝ`. -/
theorem oddSector_shifted_arithmeticForm_sub_shiftedBlindMinimum_eq
    (a : SuzukiPositiveAperture) (C : ℝ) (u v : CCMArchimedeanFormDomain a) :
    (OddSector.arithmeticForm a u v -
        (C : ℂ) * inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v)) -
      ((OddSector.blindMinimum a - C : ℝ) : ℂ) *
        inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) =
      OddSector.arithmeticShiftedForm a u v := by
  unfold OddSector.arithmeticShiftedForm
  push_cast
  ring

/-- **Farkas multiplier shift invariance.**  For any trace functional `T` that vanishes on a vector
`u` of unit physical norm `‖J_a u‖ = 1`, the dual multiplier inequality
`m_C ‖J_a v‖² ≤ Q_{a,C}(v) - ⟨λ, T(v)⟩` with `m_C = m - C` is equivalent to the unshifted
multiplier inequality `m ‖J_a v‖² ≤ Q_a(v) - ⟨λ, T(v)⟩`. -/
theorem shifted_multiplier_inequality_iff (a : SuzukiPositiveAperture) (C m : ℝ)
    (L : CCMArchimedeanFormDomain a → ℝ) (v : CCMArchimedeanFormDomain a) :
    (m - C) * ‖ccmArchimedeanFormToAperture a v‖ ^ 2 ≤ shiftedSourceQuadratic a C v - L v ↔
      m * ‖ccmArchimedeanFormToAperture a v‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a v - L v := by
  unfold shiftedSourceQuadratic
  constructor <;> intro h <;> linarith

end RHTower.EvenSector

end
