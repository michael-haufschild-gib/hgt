import GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointRadical
import GaloisForLFunctions.RHTower.XiPhysicalPrimeLocalMeshCoercivity

/-!
# Finite physical corrected-response saturation

The actual clipped-prime fusion kernel has an intrinsic corrected response: minus its signed
off-diagonal cross defect.  Its deficit from the diagonal density is definitionally the complete
fusion energy and hence the squared norm of the physical aggregate carrier.  This is the exact
finite source-linked saturation theorem underlying `RS2`--`RS10`; identifying an analytic `AC25`
sum with this response is a separate interface.
-/

namespace RHTower

noncomputable section

/-- Finite physical corrected response: negative signed cross defect. -/
def xiPhysicalPrimeLogCorrectedApertureResponse
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  -xiPhysicalPrimeLogApertureCrossDefect P A m k

/-- Exact physical response envelope identity (`RS2`, finite source-linked form). -/
theorem xiPhysicalPrimeLogDiagonal_sub_correctedResponse_eq_fusionEnergy
    (P : Finset Nat.Primes) (A m k : ℝ) :
    xiPhysicalPrimeLogApertureDiagonalEnergy P A m k -
        xiPhysicalPrimeLogCorrectedApertureResponse P A m k =
      xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
  rw [xiPhysicalPrimeLogCorrectedApertureResponse,
    xiPhysicalPrimeLogApertureFusionEnergy_eq_diagonal_add_cross]
  ring

/-- The corrected finite response never exceeds physical diagonal density (`RS3`). -/
theorem xiPhysicalPrimeLogCorrectedApertureResponse_le_diagonal
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    xiPhysicalPrimeLogCorrectedApertureResponse P A m k ≤
      xiPhysicalPrimeLogApertureDiagonalEnergy P A m k := by
  have h := xiPhysicalPrimeLogApertureFusionEnergy_nonneg P hA m k
  rw [← xiPhysicalPrimeLogDiagonal_sub_correctedResponse_eq_fusionEnergy] at h
  linarith

/-- Saturation occurs exactly when the actual coherent aperture carrier vanishes (`RS4`). -/
theorem xiPhysicalPrimeLogCorrectedApertureResponse_eq_diagonal_iff
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    xiPhysicalPrimeLogCorrectedApertureResponse P A m k =
        xiPhysicalPrimeLogApertureDiagonalEnergy P A m k ↔
      xiPhysicalPrimeLogAggregateApertureCarrier P A m k = 0 := by
  constructor
  · intro h
    have henergy : xiPhysicalPrimeLogApertureFusionEnergy P A m k = 0 := by
      rw [← xiPhysicalPrimeLogDiagonal_sub_correctedResponse_eq_fusionEnergy]
      linarith
    rw [xiPhysicalPrimeLogApertureFusionEnergy_eq_norm_sq P hA m k,
      sq_eq_zero_iff, norm_eq_zero] at henergy
    exact henergy
  · intro hzero
    have henergy : xiPhysicalPrimeLogApertureFusionEnergy P A m k = 0 := by
      rw [xiPhysicalPrimeLogApertureFusionEnergy_eq_norm_sq P hA m k, hzero,
        norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    rw [← xiPhysicalPrimeLogDiagonal_sub_correctedResponse_eq_fusionEnergy] at henergy
    linarith

/-- For a nonempty active packet of width strictly between zero and the aperture, response
saturation is impossible. -/
theorem xiPhysicalPrimeLogCorrectedApertureResponse_lt_diagonal_of_nonempty_active
    {P : Finset Nat.Primes} (hP : P.Nonempty)
    {A m k : ℝ}
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    xiPhysicalPrimeLogCorrectedApertureResponse P A m k <
      xiPhysicalPrimeLogApertureDiagonalEnergy P A m k := by
  have hA : 0 < A := hwidth0.trans hwidthA
  apply lt_of_le_of_ne
    (xiPhysicalPrimeLogCorrectedApertureResponse_le_diagonal P hA m k)
  intro h
  exact (xiPhysicalPrimeLogAggregateApertureCarrier_ne_zero_of_nonempty_active
    hP hactive hwidth0 hwidthA)
      ((xiPhysicalPrimeLogCorrectedApertureResponse_eq_diagonal_iff P hA m k).mp h)

/-- Add back an arbitrary quadrature correction to obtain the corresponding uncorrected finite
response. -/
def xiPhysicalPrimeLogApertureResponse
    (P : Finset Nat.Primes) (A m k error : ℝ) : ℝ :=
  xiPhysicalPrimeLogCorrectedApertureResponse P A m k + error

/-- Exact uncorrected deficit identity (`RS1`). -/
theorem xiPhysicalPrimeLogDiagonal_sub_response_eq_fusionEnergy_sub_error
    (P : Finset Nat.Primes) (A m k error : ℝ) :
    xiPhysicalPrimeLogApertureDiagonalEnergy P A m k -
        xiPhysicalPrimeLogApertureResponse P A m k error =
      xiPhysicalPrimeLogApertureFusionEnergy P A m k - error := by
  rw [xiPhysicalPrimeLogApertureResponse,
    ← xiPhysicalPrimeLogDiagonal_sub_correctedResponse_eq_fusionEnergy]
  ring

/-- Uncorrected response is bounded by density plus correction (`RS5`). -/
theorem xiPhysicalPrimeLogApertureResponse_le_diagonal_add_error
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k error : ℝ) :
    xiPhysicalPrimeLogApertureResponse P A m k error ≤
      xiPhysicalPrimeLogApertureDiagonalEnergy P A m k + error := by
  rw [xiPhysicalPrimeLogApertureResponse]
  simpa [add_comm] using add_le_add_right
    (xiPhysicalPrimeLogCorrectedApertureResponse_le_diagonal P hA m k) error

/-- Equality form of the uncorrected response envelope (`RS6`). -/
theorem xiPhysicalPrimeLogApertureResponse_eq_diagonal_add_error_iff
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k error : ℝ) :
    xiPhysicalPrimeLogApertureResponse P A m k error =
        xiPhysicalPrimeLogApertureDiagonalEnergy P A m k + error ↔
      xiPhysicalPrimeLogAggregateApertureCarrier P A m k = 0 := by
  rw [xiPhysicalPrimeLogApertureResponse, add_left_inj,
    xiPhysicalPrimeLogCorrectedApertureResponse_eq_diagonal_iff P hA m k]

/-- Error-budget form of the unconditional lower deficit bound (`RS7`). -/
theorem neg_errorBudget_le_diagonal_sub_xiPhysicalPrimeLogApertureResponse
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A)
    (m k error errorBudget : ℝ) (herror : |error| ≤ errorBudget) :
    -errorBudget ≤ xiPhysicalPrimeLogApertureDiagonalEnergy P A m k -
      xiPhysicalPrimeLogApertureResponse P A m k error := by
  rw [xiPhysicalPrimeLogDiagonal_sub_response_eq_fusionEnergy_sub_error]
  have henergy := xiPhysicalPrimeLogApertureFusionEnergy_nonneg P hA m k
  have herr : error ≤ errorBudget := (abs_le.mp herror).2
  linarith

/-- Error-budget form of the unconditional response upper bound (`RS7`). -/
theorem xiPhysicalPrimeLogApertureResponse_le_diagonal_add_errorBudget
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A)
    (m k error errorBudget : ℝ) (herror : |error| ≤ errorBudget) :
    xiPhysicalPrimeLogApertureResponse P A m k error ≤
      xiPhysicalPrimeLogApertureDiagonalEnergy P A m k + errorBudget := by
  calc
    xiPhysicalPrimeLogApertureResponse P A m k error ≤
        xiPhysicalPrimeLogApertureDiagonalEnergy P A m k + error :=
      xiPhysicalPrimeLogApertureResponse_le_diagonal_add_error P hA m k error
    _ ≤ xiPhysicalPrimeLogApertureDiagonalEnergy P A m k + errorBudget :=
      by
        simpa [add_comm] using
          (add_le_add_left (abs_le.mp herror).2
            (xiPhysicalPrimeLogApertureDiagonalEnergy P A m k))

/-- Automatic lower half of the absolute deficit budget (`RS8`). -/
theorem abs_diagonal_sub_response_le_iff
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k error budget : ℝ)
    (hbudget : |error| ≤ budget) :
    |xiPhysicalPrimeLogApertureDiagonalEnergy P A m k -
        xiPhysicalPrimeLogApertureResponse P A m k error| ≤ budget ↔
      xiPhysicalPrimeLogApertureDiagonalEnergy P A m k -
        xiPhysicalPrimeLogApertureResponse P A m k error ≤ budget := by
  rw [abs_le]
  have henergy := xiPhysicalPrimeLogApertureFusionEnergy_nonneg P hA m k
  have herr : error ≤ budget := (abs_le.mp hbudget).2
  rw [xiPhysicalPrimeLogDiagonal_sub_response_eq_fusionEnergy_sub_error]
  constructor
  · exact And.right
  · intro hupper
    exact ⟨by linarith, hupper⟩

/-- One-sided deficit budget is exactly response near-saturation from below (`RS8`). -/
theorem diagonal_sub_response_le_iff_response_ge
    (P : Finset Nat.Primes) (A m k error budget : ℝ) :
    xiPhysicalPrimeLogApertureDiagonalEnergy P A m k -
        xiPhysicalPrimeLogApertureResponse P A m k error ≤ budget ↔
      xiPhysicalPrimeLogApertureDiagonalEnergy P A m k - budget ≤
        xiPhysicalPrimeLogApertureResponse P A m k error := by
  constructor <;> intro h <;> linarith

/-- Combined `RS8`: under an error budget, the absolute checkpoint is exactly the one-sided
response saturation lower bound. -/
theorem abs_diagonal_sub_response_le_iff_response_ge
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k error budget : ℝ)
    (hbudget : |error| ≤ budget) :
    |xiPhysicalPrimeLogApertureDiagonalEnergy P A m k -
        xiPhysicalPrimeLogApertureResponse P A m k error| ≤ budget ↔
      xiPhysicalPrimeLogApertureDiagonalEnergy P A m k - budget ≤
        xiPhysicalPrimeLogApertureResponse P A m k error := by
  rw [abs_diagonal_sub_response_le_iff P hA m k error budget hbudget,
    diagonal_sub_response_le_iff_response_ge]

/-- One-sided deficit control forces the aperture carrier energy bound (`RS9`). -/
theorem fusionEnergy_le_deficitBudget_add_errorBudget
    (P : Finset Nat.Primes) (A m k error deficitBudget errorBudget : ℝ)
    (hdeficit : xiPhysicalPrimeLogApertureDiagonalEnergy P A m k -
      xiPhysicalPrimeLogApertureResponse P A m k error ≤ deficitBudget)
    (herror : |error| ≤ errorBudget) :
    xiPhysicalPrimeLogApertureFusionEnergy P A m k ≤
      deficitBudget + errorBudget := by
  rw [xiPhysicalPrimeLogDiagonal_sub_response_eq_fusionEnergy_sub_error] at hdeficit
  have herr : error ≤ errorBudget := (abs_le.mp herror).2
  linarith

/-- Carrier-energy upper control implies the absolute corrected deficit bound (`RS10`). -/
theorem abs_diagonal_sub_response_le_fusionBudget_add_errorBudget
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A)
    (m k error fusionBudget errorBudget : ℝ)
    (hfusion : xiPhysicalPrimeLogApertureFusionEnergy P A m k ≤ fusionBudget)
    (herror : |error| ≤ errorBudget) :
    |xiPhysicalPrimeLogApertureDiagonalEnergy P A m k -
        xiPhysicalPrimeLogApertureResponse P A m k error| ≤
      fusionBudget + errorBudget := by
  rw [xiPhysicalPrimeLogDiagonal_sub_response_eq_fusionEnergy_sub_error]
  calc
    |xiPhysicalPrimeLogApertureFusionEnergy P A m k - error| ≤
        |xiPhysicalPrimeLogApertureFusionEnergy P A m k| + |error| :=
      abs_sub _ _
    _ ≤ fusionBudget + errorBudget := by
      have henergy := xiPhysicalPrimeLogApertureFusionEnergy_nonneg P hA m k
      have habs : |xiPhysicalPrimeLogApertureFusionEnergy P A m k| ≤ fusionBudget := by
        rw [abs_of_nonneg henergy]
        exact hfusion
      exact add_le_add habs herror

end
end RHTower
