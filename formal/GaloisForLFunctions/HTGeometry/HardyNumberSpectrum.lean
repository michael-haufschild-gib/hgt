import GaloisForLFunctions.HTGeometry.HardyNumberMinusKMS
import GaloisForLFunctions.RHTower.HilbertBasisMultiplierOperator

/-!
# Natural labels for the Blaschke number spectrum

Label zero denotes the geometric ground state; positive labels denote the
successive Blaschke monomials. The pointwise KMS equation exposes the number
weight needed when finite products of these modes are assembled.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The ground state has label zero, followed by the monomial excitations. -/
def hardyBlaschkeNaturalIndex : ℕ ≃ Option ℕ where
  toFun
    | 0 => none
    | n + 1 => some n
  invFun
    | none => 0
    | some n => n + 1
  left_inv n := by cases n <;> rfl
  right_inv n := by cases n <;> rfl

/-- The complete Blaschke basis with natural-number labels. -/
def hardyNumberBasis {q : ℝ} (hq : ‖(q : ℂ)‖ < 1) : HilbertBasis ℕ ℂ HardyDisk :=
  RHTower.hilbertBasisReindex (hardyBlaschkeBasis hq) hardyBlaschkeNaturalIndex

theorem hardyNumberBasis_apply {q : ℝ} (hq : ‖(q : ℂ)‖ < 1) (k : ℕ) :
    hardyNumberBasis hq k = hardyBlaschkeBasis hq (hardyBlaschkeNaturalIndex k) :=
  RHTower.hilbertBasisReindex_apply _ _ _

/-- Ground energy and positive integer energies in natural labels. -/
def hardyNumberEnergy (q : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then -(q ^ 2) / (1 - q ^ 2) else k

theorem hardyNumberEnergy_eq (q : ℝ) (k : ℕ) :
    hardyNumberEnergy q k = hardyBlaschkeEnergy q (hardyBlaschkeNaturalIndex k) := by
  cases k with
  | zero => rfl
  | succ k => simp [hardyNumberEnergy, hardyBlaschkeNaturalIndex, hardyBlaschkeEnergy]

theorem hardyNumberBasis_mem_domain {q : ℝ} (hq : ‖(q : ℂ)‖ < 1) (k : ℕ) :
    hardyNumberBasis hq k ∈ (hardyNumberMinusKMS hq).domain := by
  rw [hardyNumberBasis_apply]
  exact hardyBlaschkeBasis_mem_numberDomain hq _

theorem hardyNumberMinusKMS_numberBasis {q : ℝ} (hq : ‖(q : ℂ)‖ < 1) (k : ℕ) :
    hardyNumberMinusKMS hq ⟨hardyNumberBasis hq k, hardyNumberBasis_mem_domain hq k⟩ =
      (hardyNumberEnergy q k : ℂ) • hardyNumberBasis hq k := by
  simpa only [hardyNumberBasis_apply, hardyNumberEnergy_eq] using
    hardyNumberMinusKMS_basis hq (hardyBlaschkeNaturalIndex k)

/-- KMS applied to a mode is the coordinate number minus its excitation shift. -/
theorem hardyGeometricKMS_numberBasis_apply {q : ℝ} (hq : ‖(q : ℂ)‖ < 1)
    (k n : ℕ) :
    hardyGeometricKMS hq (hardyNumberBasis hq k) n =
      ((n : ℂ) + 1 - (hardyNumberEnergy q k : ℂ)) * hardyNumberBasis hq k n := by
  have h := congrArg (fun x : HardyDisk => x n) (hardyNumberMinusKMS_numberBasis hq k)
  rw [hardyNumberMinusKMS_apply] at h
  change (n : ℂ) * hardyNumberBasis hq k n -
      hardyGeometricKMS hq (hardyNumberBasis hq k) n + hardyNumberBasis hq k n =
    (hardyNumberEnergy q k : ℂ) * hardyNumberBasis hq k n at h
  linear_combination -h

end GaloisForLFunctions.HTGeometry
