import GaloisForLFunctions.RHTower.EulerSquarefreeWickReplicaDensityOrientation

/-!
# Pure-vacuum magnitude rigidity for Euler--Wick

The EWQ replica source already solves two substantial pre-divisor problems at once: either
diagonal is the coefficient-faithful zeta Euler logarithm, while the off-diagonal retains the
joint quadratic character.  This module classifies how much nonunitary magnitude can be added
without changing those two vacuum diagonals.

For an arbitrary positive semidefinite two-channel lift with equal real vacuum diagonal `a`, the
off-diagonal norm is at most `a`.  Equality holds exactly when the lift has determinant zero.  In
particular, every pure lift is magnitude-rigid: its off-diagonal can carry phase or sign, but its
norm cannot differ from the vacuum coefficient.

The actual EWQ replica density lies exactly on this pure boundary at every prime and valuation
depth.  Therefore importing an independent zeta vacuum does not create the magnitude-changing
incidence requested by EWQ-V as long as positivity, two replicas, equal coefficient-faithful
diagonals, and purity are retained.  A surviving construction must leave at least one of those
four structural conditions.
-/

open Complex Matrix
open scoped ComplexOrder MatrixOrder

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- A positive rank-one two-channel lift whose two diagonal channels are the same real vacuum
coefficient. -/
def EqualVacuumDiagonalPureLift
    (a : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  M.PosSemidef ∧
    M 0 0 = (a : ℂ) ∧
    M 1 1 = (a : ℂ) ∧
    M.det = 0

/-- Positive equal-vacuum diagonals cap every coherent off-diagonal magnitude. -/
theorem offDiagonal_norm_le_of_posSemidef_equalVacuumDiagonal
    {a : ℝ} {M : Matrix (Fin 2) (Fin 2) ℂ}
    (ha : 0 ≤ a) (hpsd : M.PosSemidef)
    (h00 : M 0 0 = (a : ℂ)) (h11 : M 1 1 = (a : ℂ)) :
    ‖M 0 1‖ ≤ a := by
  have hherm := hpsd.isHermitian.apply 0 1
  have h10 : M 1 0 = star (M 0 1) := by
    simpa using congrArg star hherm
  have hdet := hpsd.det_nonneg
  rw [Matrix.det_fin_two, h00, h11, h10] at hdet
  have hmul : M 0 1 * star (M 0 1) =
      (Complex.normSq (M 0 1) : ℂ) := Complex.mul_conj _
  rw [hmul, Complex.le_def] at hdet
  have hsq : ‖M 0 1‖ ^ 2 ≤ a ^ 2 := by
    rw [Complex.sq_norm]
    norm_num at hdet
    simpa [pow_two] using hdet
  nlinarith [norm_nonneg (M 0 1)]

/-- A pure positive lift with two equal vacuum diagonals has no off-diagonal magnitude freedom. -/
theorem offDiagonal_norm_eq_of_equalVacuumDiagonalPureLift
    {a : ℝ} {M : Matrix (Fin 2) (Fin 2) ℂ}
    (ha : 0 ≤ a) (hM : EqualVacuumDiagonalPureLift a M) :
    ‖M 0 1‖ = a := by
  rcases hM with ⟨hpsd, h00, h11, hdet⟩
  have hherm := hpsd.isHermitian.apply 0 1
  have h10 : M 1 0 = star (M 0 1) := by
    simpa using congrArg star hherm
  rw [Matrix.det_fin_two, h00, h11, h10] at hdet
  have hnormSq : Complex.normSq (M 0 1) = a ^ 2 := by
    have hmul : M 0 1 * star (M 0 1) =
        (Complex.normSq (M 0 1) : ℂ) := Complex.mul_conj _
    rw [hmul] at hdet
    have hre := congrArg Complex.re hdet
    norm_num at hre
    nlinarith
  have hsq : ‖M 0 1‖ ^ 2 = a ^ 2 := by
    rw [Complex.sq_norm]
    exact hnormSq
  nlinarith [norm_nonneg (M 0 1)]

/-- Within the positive equal-diagonal chamber, off-diagonal saturation is exactly purity. -/
theorem offDiagonal_norm_eq_iff_det_eq_zero_of_posSemidef_equalVacuumDiagonal
    {a : ℝ} {M : Matrix (Fin 2) (Fin 2) ℂ}
    (ha : 0 ≤ a) (hpsd : M.PosSemidef)
    (h00 : M 0 0 = (a : ℂ)) (h11 : M 1 1 = (a : ℂ)) :
    ‖M 0 1‖ = a ↔ M.det = 0 := by
  constructor
  · intro hnorm
    have hherm := hpsd.isHermitian.apply 0 1
    have h10 : M 1 0 = star (M 0 1) := by
      simpa using congrArg star hherm
    rw [Matrix.det_fin_two, h00, h11, h10]
    have hmul : M 0 1 * star (M 0 1) =
        (Complex.normSq (M 0 1) : ℂ) := Complex.mul_conj _
    rw [hmul, ← Complex.sq_norm, hnorm]
    push_cast
    ring
  · intro hdet
    exact offDiagonal_norm_eq_of_equalVacuumDiagonalPureLift ha
      ⟨hpsd, h00, h11, hdet⟩

/-- Consequently a genuine magnitude-changing off-diagonal cannot occur in the pure positive
equal-vacuum class. -/
theorem not_equalVacuumDiagonalPureLift_of_offDiagonal_magnitude_change
    {a : ℝ} {M : Matrix (Fin 2) (Fin 2) ℂ}
    (ha : 0 ≤ a) (hchange : ‖M 0 1‖ ≠ a) :
    ¬ EqualVacuumDiagonalPureLift a M := by
  intro hM
  exact hchange (offDiagonal_norm_eq_of_equalVacuumDiagonalPureLift ha hM)

/-- The literal EWQ replica density is an equal-vacuum pure lift at every prime-depth cell. -/
theorem eulerWickReplicaDensity_equalVacuumDiagonalPureLift
    (x : PrimePowerClockIndex) :
    EqualVacuumDiagonalPureLift ((((x.2 + 1 : ℕ) : ℝ))⁻¹)
      (eulerWickReplicaDensity x) := by
  refine ⟨eulerWickReplicaDensity_posSemidef x, ?_, ?_, ?_⟩
  · simpa [eulerLogValuationProfile] using
      eulerWickReplicaDensity_apply_zero_zero x
  · simpa [eulerLogValuationProfile] using
      eulerWickReplicaDensity_apply_one_one x
  rw [Matrix.det_fin_two,
    eulerWickReplicaDensity_apply_zero_zero,
    eulerWickReplicaDensity_apply_one_one,
    eulerWickReplicaDensity_apply_zero_one,
    eulerWickReplicaDensity_apply_one_zero]
  unfold eulerWickQuadraticEulerLogReplica eulerLogValuationProfile
  have hsq := eulerWickQuadraticDepthCharacter_sq x
  field_simp
  linear_combination -hsq

/-- **EWQ pure-vacuum no-go.** The actual coefficient-faithful EWQ off-diagonal has exactly the
vacuum magnitude at every prime and valuation depth. -/
theorem norm_eulerWickReplicaDensity_offDiagonal_eq_vacuum
    (x : PrimePowerClockIndex) :
    ‖eulerWickReplicaDensity x 0 1‖ = (((x.2 + 1 : ℕ) : ℝ))⁻¹ := by
  apply offDiagonal_norm_eq_of_equalVacuumDiagonalPureLift
  · positivity
  · exact eulerWickReplicaDensity_equalVacuumDiagonalPureLift x

end

end GaloisForLFunctions.RHTower
