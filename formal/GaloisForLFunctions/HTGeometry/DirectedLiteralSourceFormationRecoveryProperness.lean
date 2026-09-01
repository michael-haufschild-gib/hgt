import GaloisForLFunctions.HTGeometry.LiteralSourceAdmissibleRankGaugeObstruction

/-!
# Directed literal-source formation/recovery properness

Actual marked formation and its exact rank recovery are jointly moderate precisely when the
character is unitary.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open _root_.RHTower

/-- Canonical rank recovery, retained only on the directed nonnegative source history. -/
def literalSourceForwardRecoveryHistory (z : ℂ) : ℤ → ℂ :=
  hardyPositiveHalf z

/-- Actual marked source formation on nonnegative ranks, extended by zero to negative ranks. -/
def literalSourceForwardFormationHistory (z : ℂ) : ℤ → ℂ :=
  fun e => (1 - z) * hardyPositiveHalf z⁻¹ e

/-- Directed recovery agrees with the natural-rank gauge. -/
theorem literalSourceForwardRecoveryHistory_nat (z : ℂ) (m : ℕ) :
    literalSourceForwardRecoveryHistory z (m : ℤ) = (z⁻¹) ^ m := by
  simp [literalSourceForwardRecoveryHistory, hardyPositiveHalf,
    zpow_neg, zpow_natCast]

/-- Directed formation is the literal coherent source edge at every natural rank. -/
theorem literalSourceForwardFormationHistory_nat
    (z : ℂ) (m : ℕ) :
    literalSourceForwardFormationHistory z (m : ℤ) =
      complexCharacterEdge z m := by
  have hpow : (z⁻¹) ^ (-((m : ℕ) : ℤ)) = z ^ m := by
    rw [inv_zpow, ← zpow_neg, neg_neg, zpow_natCast]
  rw [literalSourceForwardFormationHistory, hardyPositiveHalf,
    if_pos (Int.natCast_nonneg m), hpow, complexCharacterEdge, pow_succ]
  ring

/-- Formation followed by rank recovery is exactly the rank-independent source response. -/
theorem literalSourceForwardRecovery_mul_formation_nat
    {z : ℂ} (hz : z ≠ 0) (m : ℕ) :
    literalSourceForwardRecoveryHistory z (m : ℤ) *
        literalSourceForwardFormationHistory z (m : ℤ) =
      1 - z := by
  rw [literalSourceForwardRecoveryHistory_nat,
    literalSourceForwardFormationHistory_nat z]
  exact rankAnchoredComplexCharacterEdge_eq hz m

/-- Directed formation at rank `12+j` is the actual marked source execution. -/
theorem literalSourceForwardFormationHistory_rankTwelve
    {p : ℕ} (hp : p.Prime) (z : ℂ) (j : ℕ) :
    literalSourceForwardFormationHistory z ((12 + j : ℕ) : ℤ) =
      rankTwelveLiteralSourceMarkedExecution p z j := by
  rw [literalSourceForwardFormationHistory_nat z,
    rankTwelveLiteralSourceMarkedExecution_eq hp]

/-- Actual depth-12 formation and recovery obey the same exact reconstruction identity. -/
theorem literalSourceForwardRecovery_mul_rankTwelveLiteralSourceMarkedExecution
    {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : z ≠ 0) (j : ℕ) :
    literalSourceForwardRecoveryHistory z ((12 + j : ℕ) : ℤ) *
        rankTwelveLiteralSourceMarkedExecution p z j =
      1 - z := by
  rw [← literalSourceForwardFormationHistory_rankTwelve hp z]
  exact literalSourceForwardRecovery_mul_formation_nat hz (12 + j)

private theorem bilateralModerate_const_mul
    (a : ℂ) {c : ℤ → ℂ} (hc : bilateralModerate c) :
    bilateralModerate (fun e => a * c e) := by
  obtain ⟨C, m, hC⟩ := hc
  refine ⟨‖a‖ * C, m, fun e => ?_⟩
  rw [norm_mul]
  calc
    ‖a‖ * ‖c e‖ ≤ ‖a‖ * (C * (1 + (e.natAbs : ℝ)) ^ m) :=
      mul_le_mul_of_nonneg_left (hC e) (norm_nonneg a)
    _ = (‖a‖ * C) * (1 + (e.natAbs : ℝ)) ^ m := by ring

private theorem bilateralModerate_const_mul_iff
    {a : ℂ} (ha : a ≠ 0) (c : ℤ → ℂ) :
    bilateralModerate (fun e => a * c e) ↔ bilateralModerate c := by
  constructor
  · intro h
    have hinv := bilateralModerate_const_mul a⁻¹ h
    simpa [ha, mul_assoc] using hinv
  · exact bilateralModerate_const_mul a

/-- Recovery is moderate exactly in the inward recovery chamber. -/
theorem bilateralModerate_literalSourceForwardRecoveryHistory_iff
    {z : ℂ} (hz : z ≠ 0) :
    bilateralModerate (literalSourceForwardRecoveryHistory z) ↔
      1 ≤ ‖z‖ := by
  exact bilateralModerate_hardyPositiveHalf_iff hz

/-- Actual formation is moderate exactly in the opposite formation chamber. -/
theorem bilateralModerate_literalSourceForwardFormationHistory_iff
    {z : ℂ} (hz : z ≠ 0) :
    bilateralModerate (literalSourceForwardFormationHistory z) ↔
      ‖z‖ ≤ 1 := by
  by_cases hz1 : z = 1
  · subst z
    constructor
    · intro _
      simp
    · intro _
      refine ⟨0, 0, fun e => ?_⟩
      simp [literalSourceForwardFormationHistory]
  · have hscalar : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    change bilateralModerate (fun e => (1 - z) * hardyPositiveHalf z⁻¹ e) ↔ _
    rw [bilateralModerate_const_mul_iff hscalar,
      bilateralModerate_hardyPositiveHalf_iff (inv_ne_zero hz), norm_inv]
    exact one_le_inv₀ (norm_pos_iff.mpr hz)

/-- Joint source/recovery properness is exactly unitarity. -/
theorem literalSourceForwardFormationRecovery_jointModerate_iff
    {z : ℂ} (hz : z ≠ 0) :
    (bilateralModerate (literalSourceForwardFormationHistory z) ∧
      bilateralModerate (literalSourceForwardRecoveryHistory z)) ↔
      ‖z‖ = 1 := by
  rw [bilateralModerate_literalSourceForwardFormationHistory_iff hz,
    bilateralModerate_literalSourceForwardRecoveryHistory_iff hz]
  constructor
  · rintro ⟨hle, hge⟩
    exact le_antisymm hle hge
  · intro h
    rw [h]
    exact ⟨le_rfl, le_rfl⟩

/-- At a prime half-density character, joint properness is exactly the critical line. -/
theorem literalSourceHalfDensityFormationRecovery_jointModerate_iff
    {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    (bilateralModerate
        (literalSourceForwardFormationHistory (bilateralHalfDensityCharacter p s)) ∧
      bilateralModerate
        (literalSourceForwardRecoveryHistory (bilateralHalfDensityCharacter p s))) ↔
      s.re = 1 / 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le two_pos hp
  exact (literalSourceForwardFormationRecovery_jointModerate_iff
    (bilateralHalfDensityCharacter_ne_zero hp0 s)).trans
      (norm_bilateralHalfDensityCharacter_eq_one_iff hp s)

end

end GaloisForLFunctions.HTGeometry
