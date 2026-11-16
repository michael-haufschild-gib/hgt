import GaloisForLFunctions.RHTower.LocalCharacters.UnramifiedTateEquation

/-!
# The critical Tate equation for every continuous unitary p-adic character

Finite angular conductor is a consequence of continuity. Its primitive
representative has either conductor one, governed by the Euler-factor
ratio, or positive conductor, governed by the primitive Gauss phase.
Both cases give a unitary scalar independent of the Bruhat test.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.LocalCharacters

open MeasureTheory

variable (p : ℕ) [Fact p.Prime]

/-- Every continuous unitary character has an unconditional local Tate equation. -/
theorem exists_continuousTatePhase (χ : ℚ_[p]ˣ →ₜ* Circle) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ f : compactlySupportedLocallyConstant ℚ_[p],
      criticalTateLinear p (χ⁻¹) (fieldOnePadicBruhatFourierLinear p f) =
        γ * criticalTateLinear p χ f := by
  obtain ⟨n, ξ, hξ⟩ := exists_primitive_tate_character p χ
  let ρ := χ (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd 1, 1))
  by_cases hn : n = 0
  · subst n
    have hχ : χ = unramifiedCharacter p ρ := by
      apply ContinuousMonoidHom.ext
      intro a
      apply Subtype.ext
      rw [hξ a, unramifiedCharacter_apply, Circle.coe_zpow]
      change (ρ : ℂ) ^ Padic.valuation (a : ℚ_[p]) *
        ξ.1 (fieldOnePadicUnitReduction p 0 (fieldOnePadicAngularUnit p a)) = _
      have hang : ξ.1 (fieldOnePadicUnitReduction p 0 (fieldOnePadicAngularUnit p a)) = 1 := by
        have hunit : (fieldOnePadicUnitReduction p 0 (fieldOnePadicAngularUnit p a) :
            ZMod (p ^ 0)) = 1 := by
          letI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
          exact Subsingleton.elim _ _
        rw [hunit, map_one]
      rw [hang, mul_one]
    refine ⟨unramifiedTatePhase p ρ, norm_unramifiedTatePhase p ρ, fun f => ?_⟩
    rw [hχ, unramifiedCharacter_inv]
    exact unramifiedTateEquation p ρ f
  · let npos : ℕ+ := ⟨n, Nat.pos_of_ne_zero hn⟩
    refine ⟨fieldOnePadicRamifiedTatePhase p n ξ ρ,
      norm_fieldOnePadicRamifiedTatePhase p n ξ ρ, fun f => ?_⟩
    have hprimal : criticalTateLinear p χ f = fieldOnePadicCriticalTateLinear p n ξ ρ f := by
      apply integral_congr_ae
      filter_upwards [] with a
      change f.1 (a : ℚ_[p]) * ((χ a : ℂ) * (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)) = _
      rw [hξ a]
      unfold fieldOnePadicCriticalTateIntegrand
      rw [fieldOnePadicCriticalHalfDensity_eq_sqrt_norm]
      exact (mul_assoc _ _ _).symm
    have hdual : criticalTateLinear p (χ⁻¹) (fieldOnePadicBruhatFourierLinear p f) =
        fieldOnePadicDualCriticalTateLinear p n ξ ρ (fieldOnePadicBruhatFourierLinear p f) := by
      apply integral_congr_ae
      filter_upwards [] with a
      change (fieldOnePadicBruhatFourierLinear p f).1 (a : ℚ_[p]) *
        ((↑((χ a)⁻¹) : ℂ) * (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)) = _
      rw [Circle.coe_inv, hξ a]
      unfold fieldOnePadicDualCriticalTateIntegrand
      rw [fieldOnePadicCriticalHalfDensity_eq_sqrt_norm]
      exact (mul_assoc _ _ _).symm
    rw [hprimal, hdual]
    exact sub_eq_zero.mp (fieldOnePadicRamifiedTateDefectLinear_eq_zero p npos ξ ρ f)

#print axioms exists_continuousTatePhase

end GaloisForLFunctions.RHTower.LocalCharacters
