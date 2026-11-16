import GaloisForLFunctions.RHTower.LocalCharacters.UnramifiedTateBalls
import GaloisForLFunctions.RHTower.LocalCharacters.RadialBruhatSpanning
import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateEquation258Full

/-!
# The unramified Tate equation on the full Bruhat space

Unit averaging preserves the functional-equation defect. Its radial
image has a finite ball and shell expansion, on which the defect vanishes
by the unit-ball Euler factor and dilation covariance.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.LocalCharacters

open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

/-- Difference of the Fourier-dual and Euler-normalized Tate functionals. -/
def unramifiedTateDefect (ρ : Circle) :
    compactlySupportedLocallyConstant ℚ_[p] →ₗ[ℂ] ℂ :=
  (criticalTateLinear p (unramifiedCharacter p ρ⁻¹)).comp
      (fieldOnePadicBruhatFourierLinear p) -
    unramifiedTatePhase p ρ • criticalTateLinear p (unramifiedCharacter p ρ)

theorem unramifiedTateDefect_ball (ρ : Circle) (m : ℤ) :
    unramifiedTateDefect p ρ (fieldOnePadicSoninBall p m) = 0 := by
  change criticalTateLinear p (unramifiedCharacter p ρ⁻¹)
      (fieldOnePadicBruhatFourierLinear p (fieldOnePadicSoninBall p m)) -
    unramifiedTatePhase p ρ *
      criticalTateLinear p (unramifiedCharacter p ρ) (fieldOnePadicSoninBall p m) = 0
  rw [unramifiedTateEquation_ball, sub_self]

theorem unramifiedTateDefect_shell (ρ : Circle) (m : ℤ) :
    unramifiedTateDefect p ρ (fieldOnePadicSoninShell p m) = 0 := by
  rw [fieldOnePadicSoninShell, map_sub, unramifiedTateDefect_ball,
    unramifiedTateDefect_ball, sub_self]

theorem unramifiedTateDefect_radial (ρ : Circle)
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hunit : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p], f.1 ((u : ℤ_[p]) * x) = f.1 x) :
    unramifiedTateDefect p ρ f = 0 := by
  obtain ⟨N, L, hf⟩ := exists_ball_shell_decomposition p f hunit
  rw [hf, map_add, map_smul, map_sum]
  simp only [map_smul, unramifiedTateDefect_ball, unramifiedTateDefect_shell,
    smul_zero, Finset.sum_const_zero, add_zero]

theorem unramifiedTateDefect_dilation_unit (ρ : Circle) (u : ℤ_[p]ˣ)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    unramifiedTateDefect p ρ
        (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f) =
      unramifiedTateDefect p ρ f := by
  have hw : criticalTateWeight p (unramifiedCharacter p ρ)
      (fieldOnePadicUnitEmbedding p u) = 1 := by
    rw [criticalTateWeight_unramified]
    have hv : Padic.valuation ((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p]) = 0 :=
      fieldOnePadic_valuation_forward p (Multiplicative.ofAdd 0, u)
    rw [hv, zpow_zero]
  change criticalTateLinear p (unramifiedCharacter p ρ⁻¹)
      (fieldOnePadicBruhatFourierLinear p
        (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f)) -
    unramifiedTatePhase p ρ * criticalTateLinear p (unramifiedCharacter p ρ)
      (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f) = _
  rw [← unramifiedCharacter_inv, criticalTateLinear_fourier_dilation,
    criticalTateLinear_dilation, hw, inv_one, one_mul, one_mul]
  rfl

theorem unramifiedTateDefect_projection (ρ : Circle)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    unramifiedTateDefect p ρ (fieldOnePadicPrimitiveAngularProjection p 0
        (fieldOnePadicConductorZeroCharacter p) f) = unramifiedTateDefect p ρ f := by
  classical
  obtain ⟨N, L, hsupport, hperiod⟩ := fieldOnePadicBruhat_exists_finiteLevel p f
  rw [fieldOnePadicPrimitiveAngularProjection_eq_finiteAverage_of_finiteLevel
    p 0 N L (fieldOnePadicConductorZeroCharacter p) f hsupport hperiod]
  unfold fieldOnePadicPrimitiveAngularFiniteAverage
  simp only [map_sum, map_smul, smul_eq_mul, unramifiedTateDefect_dilation_unit,
    fieldOnePadicPrimitiveUnitCharacter, fieldOnePadicConductorZeroCharacter_apply, mul_one]
  have hC : (Fintype.card (ZMod (p ^ (0 + N + L)))ˣ : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hC, one_mul]

/-- The functional equation holds for every actual p-adic Bruhat test. -/
theorem unramifiedTateEquation (ρ : Circle)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    criticalTateLinear p (unramifiedCharacter p ρ⁻¹) (fieldOnePadicBruhatFourierLinear p f) =
      unramifiedTatePhase p ρ * criticalTateLinear p (unramifiedCharacter p ρ) f := by
  have hzero : unramifiedTateDefect p ρ f = 0 := by
    rw [← unramifiedTateDefect_projection]
    apply unramifiedTateDefect_radial
    intro u x
    simp only [fieldOnePadicPrimitiveAngularProjection_apply,
      fieldOnePadicPrimitiveAngularProjectionValue_unit_covariance,
      fieldOnePadicPrimitiveUnitCharacter, fieldOnePadicConductorZeroCharacter_apply,
      inv_one, one_mul]
  exact sub_eq_zero.mp hzero

#print axioms unramifiedTateEquation

end GaloisForLFunctions.RHTower.LocalCharacters
