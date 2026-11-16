import GaloisForLFunctions.RHTower.LocalCharacters.ContinuousTateIntegrals
import GaloisForLFunctions.RHTower.ConnesUnramifiedLocalZeta
import GaloisForLFunctions.RHTower.FieldOnePadicSoninL2

/-!
# The unramified critical Tate factor

The unit-ball integral is the Euler factor `(1 - ρ / sqrt(p))⁻¹`.
Fourier self-duality of the unit ball therefore determines the unramified
phase. Dilation covariance extends its functional equation to every
centered p-adic ball.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.LocalCharacters

open MeasureTheory
open scoped ComplexConjugate

variable (p : ℕ) [Fact p.Prime]

/-- The continuous character trivial on units with value `ρ` at `p`. -/
def unramifiedCharacter (ρ : Circle) : ℚ_[p]ˣ →ₜ* Circle :=
  padicCharacter p 0 1 ρ

@[simp] theorem unramifiedCharacter_apply (ρ : Circle) (a : ℚ_[p]ˣ) :
    unramifiedCharacter p ρ a = ρ ^ Padic.valuation (a : ℚ_[p]) := by
  simp only [unramifiedCharacter, padicCharacter_apply, MonoidHom.one_apply, mul_one]

@[simp] theorem unramifiedCharacter_inv (ρ : Circle) :
    (unramifiedCharacter p ρ)⁻¹ = unramifiedCharacter p ρ⁻¹ := by
  apply ContinuousMonoidHom.ext
  intro a
  change (unramifiedCharacter p ρ a)⁻¹ = unramifiedCharacter p ρ⁻¹ a
  rw [unramifiedCharacter_apply, unramifiedCharacter_apply, inv_zpow]

/-- Ratio of the absolutely convergent geometric series on valuation shells. -/
def unramifiedRatio (ρ : Circle) : ℂ := (ρ : ℂ) / (Real.sqrt (p : ℝ) : ℂ)

theorem norm_unramifiedRatio_lt_one (ρ : Circle) : ‖unramifiedRatio p ρ‖ < 1 := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by linarith only [hp])
  have hs1 : 1 < Real.sqrt (p : ℝ) := by
    nlinarith only [Real.sq_sqrt (show 0 ≤ (p : ℝ) by positivity), hs, hp]
  rw [unramifiedRatio, norm_div, Circle.norm_coe, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs]
  exact (div_lt_one hs).mpr hs1

theorem one_sub_unramifiedRatio_ne_zero (ρ : Circle) : 1 - unramifiedRatio p ρ ≠ 0 := by
  intro h
  have heq := congrArg norm (sub_eq_zero.mp h)
  have hlt := norm_unramifiedRatio_lt_one p ρ
  simp only [norm_one] at heq
  linarith only [heq, hlt]

theorem criticalTateWeight_unramified (ρ : Circle) (a : ℚ_[p]ˣ) :
    criticalTateWeight p (unramifiedCharacter p ρ) a =
      unramifiedRatio p ρ ^ Padic.valuation (a : ℚ_[p]) := by
  change (unramifiedCharacter p ρ a : ℂ) * (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ) = _
  rw [unramifiedCharacter_apply, Circle.coe_zpow,
    ← fieldOnePadicCriticalHalfDensity_eq_sqrt_norm]
  change (ρ : ℂ) ^ Padic.valuation (a : ℚ_[p]) *
      (Real.sqrt (p : ℝ) : ℂ) ^ (-Padic.valuation (a : ℚ_[p])) =
    ((ρ : ℂ) / (Real.sqrt (p : ℝ) : ℂ)) ^ Padic.valuation (a : ℚ_[p])
  rw [div_zpow, zpow_neg, div_eq_mul_inv]

/-- The literal unit-ball Tate integral is the unramified Euler factor. -/
theorem criticalTateLinear_unramified_unitBall (ρ : Circle) :
    criticalTateLinear p (unramifiedCharacter p ρ) (fieldOnePadicSoninBall p 0) =
      (1 - unramifiedRatio p ρ)⁻¹ := by
  have hpoint : (fun a : ℚ_[p]ˣ => (fieldOnePadicSoninBall p 0).1 (a : ℚ_[p]) *
      criticalTateWeight p (unramifiedCharacter p ρ) a) =
      connesPadicRadial p (connesPadicUnitBallProfile (unramifiedRatio p ρ)) := by
    funext a
    rw [fieldOnePadicSoninBall_apply_eq_indicator,
      fieldOnePadicSoninBallSet_mem_iff_valuation p 0 (Units.ne_zero a),
      zero_add, criticalTateWeight_unramified]
    unfold connesPadicRadial connesPadicUnitBallProfile
    by_cases hk : 0 ≤ Padic.valuation (a : ℚ_[p])
    · rw [if_pos hk, if_pos hk, one_mul,
        ← Int.toNat_of_nonneg hk, zpow_natCast, Int.toNat_natCast]
    · rw [if_neg hk, if_neg hk, zero_mul]
  change (∫ a, (fieldOnePadicSoninBall p 0).1 (a : ℚ_[p]) *
    criticalTateWeight p (unramifiedCharacter p ρ) a
    ∂fieldOnePadicMultiplicativeHaar p) = _
  rw [hpoint]
  exact connes_padic_unitBall_geometric p (norm_unramifiedRatio_lt_one p ρ)

/-- Ratio of the two local Euler denominators at the critical exponent. -/
def unramifiedTatePhase (ρ : Circle) : ℂ :=
  (1 - unramifiedRatio p ρ) / (1 - unramifiedRatio p ρ⁻¹)

omit [Fact p.Prime] in
theorem unramifiedRatio_inv (ρ : Circle) :
    unramifiedRatio p ρ⁻¹ = conj (unramifiedRatio p ρ) := by
  simp only [unramifiedRatio, Circle.coe_inv_eq_conj, map_div₀, Complex.conj_ofReal]

/-- The critical unramified phase is unitary. -/
theorem norm_unramifiedTatePhase (ρ : Circle) : ‖unramifiedTatePhase p ρ‖ = 1 := by
  have hden : 1 - unramifiedRatio p ρ⁻¹ = conj (1 - unramifiedRatio p ρ) := by
    rw [unramifiedRatio_inv, map_sub, map_one]
  rw [unramifiedTatePhase, norm_div, hden, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr (one_sub_unramifiedRatio_ne_zero p ρ))]

/-- The unramified functional equation holds on every centered ball. -/
theorem unramifiedTateEquation_ball (ρ : Circle) (m : ℤ) :
    criticalTateLinear p (unramifiedCharacter p ρ⁻¹)
        (fieldOnePadicBruhatFourierLinear p (fieldOnePadicSoninBall p m)) =
      unramifiedTatePhase p ρ *
        criticalTateLinear p (unramifiedCharacter p ρ) (fieldOnePadicSoninBall p m) := by
  have hbase : criticalTateLinear p (unramifiedCharacter p ρ⁻¹)
      (fieldOnePadicBruhatFourierLinear p (fieldOnePadicSoninBall p 0)) =
      unramifiedTatePhase p ρ *
        criticalTateLinear p (unramifiedCharacter p ρ) (fieldOnePadicSoninBall p 0) := by
    rw [fieldOnePadicBruhatFourierLinear_soninBall]
    simp only [neg_zero, zpow_zero, one_smul]
    rw [criticalTateLinear_unramified_unitBall, criticalTateLinear_unramified_unitBall,
      unramifiedTatePhase]
    field_simp [one_sub_unramifiedRatio_ne_zero p ρ,
      one_sub_unramifiedRatio_ne_zero p ρ⁻¹]
  have hzero : fieldOnePadicSoninBall p 0 = fieldOnePadicSoninUnitBall p := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    simp [fieldOnePadicSoninBall_apply]
  have hm : fieldOnePadicSoninBall p m =
      fieldOnePadicBruhatDilation p ((fieldOnePadicPrimeUnit p) ^ m)
        (fieldOnePadicSoninBall p 0) := by
    rw [hzero]
    rfl
  rw [hm, ← unramifiedCharacter_inv,
    criticalTateLinear_fourier_dilation, criticalTateLinear_dilation,
    unramifiedCharacter_inv, hbase]
  ring

#print axioms criticalTateLinear_unramified_unitBall
#print axioms norm_unramifiedTatePhase
#print axioms unramifiedTateEquation_ball

end GaloisForLFunctions.RHTower.LocalCharacters
