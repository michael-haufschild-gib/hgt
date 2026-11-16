import GaloisForLFunctions.RHTower.LocalCharacters.PrimitiveTateCharacterCompleteness
import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateLinear
import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierDilation
import GaloisForLFunctions.RHTower.FieldOneLocalHaarModule

/-!
# Critical Tate integrals for continuous unitary characters

Every continuous unitary character of `ℚ_pˣ` has finite angular conductor.
Consequently its critical Tate integral converges absolutely on every
Bruhat test. Multiplicative Haar invariance gives its exact covariance
under every nonzero dilation.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.LocalCharacters

open MeasureTheory

variable (p : ℕ) [Fact p.Prime]

/-- The multiplicative weight `χ(a) |a|^(1/2)` at the critical exponent. -/
def criticalTateWeight (χ : ℚ_[p]ˣ →ₜ* Circle) : ℚ_[p]ˣ →* ℂ where
  toFun a := (χ a : ℂ) * (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, Circle.coe_mul, Units.val_mul, norm_mul,
      Real.sqrt_mul (norm_nonneg _), Complex.ofReal_mul]
    ring

theorem criticalTateWeight_ne_zero (χ : ℚ_[p]ˣ →ₜ* Circle) (a : ℚ_[p]ˣ) :
    criticalTateWeight p χ a ≠ 0 := by
  exact mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr (Units.ne_zero a))))

/-- Absolute convergence requires no separately supplied conductor bound. -/
theorem integrable_criticalTate (χ : ℚ_[p]ˣ →ₜ* Circle)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    Integrable (fun a : ℚ_[p]ˣ => f.1 (a : ℚ_[p]) * criticalTateWeight p χ a)
      (fieldOnePadicMultiplicativeHaar p) := by
  obtain ⟨n, ξ, hξ⟩ := exists_primitive_tate_character p χ
  let ρ := χ (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd 1, 1))
  have heq : (fun a : ℚ_[p]ˣ => f.1 (a : ℚ_[p]) * criticalTateWeight p χ a) =
      fieldOnePadicCriticalTateIntegrand p n ξ ρ f := by
    funext a
    change f.1 (a : ℚ_[p]) * ((χ a : ℂ) * _) = _
    rw [hξ a]
    unfold fieldOnePadicCriticalTateIntegrand
    rw [fieldOnePadicCriticalHalfDensity_eq_sqrt_norm]
    exact (mul_assoc _ _ _).symm
  rw [heq]
  exact integrable_fieldOnePadicCriticalTateIntegrand p n ξ ρ f

/-- The actual critical Tate integral, as a complex-linear functional. -/
def criticalTateLinear (χ : ℚ_[p]ˣ →ₜ* Circle) :
    compactlySupportedLocallyConstant ℚ_[p] →ₗ[ℂ] ℂ where
  toFun f := ∫ a, f.1 (a : ℚ_[p]) * criticalTateWeight p χ a
    ∂fieldOnePadicMultiplicativeHaar p
  map_add' f g := by
    change (∫ a, (f.1 (a : ℚ_[p]) + g.1 (a : ℚ_[p])) * _
      ∂fieldOnePadicMultiplicativeHaar p) = _
    simp only [add_mul]
    exact integral_add (integrable_criticalTate p χ f) (integrable_criticalTate p χ g)
  map_smul' c f := by
    change (∫ a, (c * f.1 (a : ℚ_[p])) * _
      ∂fieldOnePadicMultiplicativeHaar p) = c * _
    simp only [mul_assoc]
    exact integral_const_mul _ _

/-- Dilation by `b` multiplies the Tate integral by `χ(b)⁻¹ |b|⁻¹ᐟ²`. -/
theorem criticalTateLinear_dilation (χ : ℚ_[p]ˣ →ₜ* Circle) (b : ℚ_[p]ˣ)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    criticalTateLinear p χ (fieldOnePadicBruhatDilation p b f) =
      (criticalTateWeight p χ b)⁻¹ * criticalTateLinear p χ f := by
  let G : ℚ_[p]ˣ → ℂ := fun a => f.1 (a : ℚ_[p]) * criticalTateWeight p χ a
  have hpoint : (fun a : ℚ_[p]ˣ =>
      (fieldOnePadicBruhatDilation p b f).1 (a : ℚ_[p]) * criticalTateWeight p χ a) =
      fun a => (criticalTateWeight p χ b)⁻¹ * G (b * a) := by
    funext a
    dsimp only [G]
    rw [fieldOnePadicBruhatDilation_apply,
      map_mul (criticalTateWeight p χ) b a, Units.val_mul]
    have hb := criticalTateWeight_ne_zero p χ b
    field_simp
  change (∫ a, (fieldOnePadicBruhatDilation p b f).1 (a : ℚ_[p]) *
    criticalTateWeight p χ a ∂fieldOnePadicMultiplicativeHaar p) = _
  rw [hpoint, integral_const_mul, integral_mul_left_eq_self G b]
  rfl

/-- The two critical weights multiply to the additive Haar modulus. -/
theorem criticalTateWeight_dual_mul (χ : ℚ_[p]ˣ →ₜ* Circle) (a : ℚ_[p]ˣ) :
    criticalTateWeight p (χ⁻¹) a * criticalTateWeight p χ a =
      (‖(a : ℚ_[p])‖ : ℂ) := by
  change ((↑((χ a)⁻¹) : ℂ) * (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)) *
    ((χ a : ℂ) * (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)) = _
  rw [Circle.coe_inv]
  calc
    _ = ((χ a : ℂ)⁻¹ * (χ a : ℂ)) * (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ) ^ 2 := by ring
    _ = (‖(a : ℚ_[p])‖ : ℂ) := by
      rw [inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul,
        ← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg _)]

/-- Fourier transformation preserves the dilation character after dualizing `χ`. -/
theorem criticalTateLinear_fourier_dilation (χ : ℚ_[p]ˣ →ₜ* Circle) (b : ℚ_[p]ˣ)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    criticalTateLinear p (χ⁻¹)
        (fieldOnePadicBruhatFourierLinear p (fieldOnePadicBruhatDilation p b f)) =
      (criticalTateWeight p χ b)⁻¹ * criticalTateLinear p (χ⁻¹)
        (fieldOnePadicBruhatFourierLinear p f) := by
  have hF : fieldOnePadicBruhatFourierLinear p (fieldOnePadicBruhatDilation p b f) =
      ((‖(b : ℚ_[p])‖ : ℂ)⁻¹) • fieldOnePadicBruhatDilation p b⁻¹
        (fieldOnePadicBruhatFourierLinear p f) := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change fieldOnePadicBruhatFourier p (fieldOnePadicBruhatDilation p b f) y =
      (‖(b : ℚ_[p])‖ : ℂ)⁻¹ *
        fieldOnePadicBruhatFourier p f (((b⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * y)
    rw [fieldOnePadicBruhatFourier_dilation,
      fieldOnePadicUnits_distribHaarChar_eq_nnnorm]
    simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_inv,
      coe_nnnorm, Complex.ofReal_inv]
  rw [hF, map_smul, criticalTateLinear_dilation, map_inv, inv_inv, smul_eq_mul]
  have hn : (‖(b : ℚ_[p])‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Units.ne_zero b))
  have hw := criticalTateWeight_ne_zero p χ b
  have hdual := criticalTateWeight_dual_mul p χ b
  have hcoef : (‖(b : ℚ_[p])‖ : ℂ)⁻¹ * criticalTateWeight p (χ⁻¹) b =
      (criticalTateWeight p χ b)⁻¹ := by
    calc
      _ = (‖(b : ℚ_[p])‖ : ℂ)⁻¹ * criticalTateWeight p (χ⁻¹) b *
          (criticalTateWeight p χ b * (criticalTateWeight p χ b)⁻¹) := by
        rw [mul_inv_cancel₀ hw, mul_one]
      _ = (‖(b : ℚ_[p])‖ : ℂ)⁻¹ *
          (criticalTateWeight p (χ⁻¹) b * criticalTateWeight p χ b) *
          (criticalTateWeight p χ b)⁻¹ := by ring
      _ = _ := by rw [hdual, inv_mul_cancel₀ hn, one_mul]
  rw [← mul_assoc, hcoef]

#print axioms integrable_criticalTate
#print axioms criticalTateLinear_dilation
#print axioms criticalTateLinear_fourier_dilation

end GaloisForLFunctions.RHTower.LocalCharacters
