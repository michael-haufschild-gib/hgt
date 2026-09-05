import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaSquareNondegenerate

/-!
# Complement transport for Brizard's Weierstrass data

The complementary Jacobi substitution `m ↦ 1-m` negates and permutes Brizard's three cubic roots.
Consequently it fixes `g₂` and the discriminant while negating `g₃`.  The same transformation on
analytic period data is induced by the quarter-turn lattice dilation `L ↦ iL`, because Eisenstein
invariants have weights four and six.  Thus the algebraic complement symmetry and analytic lattice
rotation have exactly matching invariant-level actions.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Parameters obtained by the complementary Jacobi substitution `m ↦ 1-m`. -/
noncomputable def complementParameters (P : Parameters) : Parameters where
  modulus := 1 - P.modulus
  q₀ := P.q₀

@[simp] theorem complementParameters_modulus (P : Parameters) :
    (complementParameters P).modulus = 1 - P.modulus := rfl

@[simp] theorem complementParameters_q₀ (P : Parameters) :
    (complementParameters P).q₀ = P.q₀ := rfl

theorem complementParameters_involutive (P : Parameters) :
    complementParameters (complementParameters P) = P := by
  cases P
  simp [complementParameters]

theorem complement_e₁ (P : Parameters) :
    e₁ (complementParameters P) = -e₃ P := by
  rw [e₁, e₃]
  simp only [complementParameters_modulus, complementParameters_q₀]
  ring

theorem complement_e₂ (P : Parameters) :
    e₂ (complementParameters P) = -e₂ P := by
  rw [e₂, e₂]
  simp only [complementParameters_modulus, complementParameters_q₀]
  ring

theorem complement_e₃ (P : Parameters) :
    e₃ (complementParameters P) = -e₁ P := by
  rw [e₃, e₁]
  simp only [complementParameters_modulus, complementParameters_q₀]
  ring

theorem complement_g₂ (P : Parameters) :
    g₂ (complementParameters P) = g₂ P := by
  rw [g₂, g₂]
  simp only [complementParameters_modulus, complementParameters_q₀]
  ring

theorem complement_g₃ (P : Parameters) :
    g₃ (complementParameters P) = -g₃ P := by
  rw [g₃, g₃]
  simp only [complementParameters_modulus, complementParameters_q₀]
  ring

theorem complement_discriminant (P : Parameters) :
    discriminant (complementParameters P) = discriminant P := by
  rw [discriminant, discriminant]
  simp only [complementParameters_modulus, complementParameters_q₀]
  ring

theorem complexI_inv_pow_four : (Complex.I : ℂ)⁻¹ ^ 4 = 1 := by
  rw [Complex.inv_I]
  rw [show (-Complex.I : ℂ) ^ 4 = (Complex.I ^ 2) ^ 2 by ring]
  rw [Complex.I_sq]
  norm_num

/-- A quarter turn fixes the analytic weight-four invariant. -/
theorem scaleIPeriodPair_g₂ (L : PeriodPair) :
    (scalePeriodPair complexIUnit L).g₂ = L.g₂ := by
  rw [scalePeriodPair_g₂, coe_complexIUnit, complexI_inv_pow_four, one_mul]

/-- A quarter turn negates the analytic weight-six invariant. -/
theorem scaleIPeriodPair_g₃ (L : PeriodPair) :
    (scalePeriodPair complexIUnit L).g₃ = -L.g₃ := by
  rw [scalePeriodPair_g₃, coe_complexIUnit, complexI_inv_pow_six, neg_one_mul]

/-- Quarter-turn dilation preserves the analytic curve discriminant. -/
theorem scaleIPeriodPair_discriminant (L : PeriodPair) :
    (analyticWeierstrassCurve (scalePeriodPair complexIUnit L)).Δ =
      (analyticWeierstrassCurve L).Δ := by
  rw [analyticWeierstrassCurve_discriminant, analyticWeierstrassCurve_discriminant,
    scaleIPeriodPair_g₂, scaleIPeriodPair_g₃]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
