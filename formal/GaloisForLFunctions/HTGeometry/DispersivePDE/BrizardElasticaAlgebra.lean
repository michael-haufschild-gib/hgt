import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Tactic

/-!
# Algebraic core of Brizard's closed-elastica NLS reduction

Closed, assumption-free formulations of the polynomial identities in arXiv:2607.21750,
equations (11), (47), (59)--(60), (64), and (73)--(78).  A nonzero scale is represented by a
unit rather than by a theorem hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Positive curvature scale, packaged so downstream theorems remain assumption-free. -/
abbrev PositiveCurvatureScale := {q : ℝ // 0 < q}

/-- Extended Jacobi range used by the paper. -/
abbrev NegativeModulus := Set.Iio (0 : ℝ)

/-- Classical Jacobi range. -/
abbrev ClassicalModulus := Set.Ioo (0 : ℝ) 1

/-- Appendix A transformation `n = -m/(1-m)`. -/
noncomputable def extendedToClassical (m : NegativeModulus) : ClassicalModulus := by
  have hm : (m : ℝ) < 0 := m.property
  refine ⟨-(m : ℝ) / (1 - (m : ℝ)), ?_, ?_⟩
  · exact div_pos (neg_pos.mpr hm) (by linarith [hm])
  · exact (div_lt_one (by linarith [hm])).2 (by linarith [hm])

/-- Inverse transformation `m = -n/(1-n)`. -/
noncomputable def classicalToExtended (n : ClassicalModulus) : NegativeModulus := by
  refine ⟨-(n : ℝ) / (1 - (n : ℝ)), ?_⟩
  exact div_neg_of_neg_of_pos (neg_neg_of_pos n.property.1) (by linarith [n.property.2])

theorem classicalToExtended_extendedToClassical (m : NegativeModulus) :
    classicalToExtended (extendedToClassical m) = m := by
  have hm : (m : ℝ) < 0 := m.property
  apply Subtype.ext
  rw [classicalToExtended, extendedToClassical]
  have h₁ : 1 - (m : ℝ) ≠ 0 := by linarith [hm]
  have h₂ : 1 - (-(m : ℝ) / (1 - (m : ℝ))) ≠ 0 := by
    have hlt : -(m : ℝ) / (1 - (m : ℝ)) < 1 :=
      (div_lt_one (by linarith [hm])).2 (by linarith [hm])
    linarith
  field_simp [h₁, h₂]
  ring

theorem extendedToClassical_classicalToExtended (n : ClassicalModulus) :
    extendedToClassical (classicalToExtended n) = n := by
  apply Subtype.ext
  rw [extendedToClassical, classicalToExtended]
  have h₁ : 1 - (n : ℝ) ≠ 0 := by linarith [n.property.2]
  have h₂ : 1 - (-(n : ℝ) / (1 - (n : ℝ))) ≠ 0 := by
    have hneg : -(n : ℝ) / (1 - (n : ℝ)) < 0 :=
      div_neg_of_neg_of_pos (neg_neg_of_pos n.property.1) (by linarith [n.property.2])
    linarith
  field_simp [h₁, h₂]
  ring

/-- Negative and classical Jacobi moduli are exactly equivalent under Appendix A's map. -/
noncomputable def modulusEquiv : NegativeModulus ≃ ClassicalModulus where
  toFun := extendedToClassical
  invFun := classicalToExtended
  left_inv := classicalToExtended_extendedToClassical
  right_inv := extendedToClassical_classicalToExtended

theorem transformedComplement (m : NegativeModulus) :
    1 - (extendedToClassical m : ℝ) = 1 / (1 - (m : ℝ)) := by
  have hm : (m : ℝ) < 0 := m.property
  rw [extendedToClassical]
  field_simp [ne_of_gt (show 0 < 1 - (m : ℝ) by linarith [hm])]
  ring

/-- Jacobi modulus and nonzero curvature scale parameter `q₀`. -/
structure Parameters where
  modulus : ℝ
  q₀ : ℝˣ

noncomputable def gammaSq (P : Parameters) : ℝ := (1 + P.modulus) / (P.q₀ : ℝ) - 3

noncomputable def nuSq (P : Parameters) : ℝ :=
  (1 - (P.q₀ : ℝ)) * ((P.q₀ : ℝ) - P.modulus) / (P.q₀ : ℝ) ^ 2

/-- Equation (64), first parameter reconstruction. -/
theorem modulus_eq_q₀_mul_gammaSq (P : Parameters) :
    P.modulus = (P.q₀ : ℝ) * (3 + gammaSq P) - 1 := by
  rw [gammaSq]
  field_simp [P.q₀.ne_zero]
  ring

/-- Equation (64), second parameter reconstruction. -/
theorem modulus_eq_q₀_sq_mul_gammaSq_sub_nuSq (P : Parameters) :
    P.modulus = (P.q₀ : ℝ) ^ 2 * (2 + gammaSq P - nuSq P) := by
  rw [gammaSq, nuSq]
  field_simp [P.q₀.ne_zero]
  ring

/-- The two torsionless parameter walls in equation (66). -/
theorem nuSq_eq_zero_iff (P : Parameters) :
    nuSq P = 0 ↔ (P.q₀ : ℝ) = 1 ∨ (P.q₀ : ℝ) = P.modulus := by
  rw [nuSq, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · exact (pow_ne_zero 2 P.q₀.ne_zero h).elim
  · rintro (h | h)
    · left
      apply mul_eq_zero.mpr
      exact Or.inl (by linarith)
    · left
      apply mul_eq_zero.mpr
      exact Or.inr (by linarith)

/-- The zero-speed parameter wall in equation (65). -/
theorem gammaSq_eq_zero_iff (P : Parameters) :
    gammaSq P = 0 ↔ 1 + P.modulus = 3 * (P.q₀ : ℝ) := by
  rw [gammaSq]
  constructor
  · intro h
    field_simp [P.q₀.ne_zero] at h
    linarith
  · intro h
    field_simp [P.q₀.ne_zero]
    linarith

/-- Equation (47): the NLS-selected elastica multiplier. -/
noncomputable def waveLambda (γ : ℝ) : ℝ := -(γ ^ 2) / 2

theorem waveLambda_nonpos (γ : ℝ) : waveLambda γ ≤ 0 := by
  rw [waveLambda]
  nlinarith [sq_nonneg γ]

theorem waveLambda_eq_zero_iff (γ : ℝ) : waveLambda γ = 0 ↔ γ = 0 := by
  rw [waveLambda]
  constructor
  · intro h
    have : γ ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp this
  · rintro rfl
    ring

/-- Equation (59), viewed as an algebraic energy at a nonzero curvature. -/
noncomputable def curvatureEnergy (k₀ γ ν : ℝ) (κ : ℝˣ) : ℝ :=
  (k₀ ^ 4 - (κ : ℝ) ^ 4) / 4
    + (k₀ ^ 2 * γ ^ 2 / 4) * (k₀ ^ 2 - (κ : ℝ) ^ 2)
    + (k₀ ^ 4 * ν ^ 2 / 4) * (1 - k₀ ^ 2 / (κ : ℝ) ^ 2)

/-- Right side of equation (60). -/
def squaredCurvatureCubic (k₀ γ ν q : ℝ) : ℝ :=
  -q ^ 3 - k₀ ^ 2 * γ ^ 2 * q ^ 2
    + k₀ ^ 4 * q * (1 + ν ^ 2 + γ ^ 2) - k₀ ^ 6 * ν ^ 2

/-- Equation (59) implies equation (60) after multiplying by `4κ²`. -/
theorem curvatureEnergy_to_squaredCubic (k₀ γ ν : ℝ) (κ : ℝˣ) :
    4 * (κ : ℝ) ^ 2 * curvatureEnergy k₀ γ ν κ =
      squaredCurvatureCubic k₀ γ ν ((κ : ℝ) ^ 2) := by
  rw [curvatureEnergy, squaredCurvatureCubic]
  field_simp [κ.ne_zero]
  ring

/-- Equation (64): factorization of the dimensionless curvature cubic. -/
theorem dimensionlessCurvatureCubic_factor (q₀ q γ ν : ℝ) :
    -4 * q ^ 3 - 4 * γ ^ 2 * q₀ * q ^ 2
        + 4 * (1 + ν ^ 2 + γ ^ 2) * q₀ ^ 2 * q - 4 * q₀ ^ 3 * ν ^ 2 =
      4 * (q₀ - q) * (q ^ 2 + (1 + γ ^ 2) * q₀ * q - q₀ ^ 2 * ν ^ 2) := by
  ring

/-- Equation (11): torsion reconstructed from the conserved curvature--torsion product. -/
noncomputable def torsion (k₀ τ₀ : ℝ) (κ : ℝˣ) : ℝ := k₀ ^ 2 * τ₀ / (κ : ℝ) ^ 2

theorem curvatureSq_mul_torsion (k₀ τ₀ : ℝ) (κ : ℝˣ) :
    (κ : ℝ) ^ 2 * torsion k₀ τ₀ κ = k₀ ^ 2 * τ₀ := by
  rw [torsion]
  field_simp [κ.ne_zero]

/-- Hydrodynamic density `ρ = κ²`. -/
def density (κ : ℝˣ) : ℝ := (κ : ℝ) ^ 2

/-- Hasimoto fluid speed `u = 2Dτ`. -/
noncomputable def fluidSpeed (D k₀ τ₀ : ℝ) (κ : ℝˣ) : ℝ := 2 * D * torsion k₀ τ₀ κ

/-- Equation (57), first line: mass flux is curvature-independent. -/
theorem density_mul_fluidSpeed (D k₀ τ₀ : ℝ) (κ : ℝˣ) :
    density κ * fluidSpeed D k₀ τ₀ κ = 2 * D * k₀ ^ 2 * τ₀ := by
  rw [density, fluidSpeed, torsion]
  field_simp [κ.ne_zero]

/-- Equation (57), second line: momentum flux is an inverse-curvature pressure. -/
theorem density_mul_fluidSpeed_sq (D k₀ τ₀ : ℝ) (κ : ℝˣ) :
    density κ * fluidSpeed D k₀ τ₀ κ ^ 2 =
      4 * D ^ 2 * k₀ ^ 4 * τ₀ ^ 2 / (κ : ℝ) ^ 2 := by
  rw [density, fluidSpeed, torsion]
  field_simp [κ.ne_zero]
  ring

/-- The three roots displayed after equation (73). -/
noncomputable def e₁ (P : Parameters) : ℝ := (2 - P.modulus) / (3 * (P.q₀ : ℝ))
noncomputable def e₂ (P : Parameters) : ℝ := (2 * P.modulus - 1) / (3 * (P.q₀ : ℝ))
noncomputable def e₃ (P : Parameters) : ℝ := -(1 + P.modulus) / (3 * (P.q₀ : ℝ))

/-- Equation (74): second Weierstrass invariant. -/
noncomputable def g₂ (P : Parameters) : ℝ :=
  4 * (1 - P.modulus + P.modulus ^ 2) / (3 * (P.q₀ : ℝ) ^ 2)

/-- Equation (75): third Weierstrass invariant. -/
noncomputable def g₃ (P : Parameters) : ℝ :=
  4 * (2 - 3 * P.modulus - 3 * P.modulus ^ 2 + 2 * P.modulus ^ 3) /
    (27 * (P.q₀ : ℝ) ^ 3)

/-- Equation (76): Weierstrass discriminant. -/
noncomputable def discriminant (P : Parameters) : ℝ :=
  16 * P.modulus ^ 2 * (1 - P.modulus) ^ 2 / (P.q₀ : ℝ) ^ 6

theorem e_sum (P : Parameters) : e₁ P + e₂ P + e₃ P = 0 := by
  rw [e₁, e₂, e₃]
  field_simp [P.q₀.ne_zero]
  ring

theorem e₁_sub_e₃ (P : Parameters) : e₁ P - e₃ P = 1 / (P.q₀ : ℝ) := by
  rw [e₁, e₃]
  field_simp [P.q₀.ne_zero]
  ring

theorem e₂_sub_e₃ (P : Parameters) : e₂ P - e₃ P = P.modulus / (P.q₀ : ℝ) := by
  rw [e₂, e₃]
  field_simp [P.q₀.ne_zero]
  ring

theorem e₁_sub_e₂ (P : Parameters) : e₁ P - e₂ P = (1 - P.modulus) / (P.q₀ : ℝ) := by
  rw [e₁, e₂]
  field_simp [P.q₀.ne_zero]
  ring

/-- First equality in equation (74). -/
theorem g₂_eq_root_sum (P : Parameters) :
    g₂ P = 2 * (e₁ P ^ 2 + e₂ P ^ 2 + e₃ P ^ 2) := by
  rw [g₂, e₁, e₂, e₃]
  field_simp [P.q₀.ne_zero]
  ring

/-- First equality in equation (75). -/
theorem g₃_eq_root (P : Parameters) :
    g₃ P = 4 * e₁ P * e₂ P * e₃ P := by
  rw [g₃, e₁, e₂, e₃]
  field_simp [P.q₀.ne_zero]
  ring

/-- Equation (76), recovered from the invariant definition `g₂³ - 27g₃²`. -/
theorem g₂_cubed_sub_g₃_sq (P : Parameters) :
    g₂ P ^ 3 - 27 * g₃ P ^ 2 = discriminant P := by
  rw [g₂, g₃, discriminant]
  field_simp [P.q₀.ne_zero]
  ring

theorem g₂_pos (P : Parameters) : 0 < g₂ P := by
  rw [g₂]
  have hpoly : 0 < 1 - P.modulus + P.modulus ^ 2 := by
    nlinarith [sq_nonneg (P.modulus - (1 / 2 : ℝ))]
  have hq : 0 < (P.q₀ : ℝ) ^ 2 := sq_pos_of_ne_zero P.q₀.ne_zero
  exact div_pos (mul_pos (by norm_num) hpoly) (mul_pos (by norm_num) hq)

theorem discriminant_nonneg (P : Parameters) : 0 ≤ discriminant P := by
  rw [discriminant]
  positivity

theorem discriminant_eq_zero_iff (P : Parameters) :
    discriminant P = 0 ↔ P.modulus = 0 ∨ P.modulus = 1 := by
  rw [discriminant, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · exact Or.inl (sq_eq_zero_iff.mp h)
      · have h' := sq_eq_zero_iff.mp h
        exact Or.inr (by linarith)
    · exact (pow_ne_zero 6 P.q₀.ne_zero h).elim
  · rintro (h | h)
    · left
      rw [h]
      ring
    · left
      rw [h]
      ring

/-- Each displayed `eᵢ` is a root of the Weierstrass cubic in equation (72). -/
theorem e₁_root (P : Parameters) : 4 * e₁ P ^ 3 - g₂ P * e₁ P - g₃ P = 0 := by
  rw [e₁, g₂, g₃]
  field_simp [P.q₀.ne_zero]
  ring

theorem e₂_root (P : Parameters) : 4 * e₂ P ^ 3 - g₂ P * e₂ P - g₃ P = 0 := by
  rw [e₂, g₂, g₃]
  field_simp [P.q₀.ne_zero]
  ring

theorem e₃_root (P : Parameters) : 4 * e₃ P ^ 3 - g₂ P * e₃ P - g₃ P = 0 := by
  rw [e₃, g₂, g₃]
  field_simp [P.q₀.ne_zero]
  ring

/-- Short Weierstrass model of equation (72), with `y = wp'/2`. -/
noncomputable def weierstrassCurve (P : Parameters) : WeierstrassCurve ℝ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(g₂ P) / 4
  a₆ := -(g₃ P) / 4

/-- Mathlib's curve discriminant is exactly Brizard's equation (76). -/
theorem weierstrassCurve_discriminant (P : Parameters) :
    (weierstrassCurve P).Δ = discriminant P := by
  rw [weierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  rw [← g₂_cubed_sub_g₃_sq P]
  ring

theorem e₁_on_weierstrassCurve (P : Parameters) :
    (weierstrassCurve P).toAffine.Equation (e₁ P) 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [weierstrassCurve]
  linear_combination -(e₁_root P) / 4

theorem e₂_on_weierstrassCurve (P : Parameters) :
    (weierstrassCurve P).toAffine.Equation (e₂ P) 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [weierstrassCurve]
  linear_combination -(e₂_root P) / 4

theorem e₃_on_weierstrassCurve (P : Parameters) :
    (weierstrassCurve P).toAffine.Equation (e₃ P) 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [weierstrassCurve]
  linear_combination -(e₃_root P) / 4

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
