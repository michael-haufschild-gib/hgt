import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaModularInvariant
import Mathlib.Tactic

/-!
# Exact parameter transport for Brizard's negative-modulus transformation

Appendix A of arXiv:2607.21750 replaces a negative Jacobi parameter `m` by
`-m / (1-m)`.  Transporting the nonzero scale by `q₀ ↦ q₀ / (1-m)` does more than
preserve the modular invariant: it fixes the entire Weierstrass cubic.  The first root is fixed,
the other two roots are exchanged, and consequently `g₂`, `g₃`, the discriminant, and the
mathlib `WeierstrassCurve` are exactly unchanged.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Brizard parameters in the paper's negative-modulus presentation. -/
noncomputable def negativeParameters (m : NegativeModulus) (q₀ : ℝˣ) : Parameters where
  modulus := m
  q₀ := q₀

/-- The positive denominator `1-m`, packaged as a nonzero real scale. -/
noncomputable def negativeGapUnit (m : NegativeModulus) : ℝˣ :=
  Units.mk0 (1 - (m : ℝ)) (by
    have hm : (m : ℝ) < 0 := m.property
    linarith)

theorem negativeGap_ne_zero (m : NegativeModulus) : 1 - (m : ℝ) ≠ 0 := by
  have hm : (m : ℝ) < 0 := m.property
  linarith

/-- Classical-modulus parameters with the compensating scale transformation. -/
noncomputable def transportedClassicalParameters
    (m : NegativeModulus) (q₀ : ℝˣ) : Parameters where
  modulus := extendedToClassical m
  q₀ := q₀ / negativeGapUnit m

@[simp] theorem negativeParameters_modulus (m : NegativeModulus) (q₀ : ℝˣ) :
    (negativeParameters m q₀).modulus = (m : ℝ) := rfl

@[simp] theorem negativeParameters_q₀ (m : NegativeModulus) (q₀ : ℝˣ) :
    ((negativeParameters m q₀).q₀ : ℝ) = (q₀ : ℝ) := rfl

@[simp] theorem transportedClassicalParameters_modulus
    (m : NegativeModulus) (q₀ : ℝˣ) :
    (transportedClassicalParameters m q₀).modulus =
      (extendedToClassical m : ℝ) := rfl

@[simp] theorem transportedClassicalParameters_q₀
    (m : NegativeModulus) (q₀ : ℝˣ) :
    ((transportedClassicalParameters m q₀).q₀ : ℝ) =
      (q₀ : ℝ) / (1 - (m : ℝ)) := by
  rfl

theorem transported_e₁ (m : NegativeModulus) (q₀ : ℝˣ) :
    e₁ (transportedClassicalParameters m q₀) = e₁ (negativeParameters m q₀) := by
  have hgap : 1 - (m : ℝ) ≠ 0 := negativeGap_ne_zero m
  rw [e₁, e₁]
  simp only [transportedClassicalParameters_modulus, transportedClassicalParameters_q₀,
    negativeParameters_modulus, negativeParameters_q₀]
  rw [extendedToClassical]
  field_simp [q₀.ne_zero, hgap]
  ring

theorem transported_e₂ (m : NegativeModulus) (q₀ : ℝˣ) :
    e₂ (transportedClassicalParameters m q₀) = e₃ (negativeParameters m q₀) := by
  have hgap : 1 - (m : ℝ) ≠ 0 := negativeGap_ne_zero m
  rw [e₂, e₃]
  simp only [transportedClassicalParameters_modulus, transportedClassicalParameters_q₀,
    negativeParameters_modulus, negativeParameters_q₀]
  rw [extendedToClassical]
  field_simp [q₀.ne_zero, hgap]
  ring

theorem transported_e₃ (m : NegativeModulus) (q₀ : ℝˣ) :
    e₃ (transportedClassicalParameters m q₀) = e₂ (negativeParameters m q₀) := by
  have hgap : 1 - (m : ℝ) ≠ 0 := negativeGap_ne_zero m
  rw [e₃, e₂]
  simp only [transportedClassicalParameters_modulus, transportedClassicalParameters_q₀,
    negativeParameters_modulus, negativeParameters_q₀]
  rw [extendedToClassical]
  field_simp [q₀.ne_zero, hgap]
  ring

theorem transported_g₂ (m : NegativeModulus) (q₀ : ℝˣ) :
    g₂ (transportedClassicalParameters m q₀) = g₂ (negativeParameters m q₀) := by
  have hgap : 1 - (m : ℝ) ≠ 0 := negativeGap_ne_zero m
  rw [g₂, g₂]
  simp only [transportedClassicalParameters_modulus, transportedClassicalParameters_q₀,
    negativeParameters_modulus, negativeParameters_q₀]
  rw [extendedToClassical]
  field_simp [q₀.ne_zero, hgap]
  ring

theorem transported_g₃ (m : NegativeModulus) (q₀ : ℝˣ) :
    g₃ (transportedClassicalParameters m q₀) = g₃ (negativeParameters m q₀) := by
  have hgap : 1 - (m : ℝ) ≠ 0 := negativeGap_ne_zero m
  rw [g₃, g₃]
  simp only [transportedClassicalParameters_modulus, transportedClassicalParameters_q₀,
    negativeParameters_modulus, negativeParameters_q₀]
  rw [extendedToClassical]
  field_simp [q₀.ne_zero, hgap]
  ring

theorem transported_discriminant (m : NegativeModulus) (q₀ : ℝˣ) :
    discriminant (transportedClassicalParameters m q₀) =
      discriminant (negativeParameters m q₀) := by
  rw [← g₂_cubed_sub_g₃_sq, ← g₂_cubed_sub_g₃_sq,
    transported_g₂, transported_g₃]

theorem transported_weierstrassCurve (m : NegativeModulus) (q₀ : ℝˣ) :
    weierstrassCurve (transportedClassicalParameters m q₀) =
      weierstrassCurve (negativeParameters m q₀) := by
  ext <;> simp [weierstrassCurve, transported_g₂, transported_g₃]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
