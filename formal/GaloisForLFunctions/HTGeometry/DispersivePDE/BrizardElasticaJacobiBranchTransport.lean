import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiAlternativeCurvature
import Mathlib.Tactic

/-!
# Parameter transport of the `sc` and `sd` branches

The alternative Jacobi branches are modular presentations of the same Weierstrass family.
The `sc` branch acts by `(m,q₀) ↦ (1-m,-q₀)`, while the `sd` branch acts by
`(m,q₀) ↦ (m/(m-1),q₀/(1-m))`.  Their reconstructed squared speed and torsion agree exactly with
the standard `sn` formulas after transport.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def scTransportParameters (P : Parameters) : Parameters where
  modulus := 1 - P.modulus
  q₀ := -P.q₀

@[simp] theorem scTransportParameters_modulus (P : Parameters) :
    (scTransportParameters P).modulus = 1 - P.modulus := rfl

@[simp] theorem scTransportParameters_q₀ (P : Parameters) :
    ((scTransportParameters P).q₀ : ℝ) = -(P.q₀ : ℝ) := by
  rw [scTransportParameters]
  exact Units.val_neg P.q₀

theorem scTransport_gammaSq (P : Parameters) :
    gammaSq (scTransportParameters P) = scGammaSq P.modulus P.q₀ := by
  rw [gammaSq, scGammaSq]
  simp only [scTransportParameters_modulus, scTransportParameters_q₀]
  field_simp [P.q₀.ne_zero]
  ring

theorem scTransport_nuSq (P : Parameters) :
    nuSq (scTransportParameters P) = scNuSq P.modulus P.q₀ := by
  rw [nuSq, scNuSq, scGammaSq]
  simp only [scTransportParameters_modulus, scTransportParameters_q₀]
  field_simp [P.q₀.ne_zero]
  ring

theorem scTransport_e₁ (P : Parameters) :
    e₁ (scTransportParameters P) = e₃ P := by
  rw [e₁, e₃]
  simp only [scTransportParameters_modulus, scTransportParameters_q₀]
  ring

theorem scTransport_e₂ (P : Parameters) :
    e₂ (scTransportParameters P) = e₂ P := by
  rw [e₂, e₂]
  simp only [scTransportParameters_modulus, scTransportParameters_q₀]
  ring

theorem scTransport_e₃ (P : Parameters) :
    e₃ (scTransportParameters P) = e₁ P := by
  rw [e₃, e₁]
  simp only [scTransportParameters_modulus, scTransportParameters_q₀]
  ring

theorem scTransport_g₂ (P : Parameters) :
    g₂ (scTransportParameters P) = g₂ P := by
  rw [g₂, g₂]
  simp only [scTransportParameters_modulus, scTransportParameters_q₀]
  field_simp [P.q₀.ne_zero]
  ring

theorem scTransport_g₃ (P : Parameters) :
    g₃ (scTransportParameters P) = g₃ P := by
  rw [g₃, g₃]
  simp only [scTransportParameters_modulus, scTransportParameters_q₀]
  field_simp [P.q₀.ne_zero]
  ring

theorem scTransport_discriminant (P : Parameters) :
    discriminant (scTransportParameters P) = discriminant P := by
  rw [← g₂_cubed_sub_g₃_sq, ← g₂_cubed_sub_g₃_sq,
    scTransport_g₂, scTransport_g₃]

theorem scTransport_weierstrassCurve (P : Parameters) :
    weierstrassCurve (scTransportParameters P) = weierstrassCurve P := by
  ext <;> simp [weierstrassCurve, scTransport_g₂, scTransport_g₃]

/-- The `sd` transform excludes only its genuine pole `m=1`. -/
abbrev SdTransportParameters := {P : Parameters // P.modulus ≠ 1}

theorem sdModulus_sub_one_ne (P : SdTransportParameters) :
    P.val.modulus - 1 ≠ 0 := sub_ne_zero.mpr P.property

noncomputable def sdGapUnit (P : SdTransportParameters) : ℝˣ :=
  Units.mk0 (1 - P.val.modulus) (by
    intro h
    apply P.property
    linarith)

noncomputable def sdTransportParameters (P : SdTransportParameters) : Parameters where
  modulus := P.val.modulus / (P.val.modulus - 1)
  q₀ := P.val.q₀ / sdGapUnit P

@[simp] theorem sdTransportParameters_modulus (P : SdTransportParameters) :
    (sdTransportParameters P).modulus =
      P.val.modulus / (P.val.modulus - 1) := rfl

@[simp] theorem sdTransportParameters_q₀ (P : SdTransportParameters) :
    ((sdTransportParameters P).q₀ : ℝ) =
      (P.val.q₀ : ℝ) / (1 - P.val.modulus) := by
  rfl

theorem sdTransport_gammaSq (P : SdTransportParameters) :
    gammaSq (sdTransportParameters P) =
      sdGammaSq P.val.modulus P.val.q₀ := by
  have hgap : 1 - P.val.modulus ≠ 0 := by
    intro h
    apply P.property
    linarith
  rw [gammaSq, sdGammaSq]
  simp only [sdTransportParameters_modulus, sdTransportParameters_q₀]
  field_simp [P.val.q₀.ne_zero, hgap, sdModulus_sub_one_ne P]
  ring

theorem sdTransport_nuSq (P : SdTransportParameters) :
    nuSq (sdTransportParameters P) =
      sdNuSq P.val.modulus P.val.q₀ := by
  have hgap : 1 - P.val.modulus ≠ 0 := by
    intro h
    apply P.property
    linarith
  rw [nuSq, sdNuSq, sdGammaSq]
  simp only [sdTransportParameters_modulus, sdTransportParameters_q₀]
  field_simp [P.val.q₀.ne_zero, hgap, sdModulus_sub_one_ne P]
  ring

theorem sdTransport_e₁ (P : SdTransportParameters) :
    e₁ (sdTransportParameters P) = e₁ P.val := by
  have hgap : 1 - P.val.modulus ≠ 0 := by
    intro h
    apply P.property
    linarith
  rw [e₁, e₁]
  simp only [sdTransportParameters_modulus, sdTransportParameters_q₀]
  field_simp [P.val.q₀.ne_zero, hgap, sdModulus_sub_one_ne P]
  ring

theorem sdTransport_e₂ (P : SdTransportParameters) :
    e₂ (sdTransportParameters P) = e₃ P.val := by
  have hgap : 1 - P.val.modulus ≠ 0 := by
    intro h
    apply P.property
    linarith
  rw [e₂, e₃]
  simp only [sdTransportParameters_modulus, sdTransportParameters_q₀]
  field_simp [P.val.q₀.ne_zero, hgap, sdModulus_sub_one_ne P]
  ring

theorem sdTransport_e₃ (P : SdTransportParameters) :
    e₃ (sdTransportParameters P) = e₂ P.val := by
  have hgap : 1 - P.val.modulus ≠ 0 := by
    intro h
    apply P.property
    linarith
  rw [e₃, e₂]
  simp only [sdTransportParameters_modulus, sdTransportParameters_q₀]
  field_simp [P.val.q₀.ne_zero, hgap, sdModulus_sub_one_ne P]
  ring

theorem sdTransport_g₂ (P : SdTransportParameters) :
    g₂ (sdTransportParameters P) = g₂ P.val := by
  have hgap : 1 - P.val.modulus ≠ 0 := by
    intro h
    apply P.property
    linarith
  rw [g₂, g₂]
  simp only [sdTransportParameters_modulus, sdTransportParameters_q₀]
  field_simp [P.val.q₀.ne_zero, hgap, sdModulus_sub_one_ne P]
  ring

theorem sdTransport_g₃ (P : SdTransportParameters) :
    g₃ (sdTransportParameters P) = g₃ P.val := by
  have hgap : 1 - P.val.modulus ≠ 0 := by
    intro h
    apply P.property
    linarith
  rw [g₃, g₃]
  simp only [sdTransportParameters_modulus, sdTransportParameters_q₀]
  field_simp [P.val.q₀.ne_zero, hgap, sdModulus_sub_one_ne P]
  ring

theorem sdTransport_discriminant (P : SdTransportParameters) :
    discriminant (sdTransportParameters P) = discriminant P.val := by
  rw [← g₂_cubed_sub_g₃_sq, ← g₂_cubed_sub_g₃_sq,
    sdTransport_g₂, sdTransport_g₃]

theorem sdTransport_weierstrassCurve (P : SdTransportParameters) :
    weierstrassCurve (sdTransportParameters P) = weierstrassCurve P.val := by
  ext <;> simp [weierstrassCurve, sdTransport_g₂, sdTransport_g₃]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
