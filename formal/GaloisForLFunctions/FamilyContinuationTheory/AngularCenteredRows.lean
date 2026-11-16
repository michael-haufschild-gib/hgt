import GaloisForLFunctions.FamilyContinuationTheory.AngularPlainRowBounds

/-!
# Centered angular plain rows

Both scale pairs have rapid decay at positive infinity type. Equal product scales
give one normalization, so centered rows inherit the same conductor decay without
an exceptional finite-principal term.
-/

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace GaloisForLFunctions.FamilyContinuationTheory
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open HeckeFamily HeckeRowClosure HeckeInverseAmplification
local notation "O" => Eisenstein.O

def angularCenteredRow (η : Character) (k : ℕ) (m f z : O)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*
    (angularPlainRow η k m f z W₁ X₁*angularPlainRow η k m f z W₂ X₂-
      angularPlainRow η k m f z W₁ Y₁*angularPlainRow η k m f z W₂ Y₂)

lemma angularCenteredRow_eq_sub (η : Character) (k : ℕ) (m f z : O)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (hprod : X₁*X₂=Y₁*Y₂) :
    angularCenteredRow η k m f z W₁ W₂ X₁ X₂ Y₁ Y₂=
      angularPlainZeroRow η k m f z W₁ W₂ X₁ X₂-
        angularPlainZeroRow η k m f z W₁ W₂ Y₁ Y₂ := by
  unfold angularCenteredRow angularPlainZeroRow
  rw [hprod,mul_sub]

/-- A common lower scale controls every centered positive-weight row, including finite-principal rows. -/
theorem angularCenteredRow_height_bound (k A : ℕ) (W₁ W₂ : SchwartzMap ℝ ℂ)
    (hW₁ : Function.support W₁⊆Set.Icc (1/2:ℝ) 2)
    (hW₂ : Function.support W₂⊆Set.Icc (1/2:ℝ) 2) :
    ∃(J : ℕ)(C : ℝ),0<C ∧ ∀(η : Character)(m f z : O),
      m≠0 → f≠0 → z≠0 → lambda∣m → (2:O)∣m →
      ∀(Q L X₁ X₂ Y₁ Y₂ : ℝ),(rowConductorBound η m f z:ℝ)≤Q → 0<L →
        L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=Y₁*Y₂ →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
      ‖angularCenteredRow η (k+1) m f z (twistProfile W₁ σ t) (twistProfile W₂ σ t)
        X₁ X₂ Y₁ Y₂‖≤
        (C*(1+‖t‖)^J)*Q^2/(Real.sqrt (X₁*X₂)*(1+L/Q)^(A+A)) := by
  obtain ⟨J,C,hC,hbound⟩ := angularPlainZeroRow_height_bound k A W₁ W₂ hW₁ hW₂
  refine ⟨J,2*C,by positivity,?_⟩
  intro η m f z hm hf hz hmLam hm2 Q L X₁ X₂ Y₁ Y₂ hQ hL hX₁ hX₂ hY₁ hY₂ hprod σ hσ t
  have hx := hbound η m f z hm hf hz hmLam hm2 Q L X₁ X₂ hQ hL hX₁ hX₂ σ hσ t
  have hy := hbound η m f z hm hf hz hmLam hm2 Q L Y₁ Y₂ hQ hL hY₁ hY₂ σ hσ t
  rw [←hprod] at hy
  rw [angularCenteredRow_eq_sub η (k+1) m f z _ _ X₁ X₂ Y₁ Y₂ hprod]
  exact ((norm_sub_le _ _).trans (add_le_add hx hy)).trans_eq (by ring)

end GaloisForLFunctions.FamilyContinuationTheory
