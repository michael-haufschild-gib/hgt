import GaloisForLFunctions.FamilyContinuationTheory.AngularPlainIdealSums

/-! # Angular plain sums on completed cubic rows

Finite row closure retains the sextic infinity type. The resulting long-sum
estimate applies to every row, including rows with principal finite character.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
namespace GaloisForLFunctions.FamilyContinuationTheory
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open HeckeFamily HeckeRowClosure HeckeInverseAmplification
local notation "O" => Eisenstein.O

/-- A completed cubic row with an additional sextic infinity type. -/
def angularPlainRow (η : Character) (k : ℕ) (m f z : O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : NonzeroIdeal,
    (idealCoeff η I.val * CanonicalRowCompletion.idealRowHom (m ^ 6 * f ^ 4 * z) I.val) *
      idealPsiSix I.val ^ k * W ((Ideal.absNorm I.val : ℝ) / X)

/-- Row closure changes only the finite character, leaving the angular factor intact. -/
theorem angularPlainRow_eq (η χ : Character) (k : ℕ) (m f z : O)
    (hrow : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ → ℂ) (X : ℝ) :
    angularPlainRow η k m f z W X = grossenPlainIdealSum χ k W X := by
  unfold angularPlainRow grossenPlainIdealSum
  apply tsum_congr
  intro I
  rw [idealCoeff_eq_row η χ m f z hrow I.val]

private theorem modulus_decay_mono (A : ℕ) {N Q X : ℝ}
    (hN : 0 < N) (hNQ : N ≤ Q) (hX : 0 < X) :
    N / (1 + X / N) ^ A ≤ Q / (1 + X / Q) ^ A := by
  have hQ : 0 < Q := hN.trans_le hNQ
  calc
    _ ≤ Q / (1 + X / N) ^ A := by gcongr
    _ ≤ Q / (1 + X / Q) ^ A := by gcongr

/-- Every completed row of positive infinity type has rapid decay beyond its finite conductor. -/
theorem angularPlainRow_height_bound (k A : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) :
    ∃ (J : ℕ) (C : ℝ), 0 < C ∧ ∀ (η : Character) (m f z : O),
      m ≠ 0 → f ≠ 0 → z ≠ 0 → lambda ∣ m → (2 : O) ∣ m →
      ∀ (Q X : ℝ), (rowConductorBound η m f z : ℝ) ≤ Q → 0 < X →
      ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖angularPlainRow η (k + 1) m f z (twistProfile W σ t) X‖ ≤
        (C * (1 + ‖t‖) ^ J) * Q / (1 + X / Q) ^ A := by
  obtain ⟨J, C, hC, hb⟩ := grossenPlainIdealSum_height_bound k A W hW
  refine ⟨J, C, hC, ?_⟩
  intro η m f z hm hf hz hmLam hm2 Q X hQ hX σ hσ t
  obtain ⟨χ, hχ, hrow⟩ := exists_row_character_with_conductor η m f z hm hf hz hmLam hm2
  rw [angularPlainRow_eq η χ (k + 1) m f z hrow]
  have hN : 0 < (Ideal.absNorm χ.modulus : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  have hNQ : (Ideal.absNorm χ.modulus : ℝ) ≤ Q :=
    (show (Ideal.absNorm χ.modulus : ℝ) ≤ (rowConductorBound η m f z : ℝ) by
      exact_mod_cast hχ).trans hQ
  apply (hb χ X hX σ hσ t).trans
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
    (modulus_decay_mono A hN hNQ hX) (mul_nonneg hC.le (by positivity))

/-- The normalized product of the two plain slots in an angular moment source. -/
def angularPlainZeroRow (η : Character) (k : ℕ) (m f z : O)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  (Real.sqrt (X₁ * X₂) : ℂ)⁻¹ *
    (angularPlainRow η k m f z W₁ X₁ * angularPlainRow η k m f z W₂ X₂)

/-- Both plain slots decay on every row when their scales exceed its finite conductor. -/
theorem angularPlainZeroRow_height_bound (k A : ℕ) (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hW₁ : Function.support W₁ ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (hW₂ : Function.support W₂ ⊆ Set.Icc (1 / 2 : ℝ) 2) :
    ∃ (J : ℕ) (C : ℝ), 0 < C ∧ ∀ (η : Character) (m f z : O),
      m ≠ 0 → f ≠ 0 → z ≠ 0 → lambda ∣ m → (2 : O) ∣ m →
      ∀ (Q L X₁ X₂ : ℝ), (rowConductorBound η m f z : ℝ) ≤ Q →
      0 < L → L ≤ X₁ → L ≤ X₂ →
      ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖angularPlainZeroRow η (k + 1) m f z
        (twistProfile W₁ σ t) (twistProfile W₂ σ t) X₁ X₂‖ ≤
        (C * (1 + ‖t‖) ^ J) * Q ^ 2 /
          (Real.sqrt (X₁ * X₂) * (1 + L / Q) ^ (A + A)) := by
  obtain ⟨J₁, C₁, hC₁, hb₁⟩ := angularPlainRow_height_bound k A W₁ hW₁
  obtain ⟨J₂, C₂, hC₂, hb₂⟩ := angularPlainRow_height_bound k A W₂ hW₂
  refine ⟨J₁ + J₂, C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro η m f z hm hf hz hmLam hm2 Q L X₁ X₂ hQ hL hLX₁ hLX₂ σ hσ t
  have hX₁ := hL.trans_le hLX₁
  have hX₂ := hL.trans_le hLX₂
  have hQpos : 0 < Q := by
    obtain ⟨χ, hχ, _⟩ := exists_row_character_with_conductor η m f z hm hf hz hmLam hm2
    have hn : 0 < (Ideal.absNorm χ.modulus : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
    exact hn.trans_le ((show (Ideal.absNorm χ.modulus : ℝ) ≤
      (rowConductorBound η m f z : ℝ) by exact_mod_cast hχ).trans hQ)
  have h₁ := hb₁ η m f z hm hf hz hmLam hm2 Q X₁ hQ hX₁ σ hσ t
  have h₂ := hb₂ η m f z hm hf hz hmLam hm2 Q X₂ hQ hX₂ σ hσ t
  have h₁' : ‖angularPlainRow η (k + 1) m f z (twistProfile W₁ σ t) X₁‖ ≤
      C₁ * (1 + ‖t‖) ^ J₁ * Q / (1 + L / Q) ^ A := by
    apply h₁.trans
    gcongr
  have h₂' : ‖angularPlainRow η (k + 1) m f z (twistProfile W₂ σ t) X₂‖ ≤
      C₂ * (1 + ‖t‖) ^ J₂ * Q / (1 + L / Q) ^ A := by
    apply h₂.trans
    gcongr
  have hprod := mul_le_mul h₁' h₂' (norm_nonneg _) (by positivity)
  rw [angularPlainZeroRow, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_mul]
  calc
    _ ≤ (Real.sqrt (X₁ * X₂))⁻¹ *
        ((C₁ * (1 + ‖t‖) ^ J₁ * Q / (1 + L / Q) ^ A) *
          (C₂ * (1 + ‖t‖) ^ J₂ * Q / (1 + L / Q) ^ A)) :=
      mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = _ := by rw [pow_add, pow_add]; ring

end GaloisForLFunctions.FamilyContinuationTheory
