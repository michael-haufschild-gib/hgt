import GaloisForLFunctions.FamilyContinuationTheory.AngularPlainRowBounds
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.RadialEligibleEnergy

/-! # Radial energy of angular plain rows

The two plain slots admit a conductor-controlled radial energy estimate at every
positive infinity type. No exceptional set of finite-principal rows is removed.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
namespace GaloisForLFunctions.FamilyContinuationTheory
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open HeckeFamily HeckeRowClosure HeckeInverseAmplification InversePrincipalEnergy SchwartzPlanePoisson
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => Eisenstein.O

/-- Radial energy of the two normalized plain slots with sextic infinity type. -/
def angularPlainEnergy (η : Character) (k : ℕ) (m f a : O)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (r : Radial) : ℝ :=
  ∑' z : O, if r.keep z then
    ‖angularPlainZeroRow η k m f (a * z) W₁ W₂ X₁ X₂‖ ^ 2 *
      (r.profile (‖ringComplex z‖ ^ 2 / r.scale)).re else 0

/-- A common finite-conductor bound controls every radial row without a principal exception. -/
theorem angularPlainEnergy_height_bound (k A : ℕ) (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hW₁ : Function.support W₁ ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (hW₂ : Function.support W₂ ⊆ Set.Icc (1 / 2 : ℝ) 2) :
    ∃ (J : ℕ) (C : ℝ), 0 < C ∧ ∀ (η : Character) (m f a : O),
      m ≠ 0 → f ≠ 0 → a ≠ 0 → lambda ∣ m → (2 : O) ∣ m →
      ∀ (r : Radial) (Q L X₁ X₂ : ℝ), 0 < Q → 0 < L → L ≤ X₁ → L ≤ X₂ →
      (∀ z, r.keep z → z ≠ 0) →
      (∀ z, r.keep z → r.profile (‖ringComplex z‖ ^ 2 / r.scale) ≠ 0 →
        (rowConductorBound η m f (a * z) : ℝ) ≤ Q) →
      ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      angularPlainEnergy η (k + 1) m f a
        (twistProfile W₁ σ t) (twistProfile W₂ σ t) X₁ X₂ r ≤
        diagonalControl r.profile * max 1 r.scale *
          ((C * (1 + ‖t‖) ^ J) * Q ^ 2 /
            (Real.sqrt (X₁ * X₂) * (1 + L / Q) ^ (A + A))) ^ 2 := by
  obtain ⟨J, C, hC, hb⟩ := angularPlainZeroRow_height_bound k A W₁ W₂ hW₁ hW₂
  refine ⟨J, C, hC, ?_⟩
  intro η m f a hm hf ha hmLam hm2 r Q L X₁ X₂ hQ hL hX₁ hX₂ hnz hmod σ hσ t
  let r' : Radial := { r with
    keep := fun z => r.keep z ∧ r.profile (‖ringComplex z‖ ^ 2 / r.scale) ≠ 0 }
  have heq : angularPlainEnergy η (k + 1) m f a
      (twistProfile W₁ σ t) (twistProfile W₂ σ t) X₁ X₂ r =
      angularPlainEnergy η (k + 1) m f a
        (twistProfile W₁ σ t) (twistProfile W₂ σ t) X₁ X₂ r' := by
    unfold angularPlainEnergy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · by_cases hp : r.profile (‖ringComplex z‖ ^ 2 / r.scale) = 0
      · simp only [r', hk, hp, ne_eq, not_true_eq_false, and_false, if_false, if_true,
          Complex.zero_re, mul_zero]
      · simp only [r', hk, hp, ne_eq, not_false_eq_true, and_self, if_true]
    · simp only [r', hk, false_and, if_false]
  rw [heq]
  apply CenteredMomentPlainGlobalEnergy.radial_bound_on_keep
    (fun z => angularPlainZeroRow η (k + 1) m f (a * z)
      (twistProfile W₁ σ t) (twistProfile W₂ σ t) X₁ X₂) r'
    (((C * (1 + ‖t‖) ^ J) * Q ^ 2) /
      (Real.sqrt (X₁ * X₂) * (1 + L / Q) ^ (A + A))) (by positivity)
  intro z hz
  exact hb η m f (a * z) hm hf (mul_ne_zero ha (hnz z hz.1)) hmLam hm2
    Q L X₁ X₂ (hmod z hz.1 hz.2) hL hX₁ hX₂ σ hσ t

/-- Compact radial support supplies the conductor bound explicitly from the row norm. -/
theorem angularPlainEnergy_compact_height_bound (k A : ℕ) (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hW₁ : Function.support W₁ ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (hW₂ : Function.support W₂ ⊆ Set.Icc (1 / 2 : ℝ) 2) :
    ∃ (J : ℕ) (C : ℝ), 0 < C ∧ ∀ (η : Character) (m f a : O),
      m ≠ 0 → f ≠ 0 → a ≠ 0 → lambda ∣ m → (2 : O) ∣ m →
      ∀ (r : Radial) (b L X₁ X₂ : ℝ), 0 < b → 0 < L → L ≤ X₁ → L ≤ X₂ →
      Function.support r.profile ⊆ Set.Iic b → (∀ z, r.keep z → z ≠ 0) →
      ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      let Q : ℝ := (rowConductorBound η m f a : ℝ) * b * r.scale
      angularPlainEnergy η (k + 1) m f a
        (twistProfile W₁ σ t) (twistProfile W₂ σ t) X₁ X₂ r ≤
        diagonalControl r.profile * max 1 r.scale *
          ((C * (1 + ‖t‖) ^ J) * Q ^ 2 /
            (Real.sqrt (X₁ * X₂) * (1 + L / Q) ^ (A + A))) ^ 2 := by
  obtain ⟨J, C, hC, hb⟩ := angularPlainEnergy_height_bound k A W₁ W₂ hW₁ hW₂
  refine ⟨J, C, hC, ?_⟩
  intro η m f a hm hf ha hmLam hm2 r b L X₁ X₂ hB hL hX₁ hX₂ hs hnz σ hσ t Q
  obtain ⟨χ, hχ, _⟩ := exists_row_character_with_conductor η m f a hm hf ha hmLam hm2
  have hN : 0 < (Ideal.absNorm χ.modulus : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  have hbase : 0 < (rowConductorBound η m f a : ℝ) :=
    hN.trans_le (by exact_mod_cast hχ)
  have hQ : 0 < Q := mul_pos (mul_pos hbase hB) r.scale_pos
  apply hb η m f a hm hf ha hmLam hm2 r Q L X₁ X₂ hQ hL hX₁ hX₂ hnz ?_ σ hσ t
  intro z _ hp
  have hnorm : ((Ideal.span {z}).absNorm : ℝ) ≤ b * r.scale := by
    rw [← ringComplex_norm_sq_eq_absNorm_span]
    exact (div_le_iff₀ r.scale_pos).mp (hs hp)
  have heq : (rowConductorBound η m f (a * z) : ℝ) =
      (rowConductorBound η m f a : ℝ) * ((Ideal.span {z}).absNorm : ℝ) := by
    simp only [rowConductorBound, ← Ideal.span_singleton_mul_span_singleton,
      map_mul, Nat.cast_mul]
    ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hnorm hbase.le).trans_eq (by dsimp only [Q]; ring)

end GaloisForLFunctions.FamilyContinuationTheory
