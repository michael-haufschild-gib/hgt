import GaloisForLFunctions.BezoutValuationIncidence.VasyuninReciprocityForAllModuliFromPronicCovariance

/-!
# Exact Vasyunin reciprocity: the error term is a residue-difference energy

Expanding the square of a difference of residues against the pronic measure and inserting the
Vasyunin second moments, all logarithmic main terms cancel except one. For all moduli
`m₁, m₂ ≥ 1`:

`π (V(m₂, m₁) + V(m₁, m₂)) + (m₂ - m₁)(log m₂ - log m₁) = Σ_{M ≥ 1} ((M mod m₁) - (M mod m₂))² / (M(M+1))`.

The reciprocity defect of the Nyman–Beurling cotangent sums is exactly the pronic energy of the
difference of the two residues, a nonnegative quantity. It is not an error term to be estimated
away. For `m₁ < m₂` the residues agree below `m₁` and differ by `m₁ ⌊M/m₁⌋ ≥ m₁` on `[m₁, m₂)`, so

`m₁ (m₂ - m₁) / m₂ ≤ π (V(m₂, m₁) + V(m₁, m₂)) + (m₂ - m₁) log(m₂/m₁) ≤ 4((m₁-1)²/m₁ + (m₂-1)²/m₂)`.

The defect has order at least `min(m₁, m₂)(1 - min/max)`. No bound below `O(m₁ + m₂)` can hold
for moduli of different sizes. The question of the frontier becomes the size of a pronic energy.
-/

open Finset RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The pronic energy of the difference of two residues. -/
def residueDifferenceEnergy (m₁ m₂ : ℕ) : ℝ :=
  ∑' M : ℕ, (((M % m₁ : ℕ) : ℝ) - ((M % m₂ : ℕ) : ℝ)) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1))

theorem hasSum_residueDifferenceEnergy {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    HasSum (fun M : ℕ => (((M % m₁ : ℕ) : ℝ) - ((M % m₂ : ℕ) : ℝ)) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)))
      (vasyuninSecondMoment m₁ m₁ - 2 * vasyuninSecondMoment m₁ m₂ +
        vasyuninSecondMoment m₂ m₂) := by
  have h := ((hasSum_natMod_mul_natMod_vasyunin h₁ h₁).sub
    ((hasSum_natMod_mul_natMod_vasyunin h₁ h₂).mul_left 2)).add
      (hasSum_natMod_mul_natMod_vasyunin h₂ h₂)
  exact h.congr_fun fun M => by ring

/-- **Exact Vasyunin reciprocity.** -/
theorem vasyunin_reciprocity_exact {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    Real.pi * (vasyuninSum m₂ m₁ + vasyuninSum m₁ m₂) +
        ((m₂ : ℝ) - m₁) * (Real.log m₂ - Real.log m₁) = residueDifferenceEnergy m₁ m₂ := by
  rw [residueDifferenceEnergy, (hasSum_residueDifferenceEnergy h₁ h₂).tsum_eq,
    vasyuninSecondMoment_self h₁, vasyuninSecondMoment_self h₂, vasyuninSecondMoment]
  ring

/-- The pronic mass of `[a, b)`: `Σ_{a ≤ M < b} 1/(M(M+1)) = 1/a - 1/b`. -/
theorem sum_Ico_pronic_mass {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    ∑ M ∈ Ico a b, 1 / ((M : ℝ) * ((M : ℝ) + 1)) = 1 / (a : ℝ) - 1 / (b : ℝ) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    have hb : (0 : ℝ) < b := by exact_mod_cast lt_of_lt_of_le ha hab
    push_cast
    field_simp
    ring

/-- **The reciprocity defect is at least `m₁(m₂ - m₁)/m₂`** for `m₁ < m₂`. -/
theorem residueDifferenceEnergy_ge {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₁₂ : m₁ < m₂) :
    (m₁ : ℝ) * ((m₂ : ℝ) - m₁) / m₂ ≤ residueDifferenceEnergy m₁ m₂ := by
  have h₂ : 0 < m₂ := lt_trans h₁ h₁₂
  have hS := hasSum_residueDifferenceEnergy h₁ h₂
  have hf0 : ∀ M : ℕ, 0 ≤ (((M % m₁ : ℕ) : ℝ) - ((M % m₂ : ℕ) : ℝ)) ^ 2 /
      ((M : ℝ) * ((M : ℝ) + 1)) := fun M => div_nonneg (sq_nonneg _) (by positivity)
  -- on `[m₁, m₂)` the residues differ by at least `m₁`
  have hband : ∀ M ∈ Ico m₁ m₂, (m₁ : ℝ) ^ 2 * (1 / ((M : ℝ) * ((M : ℝ) + 1))) ≤
      (((M % m₁ : ℕ) : ℝ) - ((M % m₂ : ℕ) : ℝ)) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)) := by
    intro M hM
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hM
    rw [Nat.mod_eq_of_lt hhi]
    have hd := Nat.mod_add_div M m₁
    have hq : 1 ≤ M / m₁ := (Nat.le_div_iff_mul_le h₁).mpr (by omega)
    have hgap : m₁ ≤ M - M % m₁ := by
      have : m₁ ≤ m₁ * (M / m₁) := Nat.le_mul_of_pos_right m₁ hq
      omega
    have hgapR : (m₁ : ℝ) ≤ (M : ℝ) - ((M % m₁ : ℕ) : ℝ) := by
      have hle : M % m₁ ≤ M := Nat.mod_le M m₁
      have := (Nat.cast_le (α := ℝ)).mpr hgap
      rw [Nat.cast_sub hle] at this
      exact this
    have hsq : (m₁ : ℝ) ^ 2 ≤ (((M % m₁ : ℕ) : ℝ) - (M : ℝ)) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) m₁]
    have hw : (0 : ℝ) ≤ 1 / ((M : ℝ) * ((M : ℝ) + 1)) :=
      one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg M) (by linarith [Nat.cast_nonneg (α := ℝ) M]))
    rw [show (((M % m₁ : ℕ) : ℝ) - (M : ℝ)) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)) =
      (((M % m₁ : ℕ) : ℝ) - (M : ℝ)) ^ 2 * (1 / ((M : ℝ) * ((M : ℝ) + 1))) from
        div_eq_mul_one_div _ _]
    exact mul_le_mul_of_nonneg_right hsq hw
  have hmass := sum_Ico_pronic_mass h₁ h₁₂.le
  calc (m₁ : ℝ) * ((m₂ : ℝ) - m₁) / m₂
      = (m₁ : ℝ) ^ 2 * (1 / (m₁ : ℝ) - 1 / (m₂ : ℝ)) := by
        have h1 : (m₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
        have h2 : (m₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
        field_simp
    _ = ∑ M ∈ Ico m₁ m₂, (m₁ : ℝ) ^ 2 * (1 / ((M : ℝ) * ((M : ℝ) + 1))) := by
        rw [← mul_sum, hmass]
    _ ≤ ∑ M ∈ Ico m₁ m₂, (((M % m₁ : ℕ) : ℝ) - ((M % m₂ : ℕ) : ℝ)) ^ 2 /
          ((M : ℝ) * ((M : ℝ) + 1)) := sum_le_sum hband
    _ ≤ residueDifferenceEnergy m₁ m₂ := by
        rw [residueDifferenceEnergy, hS.tsum_eq]
        exact sum_le_hasSum _ (fun M _ => hf0 M) hS

/-- **The reciprocity defect is at most `4((m₁-1)²/m₁ + (m₂-1)²/m₂)`.** -/
theorem residueDifferenceEnergy_le {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    residueDifferenceEnergy m₁ m₂ ≤ 4 * (((m₁ : ℝ) - 1) ^ 2 / m₁ + ((m₂ : ℝ) - 1) ^ 2 / m₂) := by
  have hS := hasSum_residueDifferenceEnergy h₁ h₂
  have h11 := hasSum_natMod_mul_natMod_vasyunin h₁ h₁
  have h22 := hasSum_natMod_mul_natMod_vasyunin h₂ h₂
  have hle := hasSum_le (fun M : ℕ => by
      have hw : (0 : ℝ) ≤ 1 / ((M : ℝ) * ((M : ℝ) + 1)) := by positivity
      show (((M % m₁ : ℕ) : ℝ) - ((M % m₂ : ℕ) : ℝ)) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)) ≤
        2 * (((M % m₁ : ℕ) : ℝ) * ((M % m₁ : ℕ) : ℝ) / ((M : ℝ) * ((M : ℝ) + 1))) +
          2 * (((M % m₂ : ℕ) : ℝ) * ((M % m₂ : ℕ) : ℝ) / ((M : ℝ) * ((M : ℝ) + 1)))
      rw [div_eq_mul_one_div _ ((M : ℝ) * ((M : ℝ) + 1)),
        div_eq_mul_one_div (_ * _) ((M : ℝ) * ((M : ℝ) + 1)),
        div_eq_mul_one_div (((M % m₂ : ℕ) : ℝ) * _) ((M : ℝ) * ((M : ℝ) + 1))]
      nlinarith [sq_nonneg (((M % m₁ : ℕ) : ℝ) + ((M % m₂ : ℕ) : ℝ)),
        mul_nonneg (sq_nonneg (((M % m₁ : ℕ) : ℝ) + ((M % m₂ : ℕ) : ℝ))) hw])
    hS ((h11.mul_left 2).add (h22.mul_left 2))
  rw [residueDifferenceEnergy, hS.tsum_eq]
  have hb₁ := vasyuninSecondMoment_self_le h₁
  have hb₂ := vasyuninSecondMoment_self_le h₂
  rw [mul_div_assoc] at hb₁ hb₂
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
