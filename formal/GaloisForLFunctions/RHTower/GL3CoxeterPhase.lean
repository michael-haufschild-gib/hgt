import GaloisForLFunctions.RHTower.GL3CoxeterCell

open Matrix

/-!
# Kloosterman phases in the Coxeter cell of `SL₃(ℤ)`

For `M ∈ SL₃(ℤ)` in the `w₃`-cell, with `A = M₂₀`, `B = M₂₁`, `C = M₂₂`, `p₀ = plk₀`, `D = plk₁`,
the three unipotent parameters of the Bruhat decomposition (`w3_bruhat`) reduce as follows:
- `M₁₀p₀ + M₁₁D = 0`, hence `D ∣ M₁₀` (`cell_row1_rel`, `plk1_dvd_row1`);
- writing `A = DA'`, `M₁₀ = Ds`: `M₁₂A' − sC = 1`, so the first left phase is `s/A'` with
  `s ≡ −C⁻¹ (mod A')` (`cell_phase1`);
- the right phase is `B/A = −p₀/D` (`cell_phase_right`);
- the second left phase is `M₀₂A' − M₀₀C/D` with `M₀₀p₀ + M₀₁D = 1`, i.e. `≡ −p₀⁻¹C/D (mod 1)`
  (`cell_phase2`).
These are the entries of the `w₃` Kloosterman sum `Σ e(m₁s/A' − m₂p₀⁻¹C/D − n₂p₀/D)`.
-/

namespace GaloisForLFunctions.RHTower.GL3

section Phase
variable {M : Matrix (Fin 3) (Fin 3) ℤ} (hM : M.det = 1) (hc : InW3Cell M)
include hM hc

/-- The middle row relation `M₁₀ p₀ + M₁₁ D = 0` (after dividing the vanishing minor by `A/D`). -/
theorem cell_row1_rel : M 1 0 * plk M 0 + M 1 1 * plk M 1 = 0 := by
  obtain ⟨A', hA'⟩ := plk1_dvd hM hc
  have hrel := cell_rel hc
  have h2 : M 1 0 * M 2 1 - M 1 1 * M 2 0 = 0 := by
    have := hc.2; simpa [plk] using this
  have hD := plk1_ne_zero hM hc
  -- `B · D = −A p₀ = −D A' p₀`, so `B = −A' p₀`
  have hB : M 2 1 = -(A' * plk M 0) := by
    have : plk M 1 * (M 2 1 + A' * plk M 0) = 0 := by
      rw [hA'] at hrel; linear_combination hrel
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hD
    · linear_combination h
  -- the minor: `M₁₀ B − M₁₁ A = −A'(M₁₀ p₀ + M₁₁ D) = 0`
  have hA0 : A' ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hA'; exact hc.1 hA'
  have : A' * (M 1 0 * plk M 0 + M 1 1 * plk M 1) = 0 := by
    rw [hB, hA'] at h2; linear_combination -h2
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hA0
  · exact h

/-- `D ∣ M₁₀`. -/
theorem plk1_dvd_row1 : plk M 1 ∣ M 1 0 := by
  have h := cell_row1_rel hM hc
  have hcop := cell_coprime hM hc
  have h1 : plk M 1 ∣ M 1 0 * plk M 0 := ⟨-(M 1 1), by linear_combination h⟩
  exact (IsCoprime.symm hcop).dvd_of_dvd_mul_right h1

/-- **The first Kloosterman phase.** Writing `A = D·A'` and `M₁₀ = D·s`, one has
`M₁₂A' − sC = 1`, so `s ≡ −C⁻¹ (mod A')` and the left phase `M₁₀/A = s/A'`. -/
theorem cell_phase1 :
    ∃ A' s : ℤ, M 2 0 = plk M 1 * A' ∧ M 1 0 = plk M 1 * s ∧ M 1 2 * A' - s * M 2 2 = 1 := by
  obtain ⟨A', hA'⟩ := plk1_dvd hM hc
  obtain ⟨s, hs⟩ := plk1_dvd_row1 hM hc
  refine ⟨A', s, hA', hs, ?_⟩
  have hD := plk1_ne_zero hM hc
  have hDdef : plk M 1 = M 1 2 * M 2 0 - M 1 0 * M 2 2 := by simp [plk]
  have : plk M 1 * (M 1 2 * A' - s * M 2 2 - 1) = 0 := by
    have e := hDdef; rw [hA', hs] at e; linear_combination -e
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hD
  · linear_combination h

/-- **The right Kloosterman phase.** `B/A = −p₀/D`. -/
theorem cell_phase_right : ((M 2 1 : ℚ) / M 2 0) = -((plk M 0 : ℤ) : ℚ) / ((plk M 1 : ℤ) : ℚ) := by
  have hA : (M 2 0 : ℚ) ≠ 0 := by exact_mod_cast hc.1
  have hD : ((plk M 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast plk1_ne_zero hM hc
  have hrel : ((M 2 0 * plk M 0 + M 2 1 * plk M 1 : ℤ) : ℚ) = 0 := by exact_mod_cast cell_rel hc
  push_cast at hrel
  field_simp
  linear_combination hrel

/-- **The second Kloosterman phase.** `(M₀₂A − M₀₀C)/D = M₀₂A' − M₀₀C/D`, and `M₀₀p₀ ≡ 1 (mod D)`;
so modulo `ℤ` the second left phase is `−M₀₀C/D` with `M₀₀ ≡ p₀⁻¹ (mod D)`. -/
theorem cell_phase2 :
    ∃ A' : ℤ, M 2 0 = plk M 1 * A' ∧
      (((M 0 2 : ℚ) * M 2 0 - M 0 0 * M 2 2) / ((plk M 1 : ℤ) : ℚ) =
        (M 0 2 * A' : ℤ) - (M 0 0 : ℚ) * M 2 2 / ((plk M 1 : ℤ) : ℚ)) ∧
      M 0 0 * plk M 0 + M 0 1 * plk M 1 = 1 := by
  obtain ⟨A', hA'⟩ := plk1_dvd hM hc
  refine ⟨A', hA', ?_, cell_det hM hc⟩
  have hD : ((plk M 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast plk1_ne_zero hM hc
  have hA'q : (M 2 0 : ℚ) = ((plk M 1 : ℤ) : ℚ) * A' := by exact_mod_cast hA'
  rw [hA'q]
  push_cast
  field_simp

end Phase

end GaloisForLFunctions.RHTower.GL3
