import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The sharp neutral signed-Gamma example

The signed archimedean Gamma orbit-charge phase law is realized sharply by the neutral ratio
`G_*(s) = Γ(2s) / Γ(s)²`.  Its two common-scale orbit charges are `+1` at the class `1/2 + ℤ` and
`-1` at the class `ℤ`: individually nonzero (so `G_*` is hypertranscendental) but summing to the
neutral total charge `0`.  The reduction to a single-orbit-pair closed form is the Legendre
duplication identity

`Γ(2s) / Γ(s)² = 2^(2s-1)/√π · Γ(s + 1/2) / Γ(s)`,

formalized here directly from mathlib's `Complex.Gamma_mul_Gamma_add_half`.  This exhibits the two
signed orbit exponents `+1` (on `Γ(s+1/2)`) and `-1` (on `Γ(s)`) explicitly.
-/

namespace GaloisForLFunctions

open Complex

/-- **Legendre duplication in ratio form (the sharp neutral example).**  For `Γ(s) ≠ 0`,
`Γ(2s)/Γ(s)²` reduces to the single common-scale orbit pair
`2^(2s-1)/√π · Γ(s+1/2)/Γ(s)`, whose two signed orbit charges are `+1` at `1/2 + ℤ` and `-1` at
`ℤ`. -/
theorem sharpNeutralGammaRatio (s : ℂ) (hs : Complex.Gamma s ≠ 0) :
    Complex.Gamma (2 * s) / Complex.Gamma s ^ (2 : ℕ)
      = (2 : ℂ) ^ (2 * s - 1) / (Real.sqrt Real.pi : ℂ) *
          (Complex.Gamma (s + 1 / 2) / Complex.Gamma s) := by
  have hdup := Complex.Gamma_mul_Gamma_add_half s
  have hpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2 : (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hpow : (2 : ℂ) ^ (2 * s - 1) = ((2 : ℂ) ^ (1 - 2 * s))⁻¹ := by
    rw [show 2 * s - 1 = -(1 - 2 * s) by ring, Complex.cpow_neg]
  rw [hpow]
  field_simp
  rw [show ((2 * s + 1) / 2 : ℂ) = s + 1 / 2 by ring]
  linear_combination -hdup

end GaloisForLFunctions
