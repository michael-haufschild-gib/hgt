import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaPeriodScaling
import Mathlib.Tactic

/-!
# Modular invariant of Brizard's negative/classical parameter transform

The paper's rational `g₂,g₃` formulas yield the Legendre modular invariant.  Its extended-to-
classical map `m ↦ -m/(1-m)` preserves that invariant exactly.  Combined with the analytic period
scaling laws, this separates elliptic shape (the `j`-invariant) from curvature/lattice scale.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def legendreJ (m : ℝ) : ℝ :=
  256 * (1 - m + m ^ 2) ^ 3 / (m ^ 2 * (1 - m) ^ 2)

noncomputable def parameterJ (P : Parameters) : ℝ :=
  1728 * g₂ P ^ 3 / (g₂ P ^ 3 - 27 * g₃ P ^ 2)

/-- Brizard's rational invariants give the classical Legendre `j`-invariant. -/
theorem parameterJ_eq_legendreJ (P : Parameters) :
    parameterJ P = legendreJ P.modulus := by
  by_cases hm0 : P.modulus = 0
  · simp [parameterJ, legendreJ, g₂_cubed_sub_g₃_sq, discriminant, hm0]
  by_cases hm1 : P.modulus = 1
  · simp [parameterJ, legendreJ, g₂_cubed_sub_g₃_sq, discriminant, hm1]
  rw [parameterJ, g₂_cubed_sub_g₃_sq, g₂, discriminant, legendreJ]
  field_simp [P.q₀.ne_zero, hm0, hm1]
  ring

/-- Appendix A's negative-to-classical transform preserves elliptic shape. -/
theorem legendreJ_extendedToClassical (m : NegativeModulus) :
    legendreJ (extendedToClassical m) = legendreJ m := by
  have hm0 : (m : ℝ) ≠ 0 := ne_of_lt m.property
  have hm1 : (m : ℝ) ≠ 1 := ne_of_lt (lt_trans m.property zero_lt_one)
  have hden : 1 - (m : ℝ) ≠ 0 := sub_ne_zero.mpr hm1.symm
  change legendreJ (-((m : ℝ)) / (1 - (m : ℝ))) = legendreJ (m : ℝ)
  rw [legendreJ, legendreJ]
  field_simp [hm0, hm1, hden]
  ring

/-- The inverse classical-to-negative chart preserves the same invariant. -/
theorem legendreJ_classicalToExtended (n : ClassicalModulus) :
    legendreJ (classicalToExtended n) = legendreJ n := by
  have h := legendreJ_extendedToClassical (classicalToExtended n)
  rw [extendedToClassical_classicalToExtended] at h
  exact h.symm

/-- The complementary Legendre parameter has the same elliptic shape. -/
theorem legendreJ_one_sub (m : ℝ) : legendreJ (1 - m) = legendreJ m := by
  rw [legendreJ, legendreJ]
  congr 1 <;> ring

noncomputable def periodJ (L : PeriodPair) : ℂ :=
  1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)

/-- Analytic lattice homothety preserves the modular invariant, including singular convention. -/
theorem periodJ_scalePeriodPair (c : ℂˣ) (L : PeriodPair) :
    periodJ (scalePeriodPair c L) = periodJ L := by
  rw [periodJ, periodJ, scalePeriodPair_g₂, scalePeriodPair_g₃]
  have hc : (c : ℂ)⁻¹ ≠ 0 := inv_ne_zero c.ne_zero
  have hnum : (((c : ℂ)⁻¹ ^ 4 * L.g₂) ^ 3) =
      (c : ℂ)⁻¹ ^ 12 * L.g₂ ^ 3 := by ring
  have hden :
      ((c : ℂ)⁻¹ ^ 4 * L.g₂) ^ 3 -
          27 * ((c : ℂ)⁻¹ ^ 6 * L.g₃) ^ 2 =
        (c : ℂ)⁻¹ ^ 12 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by ring
  rw [hden, hnum]
  by_cases hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 0
  · rw [hΔ]
    simp
  · field_simp [hc, hΔ]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
