import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ExceptionalLogarithmicWindows

/-! Absolute bounds on logarithmic prime windows detect the exact zero
width even after independently deleting power-thin sets in each window. -/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The exact width criterion with absolute values and thin exceptions. -/
theorem zeta_re_le_iff_abs_prime_logarithmic_power_windows_off_finset
    {σ δ : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) ↔
      ∃ K C : ℝ, 0 ≤ C ∧ ∀ U : ℝ, ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧
        (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
        ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ primeLogarithmicRadius T →
          |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤
            K * (p : ℝ) ^ σ := by
  constructor
  · intro hwidth
    obtain ⟨K, hK⟩ := (zeta_re_le_iff_abs_prime_logarithmic_power_windows hσ).mp hwidth
    refine ⟨K, 0, le_rfl, fun U => ?_⟩
    obtain ⟨T, hT, hbound⟩ := hK U
    exact ⟨T, ∅, hT, by simp, fun p hp _ hwin => hbound p hp hwin⟩
  · rintro ⟨K, C, hC, hK⟩
    apply (zeta_re_le_iff_prime_logarithmic_power_windows_off_finset hσ hδ hδ1).mpr
    refine ⟨K, C, hC, fun U => ?_⟩
    obtain ⟨T, E, hT, hE, hbound⟩ := hK U
    exact ⟨T, E, hT, hE, fun p hp hpE hwin => (abs_le.mp (hbound p hp hpE hwin)).1⟩

/-- Bounded absolute prime correlations on sparse windows with exceptions
are equivalent to RH, with no attainment or separation assumption. -/
theorem riemannHypothesis_iff_abs_prime_logarithmic_windows_off_finset
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    RiemannHypothesis ↔ ∃ K C : ℝ, 0 ≤ C ∧ ∀ U : ℝ,
      ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧ (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
        ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ primeLogarithmicRadius T →
          |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ K := by
  constructor
  · intro hRH
    obtain ⟨K, hK⟩ := riemannHypothesis_iff_abs_prime_logarithmic_windows.mp hRH
    refine ⟨K, 0, le_rfl, fun U => ?_⟩
    obtain ⟨T, hT, hbound⟩ := hK U
    exact ⟨T, ∅, hT, by simp, fun p hp _ hwin => hbound p hp hwin⟩
  · rintro ⟨K, C, hC, hK⟩
    apply (riemannHypothesis_iff_prime_logarithmic_windows_off_finset hδ hδ1).mpr
    refine ⟨K, C, hC, fun U => ?_⟩
    obtain ⟨T, E, hT, hE, hbound⟩ := hK U
    exact ⟨T, E, hT, hE, fun p hp hpE hwin => (abs_le.mp (hbound p hp hpE hwin)).1⟩

#print axioms zeta_re_le_iff_abs_prime_logarithmic_power_windows_off_finset
#print axioms riemannHypothesis_iff_abs_prime_logarithmic_windows_off_finset

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
