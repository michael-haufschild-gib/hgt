import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ExceptionalLogarithmicWindows
import GaloisForLFunctions.SurfaceOfSpecZ.TheEffectiveClassesOfThePrimePlanes

/-!
# Counts on logarithmic prime windows with exceptions

The natural-number count on the ray `Γ₁ + Γₚ` need only exist on arbitrarily
late logarithmic windows, after deleting a power-saving number of primes.
Its quadratic limit is nonnegative; the exceptional-window theorem then
forces RH. Under RH the floor of the quadratic defect supplies the count.
-/

open Filter Topology

noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri CountingHolography

/-- RH is equivalent to natural-number counts on the effective prime rays
in sparse logarithmic windows with independently chosen thin exceptions. -/
theorem riemannHypothesis_iff_effectiveCounts_logarithmic_windows_off_finset
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℝ,
      ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧ (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
        ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ primeLogarithmicRadius T →
          ∃ K : ℕ → ℕ, Tendsto (fun m : ℕ => (K m : ℝ) / (m : ℝ) ^ 2)
            atTop (𝓝 (planeDefect p (1, 1))) := by
  constructor
  · intro hRH
    refine ⟨0, le_rfl, fun U => ⟨U, ∅, le_rfl, by simp, ?_⟩⟩
    intro p hp _ _
    exact riemannHypothesis_iff_effectivePrimeCounts.mp hRH p hp
  · rintro ⟨C, hC, hcounts⟩
    apply (riemannHypothesis_iff_prime_logarithmic_windows_off_finset hδ hδ1).mpr
    refine ⟨2 * zetaScalingDatum.orbitCorr splineCycle 0, C, hC, fun U => ?_⟩
    obtain ⟨T, E, hT, hE, hcount⟩ := hcounts U
    refine ⟨T, E, hT, hE, fun p hp hpE hwin => ?_⟩
    obtain ⟨K, hK⟩ := hcount p hp hpE hwin
    have hnonneg : 0 ≤ planeDefect p (1, 1) :=
      ge_of_tendsto' hK fun m => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    rw [planeDefect_one_one] at hnonneg
    rw [← orbitCorr_eq_re_lagStructure_spline]
    linarith only [hnonneg]

#print axioms riemannHypothesis_iff_effectiveCounts_logarithmic_windows_off_finset

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
