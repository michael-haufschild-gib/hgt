import GaloisForLFunctions.RHTower.Sieve.LogPolySetScaling

/-!
# Integral Halász–Montgomery in the Gallagher variable

`Sieve/LogPolySetScaling.setIntegral_normSq_logPoly_le_HM` states the bound over the preimage of a
set of Dirichlet frequencies.  Every frequency set produced by a ladder partition lives in the
Gallagher variable instead, so the statement is repackaged here over an arbitrary measurable set of
that variable: the only change is that the measure of the set is multiplied by `2π`.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- **Halász–Montgomery over a measurable set of Gallagher frequencies.**  The row mass is `2N`
plus the oscillation bound times the measure of the set — never times the height. -/
theorem setIntegral_normSq_logPoly_le_HM_window (a : ℕ → ℂ) {D : Finset ℕ} {N : ℕ} (hN : 1 ≤ N)
    (hD : D ⊆ Finset.Icc 1 N) {E : Set ℝ} (hE : MeasurableSet E) {W : ℝ}
    (hEs : E ⊆ Set.Icc (-W) W) {Ω : ℝ} (hΩ : 0 ≤ Ω) (ha : ∀ n, ‖a n‖ ≤ Ω) :
    (∫ w in E, ‖logPoly a D w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹
        * ((2 * (N : ℝ)
            + (((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
                + 3072 * (N : ℝ))
              * (2 * Real.pi * volume.real E)) * (Ω ^ 2 * (D.card : ℝ))) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hinv : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
  have hne : (2 * Real.pi) ≠ 0 := ne_of_gt hpi
  set S : Set ℝ := (fun v : ℝ => (2 * Real.pi)⁻¹ * v) ⁻¹' E with hSdef
  have hSm : MeasurableSet S := (measurable_const_mul _) hE
  have hpre : (fun v : ℝ => 2 * Real.pi * v) ⁻¹' S = E := by
    ext w
    simp only [hSdef, Set.mem_preimage]
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hSs : S ⊆ Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W) := by
    intro v hv
    have hmem : (2 * Real.pi)⁻¹ * v ∈ Set.Icc (-W) W := hEs hv
    rw [Set.mem_Icc] at hmem ⊢
    obtain ⟨h1, h2⟩ := hmem
    constructor
    · have := mul_le_mul_of_nonneg_left h1 hpi.le
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at this
      linarith
    · have := mul_le_mul_of_nonneg_left h2 hpi.le
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at this
      linarith
  have hvol : volume.real S = 2 * Real.pi * volume.real E := by
    rw [hSdef, volume_real_preimage_mul_left hinv, inv_inv]
  have hbase := setIntegral_normSq_logPoly_le_HM a hN hD hSm hSs hΩ ha
  rw [hpre, hvol] at hbase
  exact hbase

end

end RHTower.Sieve
