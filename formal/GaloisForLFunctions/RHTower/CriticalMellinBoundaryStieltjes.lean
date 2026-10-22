import GaloisForLFunctions.RHTower.CCM.CCMPolarPrimeStieltjesAutocorrelation

/-!
# The critical-Mellin Stieltjes pairing with its boundary term

The corpus integration-by-parts law
`criticalMellinStieltjesPairing_integrationByParts` assumes the test function vanishes at the
aperture endpoint.  Applying it to `F - F(2a)` and using the value of the pairing on constants
removes that assumption and exposes the boundary term:

```text
⟨F⟩_a = E_crit(2a) F(2a) - ∫_0^{2a} E_crit(h) F'(h) dh.
```

This is the form needed to pass to an infinite aperture, where the boundary term is killed by
decay of `F` rather than by support.
-/

namespace RHTower

open MeasureTheory Set Complex
open scoped BigOperators

noncomputable section

theorem continuousOn_of_hasDerivAt_Icc {F F' : ℝ → ℂ} {H : ℝ}
    (hF : ∀ x ∈ Set.Icc (0 : ℝ) H, HasDerivAt F (F' x) x) :
    ContinuousOn F (Set.Icc 0 H) :=
  fun x hx => (hF x hx).continuousAt.continuousWithinAt

theorem integrableOn_polarWeight_mul {F : ℝ → ℂ} {H : ℝ}
    (hFc : ContinuousOn F (Set.Icc 0 H)) :
    IntegrableOn (fun h : ℝ => F h * (2 * Real.cosh (h / 2) : ℂ)) (Ioc 0 H) := by
  have hcont : ContinuousOn (fun h : ℝ => F h * (2 * Real.cosh (h / 2) : ℂ))
      (Set.Icc 0 H) := hFc.mul (by fun_prop)
  exact (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

theorem criticalMellinStieltjesPairing_sub {a : ℝ} {F G : ℝ → ℂ}
    (hF : IntegrableOn (fun h : ℝ => F h * (2 * Real.cosh (h / 2) : ℂ)) (Ioc 0 (2 * a)))
    (hG : IntegrableOn (fun h : ℝ => G h * (2 * Real.cosh (h / 2) : ℂ)) (Ioc 0 (2 * a))) :
    criticalMellinStieltjesPairing a (fun h => F h - G h)
      = criticalMellinStieltjesPairing a F - criticalMellinStieltjesPairing a G := by
  unfold criticalMellinStieltjesPairing
  have hint : (∫ h in Ioc (0 : ℝ) (2 * a), (F h - G h) * (2 * Real.cosh (h / 2) : ℂ))
      = (∫ h in Ioc (0 : ℝ) (2 * a), F h * (2 * Real.cosh (h / 2) : ℂ))
        - ∫ h in Ioc (0 : ℝ) (2 * a), G h * (2 * Real.cosh (h / 2) : ℂ) := by
    rw [← MeasureTheory.integral_sub hF hG]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    ring
  have hsum : (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        (criticalMellinAtomWeight k : ℂ) * (F (Real.log k) - G (Real.log k)))
      = (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          (criticalMellinAtomWeight k : ℂ) * F (Real.log k))
        - ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          (criticalMellinAtomWeight k : ℂ) * G (Real.log k) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hint, hsum]
  ring

theorem criticalMellinStieltjesPairing_const {a : ℝ} (ha : 0 ≤ a) (z : ℂ) :
    criticalMellinStieltjesPairing a (fun _ => z)
      = z * (criticalMellinCompletedError (2 * a) : ℂ) := by
  have hone := criticalMellinStieltjesPairing_one (a := a) ha
  rw [← hone]
  unfold criticalMellinStieltjesPairing
  have hint : (∫ h in Ioc (0 : ℝ) (2 * a), z * (2 * Real.cosh (h / 2) : ℂ))
      = z * ∫ h in Ioc (0 : ℝ) (2 * a), (1 : ℂ) * (2 * Real.cosh (h / 2) : ℂ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    ring
  have hsum : (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        (criticalMellinAtomWeight k : ℂ) * z)
      = z * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        (criticalMellinAtomWeight k : ℂ) * (1 : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hint, hsum, mul_sub]

/-- **The Stieltjes pairing with its boundary term.**  No support or endpoint hypothesis. -/
theorem criticalMellinStieltjesPairing_boundary {a : ℝ} (ha : 0 ≤ a) {F F' : ℝ → ℂ}
    (hF : ∀ x ∈ Set.Icc (0 : ℝ) (2 * a), HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume 0 (2 * a)) :
    criticalMellinStieltjesPairing a F
      = (criticalMellinCompletedError (2 * a) : ℂ) * F (2 * a)
        - ∫ h in Ioc (0 : ℝ) (2 * a), (criticalMellinCompletedError h : ℂ) * F' h := by
  have hFc : ContinuousOn F (Set.Icc 0 (2 * a)) := continuousOn_of_hasDerivAt_Icc hF
  have hG : ∀ x ∈ Set.Icc (0 : ℝ) (2 * a),
      HasDerivAt (fun h => F h - F (2 * a)) (F' x) x := by
    intro x hx
    simpa using (hF x hx).sub_const (F (2 * a))
  have hzero : (fun h => F h - F (2 * a)) (2 * a) = 0 := by simp
  have hmain := criticalMellinStieltjesPairing_integrationByParts (a := a) ha hG hF' hzero
  have hsplit := criticalMellinStieltjesPairing_sub (a := a) (F := F) (G := fun _ => F (2 * a))
    (integrableOn_polarWeight_mul hFc)
    (integrableOn_polarWeight_mul (continuousOn_const))
  rw [hsplit, criticalMellinStieltjesPairing_const ha] at hmain
  linear_combination hmain

end

end RHTower
