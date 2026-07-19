import GaloisForLFunctions.HTGeometry.CompactDeterminacy

/-!
# Bounded powers confine the measure

If the integrals `∫ fⁿ dν` stay bounded for a nonnegative `f`, then `ν` gives no mass to `{f ≥ t}`
for any `t > 1`: on that set the integrand is at least `tⁿ`, so the mass is at most `C / tⁿ`, which
tends to zero.

This is the engine for confining a representing measure to the support of a compactly supported one:
taking `f` to be the normalised distance to the centre of the interval, boundedness of the powers is
inherited from the compactly supported measure through the shared moments.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

/-- **Bounded power integrals force the measure to vanish beyond `1`.** -/
theorem measure_ge_eq_zero_of_pow_integral_le {nu : Measure ℝ} [IsFiniteMeasure nu]
    {f : ℝ → ℝ} (hf : Measurable f) (hfnn : ∀ x, 0 ≤ f x)
    {C : ℝ} (hint : ∀ n : ℕ, Integrable (fun x => (f x) ^ n) nu)
    (hbound : ∀ n : ℕ, ∫ x, (f x) ^ n ∂nu ≤ C) {t : ℝ} (ht : 1 < t) :
    nu {x | t ≤ f x} = 0 := by
  set A : Set ℝ := {x | t ≤ f x} with hAdef
  have hA : MeasurableSet A := measurableSet_le measurable_const hf
  have hkey : ∀ n : ℕ, (nu A).toReal * t ^ n ≤ C := by
    intro n
    have hconst : ∫ _x in A, t ^ n ∂nu = (nu A).toReal * t ^ n := by
      rw [setIntegral_const, smul_eq_mul]
      rfl
    have hmono : ∫ _x in A, t ^ n ∂nu ≤ ∫ x in A, (f x) ^ n ∂nu := by
      refine setIntegral_mono_on ((integrable_const (t ^ n)).integrableOn)
        ((hint n).integrableOn) hA fun x hx => ?_
      exact pow_le_pow_left₀ (by linarith) hx n
    have hle : ∫ x in A, (f x) ^ n ∂nu ≤ ∫ x, (f x) ^ n ∂nu :=
      setIntegral_le_integral (hint n)
        (Filter.Eventually.of_forall fun x => pow_nonneg (hfnn x) n)
    rw [← hconst]
    exact le_trans hmono (le_trans hle (hbound n))
  by_contra hne
  have hpos : 0 < (nu A).toReal := by
    refine lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm ?_)
    simpa [ENNReal.toReal_eq_zero_iff, measure_ne_top nu A] using hne
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / (nu A).toReal) ht
  have hkn := hkey n
  rw [div_lt_iff₀ hpos] at hn
  nlinarith [hkn, hn]

end HTGeometry
