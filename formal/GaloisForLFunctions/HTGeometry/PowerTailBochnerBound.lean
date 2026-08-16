import GaloisForLFunctions.HTGeometry.PowerTailIntegral

/-!
# The tail of a power-dominated Bochner integral

A profile dominated by `C|t|^{-q}` past a positive radius is integrable there when `q > 1`, and its
tail integral obeys the same estimate as the scalar majorant:

`‖∫_x^∞ f‖ ≤ C x^{1-q}/(q-1)`.

This is what turns the three-fold expansion into a decay statement: the remaining amplitude is
`O(t^{p-3})` after transport, so its tail past `x` is `O(x^{p-2})`, and one more power of the
propagator's decay makes the transported tail `O(x^{-2})`.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
/-- A profile dominated by a power tail past a positive radius is integrable there. -/
theorem integrableOn_of_powerTail_bound {f : ℝ → X} {C q x : ℝ} (hq : 1 < q) (hx : 0 < x)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioi x)))
    (hf : ∀ t ∈ Ioi x, ‖f t‖ ≤ C * |t| ^ (-q)) :
    IntegrableOn f (Ioi x) := by
  refine Integrable.mono' ((integrableOn_powerTail_Ioi hx hq).const_mul C) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hf t ht

/-- **The tail of a power-dominated profile.** -/
theorem norm_integral_Ioi_le_powerTail {f : ℝ → X} {C q x : ℝ} (hq : 1 < q) (hx : 0 < x)
    (hf : ∀ t ∈ Ioi x, ‖f t‖ ≤ C * |t| ^ (-q)) :
    ‖∫ t in Ioi x, f t‖ ≤ C * (x ^ (1 - q) / (q - 1)) := by
  have hint : IntegrableOn (fun t : ℝ => C * |t| ^ (-q)) (Ioi x) :=
    (integrableOn_powerTail_Ioi hx hq).const_mul C
  have hle := MeasureTheory.norm_integral_le_of_norm_le hint
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hf t ht)
  rwa [integral_const_mul, integral_powerTail_Ioi hx hq] at hle

end GaloisForLFunctions.HTGeometry
