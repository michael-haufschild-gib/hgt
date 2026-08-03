import GaloisForLFunctions.HTGeometry.MidpointConvexIntegral

/-!
# The midpoint rule for an integrand convex only in the interior

The midpoint comparison

```text
f((a+b)/2) · (b - a) ≤ ∫_a^b f
```

needs convexity only on the *open* interval, provided `f` is interval integrable.  This is what makes
it applicable to a kernel with an integrable singularity at an endpoint — `1/((A+t)√t)` at `t = 0`
being the case at hand, where no convexity statement on the closed interval is available at all.

The reflection argument is unchanged; only the comparison of integrals is made almost everywhere,
the two endpoints forming a null set.
-/

open MeasureTheory Set

namespace GaloisForLFunctions

/-- **The midpoint rule for an integrand convex on the open interval.** -/
theorem ConvexOn.midpoint_mul_le_integral_of_Ioo {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Set.Ioo a b) f) (hint : IntervalIntegrable f volume a b) :
    f ((a + b) / 2) * (b - a) ≤ ∫ t in a..b, f t := by
  have hintrefl : IntervalIntegrable (fun t => f (a + b - t)) volume a b := by
    have h := hint.comp_sub_left (a + b)
    simpa using h.symm
  have hrefl : (∫ t in a..b, f (a + b - t)) = ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_comp_sub_left f (a + b)]
    simp
  -- convexity at the midpoint of `t` and its reflection, for `t` in the open interval
  have hpt : ∀ t ∈ Set.Ioo a b, f ((a + b) / 2) ≤ (f t + f (a + b - t)) / 2 := by
    intro t ht
    have hrmem : a + b - t ∈ Set.Ioo a b := by
      obtain ⟨h1, h2⟩ := ht
      exact ⟨by linarith, by linarith⟩
    have hconv := hf.2 ht hrmem (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num : (1:ℝ) / 2 + 1 / 2 = 1)
    have hmid : ((1:ℝ) / 2) • t + ((1:ℝ) / 2) • (a + b - t) = (a + b) / 2 := by
      show (1:ℝ) / 2 * t + (1:ℝ) / 2 * (a + b - t) = (a + b) / 2
      ring
    have hconv' : f ((a + b) / 2) ≤ 1 / 2 * f t + 1 / 2 * f (a + b - t) := by
      calc f ((a + b) / 2) = f (((1:ℝ) / 2) • t + ((1:ℝ) / 2) • (a + b - t)) := by rw [hmid]
        _ ≤ ((1:ℝ) / 2) • f t + ((1:ℝ) / 2) • f (a + b - t) := hconv
        _ = 1 / 2 * f t + 1 / 2 * f (a + b - t) := by simp only [smul_eq_mul]
    linarith
  -- the open interval carries full measure inside the closed one
  have hmem : Set.Ioo a b ∈ ae (volume.restrict (Set.Icc a b)) := by
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioo.compl]
    refine measure_mono_null (t := ({a, b} : Set ℝ)) ?_ ?_
    · intro x hx
      obtain ⟨hxc, hxi⟩ := hx
      obtain ⟨h1, h2⟩ := hxi
      rcases eq_or_lt_of_le h1 with h | h
      · exact Or.inl h.symm
      · rcases eq_or_lt_of_le h2 with h' | h'
        · exact Or.inr h'
        · exact absurd (Set.mem_Ioo.mpr ⟨h, h'⟩) hxc
    · exact (Set.finite_singleton b).insert a |>.measure_zero volume
  have hae : (fun _ : ℝ => f ((a + b) / 2))
      ≤ᵐ[volume.restrict (Set.Icc a b)] fun t => (f t + f (a + b - t)) / 2 :=
    Filter.eventually_of_mem hmem hpt
  have hmono : (∫ _t in a..b, f ((a + b) / 2))
      ≤ ∫ t in a..b, (f t + f (a + b - t)) / 2 :=
    intervalIntegral.integral_mono_ae_restrict hab intervalIntegrable_const
      ((hint.add hintrefl).div_const 2) hae
  rw [intervalIntegral.integral_const] at hmono
  have hsplit : (∫ t in a..b, (f t + f (a + b - t)) / 2) = ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add hint hintrefl, hrefl]
    ring
  rw [hsplit] at hmono
  calc f ((a + b) / 2) * (b - a) = (b - a) • f ((a + b) / 2) := by
        rw [smul_eq_mul]; ring
    _ ≤ ∫ t in a..b, f t := hmono

end GaloisForLFunctions
