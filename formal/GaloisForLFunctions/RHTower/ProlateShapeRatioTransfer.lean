import GaloisForLFunctions.RHTower.ProlateCoordinateNormalization

/-!
# The normalisation transfer, for an arbitrary mode

The passage from the rescaled, amplitude-normalised profile to the eigenfunction's own variable uses
nothing about which mode is involved.  For any family `Φ` whatever, if the shape ratio of the
normalised profile over the growing window has a nonzero limit `L`, then

```text
√c · ( ∫_{-1}^{1} Φ_c )² / ∫_{-1}^{1} Φ_c²  ⟶  L .
```

The amplitude `Φ_c(0)` cannot vanish for large `c`: if it did the normalised profile would be
identically zero and its shape ratio would be `0`, contradicting `L ≠ 0`.

Stated this way the transfer applies to every index `j`, not only to the ground mode: the only input
is the profile limit for that mode.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **The normalisation transfer for an arbitrary family and an arbitrary nonzero limit.** -/
theorem tendsto_sqrt_mul_shapeRatio_of_normalized {Φ : ℝ → ℝ → ℝ} {L : ℝ} (hL : L ≠ 0)
    (h : Tendsto (fun c : ℝ =>
        (∫ xi in (-Real.sqrt c)..(Real.sqrt c), normalizedProlateProfile c (Φ c) xi) ^ 2
          / ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
            (normalizedProlateProfile c (Φ c) xi) ^ 2) atTop (𝓝 L)) :
    Tendsto (fun c : ℝ => Real.sqrt c *
        ((∫ u in (-1 : ℝ)..1, Φ c u) ^ 2 / ∫ u in (-1 : ℝ)..1, (Φ c u) ^ 2))
      atTop (𝓝 L) := by
  have hzero : ∀ c : ℝ, Φ c 0 = 0 →
      ((∫ xi in (-Real.sqrt c)..(Real.sqrt c), normalizedProlateProfile c (Φ c) xi) ^ 2
        / ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
          (normalizedProlateProfile c (Φ c) xi) ^ 2) = 0 := by
    intro c hc
    have hprof : ∀ xi : ℝ, normalizedProlateProfile c (Φ c) xi = 0 := by
      intro xi
      rw [normalizedProlateProfile, hc, div_zero]
    simp [hprof]
  have hratne : ∀ᶠ c : ℝ in atTop,
      ((∫ xi in (-Real.sqrt c)..(Real.sqrt c), normalizedProlateProfile c (Φ c) xi) ^ 2
        / ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
          (normalizedProlateProfile c (Φ c) xi) ^ 2) ≠ 0 :=
    h.eventually_ne hL
  refine h.congr' ?_
  filter_upwards [hratne, eventually_gt_atTop (0 : ℝ)] with c hcne hcpos
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.2 hcpos
  have hamp : Φ c 0 ≠ 0 := fun hcon => hcne (hzero c hcon)
  have hprof : ∀ xi : ℝ,
      normalizedProlateProfile c (Φ c) xi = (Φ c 0)⁻¹ * Φ c (xi / Real.sqrt c) := by
    intro xi
    rw [normalizedProlateProfile, prolateHermiteRescale, div_eq_inv_mul]
  have hdil := HTGeometry.shapeRatio_dilate (Φ c) (α := Real.sqrt c)
    (β := (Φ c 0)⁻¹) (ne_of_gt hsq) (inv_ne_zero hamp) 1
  rw [mul_one] at hdil
  calc ((∫ xi in (-Real.sqrt c)..(Real.sqrt c), normalizedProlateProfile c (Φ c) xi) ^ 2
        / ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
          (normalizedProlateProfile c (Φ c) xi) ^ 2)
      = ((∫ xi in (-Real.sqrt c)..(Real.sqrt c),
            (Φ c 0)⁻¹ * Φ c (xi / Real.sqrt c)) ^ 2
          / ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
            ((Φ c 0)⁻¹ * Φ c (xi / Real.sqrt c)) ^ 2) := by
        simp only [hprof]
    _ = Real.sqrt c * ((∫ u in (-1 : ℝ)..1, Φ c u) ^ 2
          / ∫ u in (-1 : ℝ)..1, (Φ c u) ^ 2) := hdil

end GaloisForLFunctions.RHTower

end
