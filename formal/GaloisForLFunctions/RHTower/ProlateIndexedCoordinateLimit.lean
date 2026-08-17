import GaloisForLFunctions.RHTower.HermiteLineIntegral
import GaloisForLFunctions.RHTower.ProlateIndexedProfileIntegral
import GaloisForLFunctions.RHTower.ProlateShapeRatioTransfer

/-!
# The coordinate limit of the canonical indexed prolate mode

The normalization transfer is stated along the bandwidth; the canonical indexed family lives on the
aperture axis, and the bandwidth is a function of the aperture.  Since the transfer is a pointwise
dilation identity followed by a filter congruence, it holds along any filter on any index type,
with the bandwidth given by an arbitrary function that is eventually positive.

Instantiating it at the canonical family gives the coordinate limit at every even rung:

```text
√c · ( ∫_{−1}^{1} R_n )² / ∫_{−1}^{1} R_n²  →  (∫_ℝ φ_{2n})² / ∫_ℝ φ_{2n}² ,
```

a nonzero limit, because the even Hermite first moments do not vanish.  The `n = 0` case is the
ground coordinate limit already in the tree; this is the whole ladder.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **The normalization transfer along an arbitrary filter.**  The passage from the rescaled,
amplitude-normalized profile to the eigenfunction's own variable is a pointwise identity, so the
index type and the filter are irrelevant; only eventual positivity of the bandwidth is used. -/
theorem tendsto_sqrt_mul_shapeRatio_of_normalized' {ι : Type*} {L' : Filter ι}
    {Φ : ι → ℝ → ℝ} {c : ι → ℝ} {L : ℝ} (hL : L ≠ 0) (hc : ∀ᶠ i in L', 0 < c i)
    (h : Tendsto (fun i => (∫ xi in (-Real.sqrt (c i))..(Real.sqrt (c i)),
            normalizedProlateProfile (c i) (Φ i) xi) ^ 2
          / ∫ xi in (-Real.sqrt (c i))..(Real.sqrt (c i)),
            (normalizedProlateProfile (c i) (Φ i) xi) ^ 2) L' (𝓝 L)) :
    Tendsto (fun i => Real.sqrt (c i) *
        ((∫ u in (-1 : ℝ)..1, Φ i u) ^ 2 / ∫ u in (-1 : ℝ)..1, (Φ i u) ^ 2)) L' (𝓝 L) := by
  have hzero : ∀ i : ι, Φ i 0 = 0 →
      ((∫ xi in (-Real.sqrt (c i))..(Real.sqrt (c i)), normalizedProlateProfile (c i) (Φ i) xi) ^ 2
        / ∫ xi in (-Real.sqrt (c i))..(Real.sqrt (c i)),
          (normalizedProlateProfile (c i) (Φ i) xi) ^ 2) = 0 := by
    intro i hi
    have hprof : ∀ xi : ℝ, normalizedProlateProfile (c i) (Φ i) xi = 0 := by
      intro xi
      rw [normalizedProlateProfile, hi, div_zero]
    simp [hprof]
  have hratne : ∀ᶠ i in L',
      ((∫ xi in (-Real.sqrt (c i))..(Real.sqrt (c i)), normalizedProlateProfile (c i) (Φ i) xi) ^ 2
        / ∫ xi in (-Real.sqrt (c i))..(Real.sqrt (c i)),
          (normalizedProlateProfile (c i) (Φ i) xi) ^ 2) ≠ 0 :=
    h.eventually_ne hL
  refine h.congr' ?_
  filter_upwards [hratne, hc] with i hine hipos
  have hsq : 0 < Real.sqrt (c i) := Real.sqrt_pos.2 hipos
  have hamp : Φ i 0 ≠ 0 := fun hcon => hine (hzero i hcon)
  have hprof : ∀ xi : ℝ,
      normalizedProlateProfile (c i) (Φ i) xi = (Φ i 0)⁻¹ * Φ i (xi / Real.sqrt (c i)) := by
    intro xi
    rw [normalizedProlateProfile, prolateHermiteRescale, div_eq_inv_mul]
  have hdil := HTGeometry.shapeRatio_dilate (Φ i) (α := Real.sqrt (c i))
    (β := (Φ i 0)⁻¹) (ne_of_gt hsq) (inv_ne_zero hamp) 1
  rw [mul_one] at hdil
  calc ((∫ xi in (-Real.sqrt (c i))..(Real.sqrt (c i)),
        normalizedProlateProfile (c i) (Φ i) xi) ^ 2
        / ∫ xi in (-Real.sqrt (c i))..(Real.sqrt (c i)),
          (normalizedProlateProfile (c i) (Φ i) xi) ^ 2)
      = ((∫ xi in (-Real.sqrt (c i))..(Real.sqrt (c i)),
            (Φ i 0)⁻¹ * Φ i (xi / Real.sqrt (c i))) ^ 2
          / ∫ xi in (-Real.sqrt (c i))..(Real.sqrt (c i)),
            ((Φ i 0)⁻¹ * Φ i (xi / Real.sqrt (c i))) ^ 2) := by
        simp only [hprof]
    _ = Real.sqrt (c i) * ((∫ u in (-1 : ℝ)..1, Φ i u) ^ 2
          / ∫ u in (-1 : ℝ)..1, (Φ i u) ^ 2) := hdil

/-- The limiting shape ratio of an even Hermite rung is not zero. -/
theorem hermiteShapeRatio_ne_zero (n : ℕ) :
    (∫ x, hermiteFun (2 * n) x) ^ 2 / ∫ x, hermiteFun (2 * n) x ^ 2 ≠ 0 := by
  have hnum : (∫ x, hermiteFun (2 * n) x) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (integral_hermiteFun_two_mul_ne_zero n)
  exact div_ne_zero hnum (integral_hermiteFun_sq_pos_line (2 * n)).ne'

/-- **The coordinate limit of the canonical indexed prolate mode.**  In the eigenfunction's own
variable, the normalized shape ratio of the `n`-th canonical even mode converges to the shape ratio
of the `2n`-th Hermite function, which is nonzero. -/
theorem tendsto_indexedRung_coordinateLimit (n : ℕ) :
    Tendsto (fun a : ProlatePositiveAperture => Real.sqrt (indexedOscillatorBandwidth a) *
        ((∫ u in (-1 : ℝ)..1, (signedModeRadialData (a : ℝ) n).R u) ^ 2
          / ∫ u in (-1 : ℝ)..1, ((signedModeRadialData (a : ℝ) n).R u) ^ 2))
      atTop (𝓝 ((∫ x, hermiteFun (2 * n) x) ^ 2 / ∫ x, hermiteFun (2 * n) x ^ 2)) := by
  refine tendsto_sqrt_mul_shapeRatio_of_normalized'
    (Φ := fun a : ProlatePositiveAperture => (signedModeRadialData (a : ℝ) n).R)
    (c := indexedOscillatorBandwidth) (hermiteShapeRatio_ne_zero n)
    (Filter.Eventually.of_forall fun a => indexedOscillatorBandwidth_pos a) ?_
  exact tendsto_indexedRung_shapeRatio n

end GaloisForLFunctions.RHTower

end
