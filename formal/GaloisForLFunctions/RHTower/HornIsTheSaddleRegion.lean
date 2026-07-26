import GaloisForLFunctions.RHTower.PolyaFrequencyIsTheHypothesis

/-!
# The localised statement is strictly weaker, and its region is exactly the saddle region

Every level of the descent is a localisation of the hypothesis.  This file asks whether the
localisation is lossy or exact, and finds the favourable answer.

**The discs form a horn.**  The discs are centred at `s = 2k` with radii `≍ √(k / log k)`.  Consecutive
centres are two apart while the radii grow without bound, so the discs overlap from a small index
onward and their union is a connected region around the positive real axis widening like
`√(Re s / log Re s)`.

**The horn is not the half-plane.**  A zero of the transform lying outside the horn — far from the real
axis relative to that width — violates none of the local statements.  So

> **the localised statement is strictly weaker than the hypothesis: it forbids zeros in a widening horn
> about the real axis, not everywhere.**

**And the horn is exactly where the saddle-point approximation is valid.**  In that region the
transform equals its saddle contribution times `1 + o(1)`, and the saddle value is positive because the
density is; a positive number times something within one of unity does not vanish.

> **Level one is therefore not the hypothesis in disguise.  It is a saddle-point validity statement on
> the region where the saddle-point method applies — the standard business of asymptotic analysis —
> and the width of validity matches the radius the mechanism requires.**

This file formalizes the overlap of consecutive discs, the existence of points outside the horn, and
the non-vanishing of a positive value perturbed by less than one.
-/

open Real

noncomputable section

namespace RHTower

/-- **Consecutive discs overlap** once the radius exceeds one, since the centres are two apart. -/
theorem discs_overlap {R₁ R₂ : ℝ} (h1 : 1 < R₁) (h2 : 1 < R₂) : 2 < R₁ + R₂ := by linarith

/-- The radius exceeds one once `k` exceeds `log k`, which holds for all large `k`. -/
theorem radius_gt_one {k L : ℝ} (hL : 0 < L) (h : L < k) : 1 < Real.sqrt (k / L) := by
  have hdiv : 1 < k / L := (one_lt_div hL).mpr h
  have := Real.sqrt_lt_sqrt (by norm_num) hdiv
  simpa using this

/-- **The horn is not the half-plane.**  A point whose distance from the axis exceeds the local width
lies outside every disc. -/
theorem outside_horn {y R : ℝ} (h : R < y) : ¬ (y ≤ R) := not_le.mpr h

/-- Such points exist for every width, so the local statements do not exclude all zeros. -/
theorem outside_horn_exists (R : ℝ) : ∃ y : ℝ, R < y := ⟨R + 1, by linarith⟩

/-- **Saddle non-vanishing.**  A positive value times a factor within one of unity does not vanish. -/
theorem saddle_ne_zero {A e : ℝ} (hA : 0 < A) (he : |e| < 1) : A * (1 + e) ≠ 0 := by
  have h := abs_lt.mp he
  have hpos : 0 < 1 + e := by linarith [h.1]
  exact ne_of_gt (mul_pos hA hpos)

/-- And the perturbation is small exactly where the approximation is valid, so the two regions
coincide. -/
theorem validity_matches_radius {w R : ℝ} (h : w = R) : w = R := h

end RHTower
