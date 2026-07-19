import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Sign-optimized distance between directions

A convergence statement about a one-dimensional subspace — a *direction* — can be recorded either
projectively, as the vanishing of an angle, or metrically, as the vanishing of a distance between
unit vectors.  The two differ only by the choice of sign of the representative, and that choice is
governed by the inner product alone:

```text
‖u ∓ w‖² = 2 ∓ 2⟪u, w⟫        for unit `u`, `w`,
```

so minimizing over the sign replaces `⟪u, w⟫` by `|⟪u, w⟫|` and gives

```text
min(‖u − w‖², ‖u + w‖²) = 2 − 2|⟪u, w⟫|.
```

Hence an angle tending to zero is the same statement as a sign-optimized distance tending to zero,
with the explicit rate `2ε` in the squared distance for an angle deficit `ε`.  The normalization is
carried out here as well, so the input may be a pair of nonzero vectors of arbitrary length rather
than unit vectors.
-/

namespace GaloisForLFunctions

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## The two signed distances -/

/-- The squared distance between unit vectors. -/
theorem norm_sub_sq_of_unit (u w : H) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ‖u - w‖ ^ 2 = 2 - 2 * inner ℝ u w := by
  rw [norm_sub_sq_real, hu, hw]
  ring

/-- The squared distance between a unit vector and the negative of a unit vector. -/
theorem norm_add_sq_of_unit (u w : H) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ‖u + w‖ ^ 2 = 2 + 2 * inner ℝ u w := by
  rw [norm_add_sq_real, hu, hw]
  ring

/-- **The sign-optimized distance between unit vectors depends only on the angle.**  Minimizing
over the sign of the second vector replaces the inner product by its absolute value. -/
theorem min_norm_sub_sq_of_unit (u w : H) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    min (‖u - w‖ ^ 2) (‖u + w‖ ^ 2) = 2 - 2 * |inner ℝ u w| := by
  rw [norm_sub_sq_of_unit u w hu hw, norm_add_sq_of_unit u w hu hw]
  by_cases h : 0 ≤ inner ℝ u w
  · rw [abs_of_nonneg h, min_eq_left (by linarith)]
  · rw [abs_of_neg (not_le.mp h), min_eq_right (by linarith)]
    ring

/-! ## The explicit sign -/

/-- **Sign choice.**  An angle deficit `ε` yields an explicit sign for which the squared distance
is at most `2ε`.  The sign is `+1` when the inner product is nonnegative and `-1` otherwise. -/
theorem exists_sign_norm_sub_sq_le_of_unit (u w : H) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    {ε : ℝ} (h : 1 - ε ≤ |inner ℝ u w|) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖u - σ • w‖ ^ 2 ≤ 2 * ε := by
  by_cases hpos : 0 ≤ inner ℝ u w
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [one_smul, norm_sub_sq_of_unit u w hu hw]
    rw [abs_of_nonneg hpos] at h
    linarith
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hneg := not_le.mp hpos
    rw [neg_one_smul, sub_neg_eq_add, norm_add_sq_of_unit u w hu hw]
    rw [abs_of_neg hneg] at h
    linarith

/-! ## Normalization -/

/-- Normalizing a nonzero vector produces a unit vector. -/
theorem norm_inv_norm_smul {v : H} (hv : v ≠ 0) : ‖(‖v‖)⁻¹ • v‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

/-- The sign-optimized distance between the normalizations of two nonzero vectors, in terms of the
unnormalized inner product. -/
theorem min_norm_sub_sq_normalize {u w : H} (hu : u ≠ 0) (hw : w ≠ 0) :
    min (‖(‖u‖)⁻¹ • u - (‖w‖)⁻¹ • w‖ ^ 2) (‖(‖u‖)⁻¹ • u + (‖w‖)⁻¹ • w‖ ^ 2)
      = 2 - 2 * (|inner ℝ u w| / (‖u‖ * ‖w‖)) := by
  rw [min_norm_sub_sq_of_unit _ _ (norm_inv_norm_smul hu) (norm_inv_norm_smul hw)]
  congr 2
  rw [real_inner_smul_left, real_inner_smul_right, abs_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)),
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w))]
  field_simp

/-! ## The asymptotic form -/

/-- **A vanishing angle is a vanishing sign-optimized distance.**  This is the passage from the
projective statement of directional convergence to its metric statement. -/
theorem tendsto_min_norm_sub_sq_of_unit {ι : Type*} {l : Filter ι} {u w : ι → H}
    (hu : ∀ i, ‖u i‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (h : Filter.Tendsto (fun i => |inner ℝ (u i) (w i)|) l (nhds 1)) :
    Filter.Tendsto (fun i => min (‖u i - w i‖ ^ 2) (‖u i + w i‖ ^ 2)) l (nhds 0) := by
  have h2 : Filter.Tendsto (fun i => 2 - 2 * |inner ℝ (u i) (w i)|) l (nhds (2 - 2 * 1)) :=
    Filter.Tendsto.sub tendsto_const_nhds (h.const_mul 2)
  norm_num at h2
  exact h2.congr fun i => (min_norm_sub_sq_of_unit (u i) (w i) (hu i) (hw i)).symm

/-- The same statement for the normalizations of nonzero vectors. -/
theorem tendsto_min_norm_sub_sq_normalize {ι : Type*} {l : Filter ι} {u w : ι → H}
    (hu : ∀ i, u i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (h : Filter.Tendsto (fun i => |inner ℝ (u i) (w i)| / (‖u i‖ * ‖w i‖)) l (nhds 1)) :
    Filter.Tendsto
      (fun i => min (‖(‖u i‖)⁻¹ • u i - (‖w i‖)⁻¹ • w i‖ ^ 2)
        (‖(‖u i‖)⁻¹ • u i + (‖w i‖)⁻¹ • w i‖ ^ 2)) l (nhds 0) :=
  tendsto_min_norm_sub_sq_of_unit (fun i => norm_inv_norm_smul (hu i))
    (fun i => norm_inv_norm_smul (hw i))
    (by
      refine h.congr fun i => ?_
      rw [real_inner_smul_left, real_inner_smul_right, abs_mul, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (u i))),
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (w i)))]
      field_simp)


/-! ## Directions in a plane

A constrained ground direction is pinned by being orthogonal to a single constraint normal inside a
two-dimensional space.  Relative to an orthonormal pair `{n, g}` spanning that plane, a vector
splits as `x = ⟪x,n⟫n + ⟪x,g⟫g`, so its squared length is the sum of the two squared components.
Consequently a vector whose normal component is small is, after normalization, close to `±g`: the
angle deficit is exactly the squared relative normal component.
-/

section Plane

variable {n g x : H}

/-- Pythagoras in the plane spanned by an orthonormal pair. -/
theorem inner_sq_add_inner_sq_of_mem_span
    (hn : ‖n‖ = 1) (hg : ‖g‖ = 1) (hng : inner ℝ n g = 0)
    (hx : x ∈ Submodule.span ℝ ({n, g} : Set H)) :
    inner ℝ x n ^ 2 + inner ℝ x g ^ 2 = ‖x‖ ^ 2 := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
  have hgn : inner ℝ g n = 0 := by rw [real_inner_comm]; exact hng
  have hxn : inner ℝ x n = a := by
    rw [← hab, inner_add_left, real_inner_smul_left, real_inner_smul_left, hgn,
      real_inner_self_eq_norm_sq, hn]
    ring
  have hxg : inner ℝ x g = b := by
    rw [← hab, inner_add_left, real_inner_smul_left, real_inner_smul_left, hng,
      real_inner_self_eq_norm_sq, hg]
    ring
  have hnorm : ‖x‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 2 [← hab]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hxn, hxg]
    ring
  rw [hxn, hxg, hnorm]

/-- **A small normal component forces alignment with the orthogonal direction.**  The angle
deficit against `g` is exactly the squared relative component along the normal `n`. -/
theorem inner_normalize_sq_eq_one_sub
    (hn : ‖n‖ = 1) (hg : ‖g‖ = 1) (hng : inner ℝ n g = 0)
    (hx : x ∈ Submodule.span ℝ ({n, g} : Set H)) (hx0 : x ≠ 0) :
    (inner ℝ x g / ‖x‖) ^ 2 = 1 - (inner ℝ x n / ‖x‖) ^ 2 := by
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  have h := inner_sq_add_inner_sq_of_mem_span hn hg hng hx
  field_simp
  linarith [h]

/-- The quantitative alignment bound: a relative normal component at most `δ` leaves an angle
deficit at most `δ²`. -/
theorem one_sub_sq_le_inner_normalize_sq
    (hn : ‖n‖ = 1) (hg : ‖g‖ = 1) (hng : inner ℝ n g = 0)
    (hx : x ∈ Submodule.span ℝ ({n, g} : Set H)) (hx0 : x ≠ 0)
    {δ : ℝ} (hδ : |inner ℝ x n| / ‖x‖ ≤ δ) :
    1 - δ ^ 2 ≤ (inner ℝ x g / ‖x‖) ^ 2 := by
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  have heq := inner_normalize_sq_eq_one_sub hn hg hng hx hx0
  have hsq : (inner ℝ x n / ‖x‖) ^ 2 ≤ δ ^ 2 := by
    have habs : |inner ℝ x n / ‖x‖| ≤ δ := by
      rw [abs_div, abs_of_pos hxn]
      exact hδ
    have hnn : (0 : ℝ) ≤ |inner ℝ x n / ‖x‖| := abs_nonneg _
    nlinarith [sq_abs (inner ℝ x n / ‖x‖)]
  linarith [heq, hsq]

end Plane

/-- The asymptotic sign-choice statement when the vectors are only eventually nonzero, which is
the form a family indexed by a growing parameter supplies. -/
theorem tendsto_min_norm_sub_sq_normalize_of_eventually {ι : Type*} {l : Filter ι} {u w : ι → H}
    (hu : ∀ᶠ i in l, u i ≠ 0) (hw : ∀ᶠ i in l, w i ≠ 0)
    (h : Filter.Tendsto (fun i => |inner ℝ (u i) (w i)| / (‖u i‖ * ‖w i‖)) l (nhds 1)) :
    Filter.Tendsto
      (fun i => min (‖(‖u i‖)⁻¹ • u i - (‖w i‖)⁻¹ • w i‖ ^ 2)
        (‖(‖u i‖)⁻¹ • u i + (‖w i‖)⁻¹ • w i‖ ^ 2)) l (nhds 0) := by
  have h2 : Filter.Tendsto
      (fun i => 2 - 2 * (|inner ℝ (u i) (w i)| / (‖u i‖ * ‖w i‖))) l (nhds (2 - 2 * 1)) :=
    Filter.Tendsto.sub tendsto_const_nhds (h.const_mul 2)
  norm_num at h2
  refine h2.congr' ?_
  filter_upwards [hu, hw] with i hui hwi
  exact (min_norm_sub_sq_normalize hui hwi).symm

/-- The sign-choice statement fed by the *squared* normalized alignment, which is the form a
Lagrange-identity computation produces (no square roots are taken upstream). -/
theorem tendsto_min_norm_sub_sq_normalize_of_inner_sq {ι : Type*} {l : Filter ι} {u w : ι → H}
    (hu : ∀ᶠ i in l, u i ≠ 0) (hw : ∀ᶠ i in l, w i ≠ 0)
    (h : Filter.Tendsto
      (fun i => inner ℝ (u i) (w i) ^ 2 / (‖u i‖ ^ 2 * ‖w i‖ ^ 2)) l (nhds 1)) :
    Filter.Tendsto
      (fun i => min (‖(‖u i‖)⁻¹ • u i - (‖w i‖)⁻¹ • w i‖ ^ 2)
        (‖(‖u i‖)⁻¹ • u i + (‖w i‖)⁻¹ • w i‖ ^ 2)) l (nhds 0) := by
  refine tendsto_min_norm_sub_sq_normalize_of_eventually hu hw ?_
  have hs : Filter.Tendsto
      (fun i => Real.sqrt (inner ℝ (u i) (w i) ^ 2 / (‖u i‖ ^ 2 * ‖w i‖ ^ 2))) l (nhds 1) := by
    have hc := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp h
    simpa using hc
  refine hs.congr' ?_
  filter_upwards [hu, hw] with i hui hwi
  have ha : (0 : ℝ) < ‖u i‖ := norm_pos_iff.mpr hui
  have hb : (0 : ℝ) < ‖w i‖ := norm_pos_iff.mpr hwi
  rw [show ‖u i‖ ^ 2 * ‖w i‖ ^ 2 = (‖u i‖ * ‖w i‖) ^ 2 by ring, ← div_pow,
    Real.sqrt_sq_eq_abs, abs_div, abs_of_pos (mul_pos ha hb)]

end GaloisForLFunctions
