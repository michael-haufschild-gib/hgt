import GaloisForLFunctions.HTGeometry.PositiveExpSumLogConvex

/-!
# The Legendre profile of the cosine cap

On the arc `|u| ≤ π/2` the function `u ↦ log (2 cos u)` is the concave "cap" that a positive
exponential sum must dominate once a conjugate pair of complex exponents enters the comparison.
Its Legendre transform

`Φ(x) = sup_{|u| < π/2} ( log 2 + log cos u - x u ) = log 2 - ½ log (1 + x²) + x arctan x`

is computed here in closed form.  The supremum is attained at the unique point `u = -arctan x`,
where the tangent to the cap has slope `x`; this is the exact tangency that will later separate a
convex `log R` from the cap by a single exponential.

Equivalently: `2 cos u ≤ e^{Φ(x)} e^{x u}` on the arc, with equality exactly at `u = -arctan x`,
and `Φ(x)` is the smallest constant for which this holds.
-/

open Set Real

namespace GaloisForLFunctions.HTGeometry

/-- The Legendre profile of the cosine cap. -/
noncomputable def capProfile (x : ℝ) : ℝ :=
  Real.log 2 - (1 / 2) * Real.log (1 + x ^ 2) + x * Real.arctan x

theorem capProfile_eq_log_cos (x : ℝ) :
    capProfile x = Real.log 2 + Real.log (Real.cos (Real.arctan x)) + x * Real.arctan x := by
  rw [capProfile, Real.cos_arctan, Real.log_div one_ne_zero (by positivity),
    Real.log_one, Real.log_sqrt (by positivity)]
  ring

@[simp] theorem capProfile_zero : capProfile 0 = Real.log 2 := by
  simp [capProfile]

theorem capProfile_neg (x : ℝ) : capProfile (-x) = capProfile x := by
  simp [capProfile, Real.arctan_neg]

/-! ## The tangency point -/

private theorem arctan_mem (x : ℝ) : -Real.arctan x ∈ Ioo (-(π / 2)) (π / 2) :=
  ⟨by have := Real.arctan_lt_pi_div_two x; linarith,
   by have := Real.neg_pi_div_two_lt_arctan x; linarith⟩

private theorem hasDerivAt_capFn (x : ℝ) {u : ℝ} (hu : u ∈ Ioo (-(π / 2)) (π / 2)) :
    HasDerivAt (fun w => x * w - Real.log (Real.cos w)) (x + Real.tan u) u := by
  have hcos : Real.cos u ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo hu)
  have h1 : HasDerivAt (fun w : ℝ => x * w) x u := by
    simpa using (hasDerivAt_id u).const_mul x
  have h2 : HasDerivAt (fun w : ℝ => Real.log (Real.cos w)) (-Real.sin u / Real.cos u) u :=
    (Real.hasDerivAt_cos u).log hcos
  refine (h1.sub h2).congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]
  ring

private theorem continuousOn_capFn (x : ℝ) {A : Set ℝ} (hA : A ⊆ Ioo (-(π / 2)) (π / 2)) :
    ContinuousOn (fun w => x * w - Real.log (Real.cos w)) A := fun _ hu =>
  ((hasDerivAt_capFn x (hA hu)).continuousAt).continuousWithinAt

/-- **The tangency.**  For each slope `x` the function `u ↦ x u - log cos u` attains its minimum on
the open arc at the single point `u = -arctan x`. -/
theorem capFn_min (x : ℝ) {u : ℝ} (hu : u ∈ Ioo (-(π / 2)) (π / 2)) :
    x * (-Real.arctan x) - Real.log (Real.cos (-Real.arctan x))
      ≤ x * u - Real.log (Real.cos u) := by
  have hvmem : -Real.arctan x ∈ Ioo (-(π / 2)) (π / 2) := arctan_mem x
  have htanv : Real.tan (-Real.arctan x) = -x := by rw [Real.tan_neg, Real.tan_arctan]
  rcases lt_trichotomy u (-Real.arctan x) with h | h | h
  · have hsub : Icc u (-Real.arctan x) ⊆ Ioo (-(π / 2)) (π / 2) := fun w hw =>
      ⟨lt_of_lt_of_le hu.1 hw.1, lt_of_le_of_lt hw.2 hvmem.2⟩
    have hanti : StrictAntiOn (fun w => x * w - Real.log (Real.cos w))
        (Icc u (-Real.arctan x)) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuousOn_capFn x hsub) ?_
      intro w hw
      rw [interior_Icc] at hw
      have hwmem : w ∈ Ioo (-(π / 2)) (π / 2) := hsub (Ioo_subset_Icc_self hw)
      rw [(hasDerivAt_capFn x hwmem).deriv]
      have hlt : Real.tan w < Real.tan (-Real.arctan x) :=
        Real.tan_lt_tan_of_lt_of_lt_pi_div_two hwmem.1 hvmem.2 hw.2
      rw [htanv] at hlt
      linarith
    exact le_of_lt (hanti (left_mem_Icc.mpr h.le) (right_mem_Icc.mpr h.le) h)
  · rw [h]
  · have hsub : Icc (-Real.arctan x) u ⊆ Ioo (-(π / 2)) (π / 2) := fun w hw =>
      ⟨lt_of_lt_of_le hvmem.1 hw.1, lt_of_le_of_lt hw.2 hu.2⟩
    have hmono : StrictMonoOn (fun w => x * w - Real.log (Real.cos w))
        (Icc (-Real.arctan x) u) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_capFn x hsub) ?_
      intro w hw
      rw [interior_Icc] at hw
      have hwmem : w ∈ Ioo (-(π / 2)) (π / 2) := hsub (Ioo_subset_Icc_self hw)
      rw [(hasDerivAt_capFn x hwmem).deriv]
      have hlt : Real.tan (-Real.arctan x) < Real.tan w :=
        Real.tan_lt_tan_of_lt_of_lt_pi_div_two hvmem.1 hwmem.2 hw.1
      rw [htanv] at hlt
      linarith
    exact le_of_lt (hmono (left_mem_Icc.mpr h.le) (right_mem_Icc.mpr h.le) h)

/-! ## The profile bound -/

/-- **The cap is dominated by its Legendre profile**, on the open arc. -/
theorem log_cos_sub_le_capProfile (x : ℝ) {u : ℝ} (hu : u ∈ Ioo (-(π / 2)) (π / 2)) :
    Real.log 2 + Real.log (Real.cos u) - x * u ≤ capProfile x := by
  have h := capFn_min x hu
  rw [Real.cos_neg] at h
  rw [capProfile_eq_log_cos]
  linarith

/-- The profile value is attained at the tangency point. -/
theorem log_cos_sub_eq_capProfile (x : ℝ) :
    Real.log 2 + Real.log (Real.cos (-Real.arctan x)) - x * (-Real.arctan x) = capProfile x := by
  rw [capProfile_eq_log_cos, Real.cos_neg]
  ring

/-- **The exponential form on the closed arc.**  `2 cos u ≤ e^{Φ(x)} e^{x u}` for `|u| ≤ π/2`. -/
theorem two_mul_cos_le_exp_capProfile (x : ℝ) {u : ℝ} (hu : u ∈ Icc (-(π / 2)) (π / 2)) :
    2 * Real.cos u ≤ Real.exp (capProfile x + x * u) := by
  rcases eq_or_lt_of_le hu.1 with h | h
  · have : Real.cos u = 0 := by rw [← h]; simp
    rw [this]
    simpa using (Real.exp_pos _).le
  rcases eq_or_lt_of_le hu.2 with h' | h'
  · have : Real.cos u = 0 := by rw [h']; simp
    rw [this]
    simpa using (Real.exp_pos _).le
  · have hmem : u ∈ Ioo (-(π / 2)) (π / 2) := ⟨h, h'⟩
    have hcos : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo hmem
    have hlog := log_cos_sub_le_capProfile x hmem
    have h2 : Real.log (2 * Real.cos u) ≤ capProfile x + x * u := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hcos)]
      linarith
    have := Real.exp_le_exp.mpr h2
    rwa [Real.exp_log (by positivity)] at this

/-- **Sharpness.**  `Φ(x)` is the least constant for which the exponential bound holds. -/
theorem capProfile_le_of_forall {x A : ℝ}
    (h : ∀ u ∈ Icc (-(π / 2)) (π / 2), 2 * Real.cos u ≤ Real.exp (A + x * u)) :
    capProfile x ≤ A := by
  have hmem : -Real.arctan x ∈ Icc (-(π / 2)) (π / 2) :=
    Ioo_subset_Icc_self (arctan_mem x)
  have hcos : 0 < Real.cos (-Real.arctan x) :=
    Real.cos_pos_of_mem_Ioo (arctan_mem x)
  have hbound := h _ hmem
  have hlog : Real.log (2 * Real.cos (-Real.arctan x)) ≤ A + x * (-Real.arctan x) := by
    have := Real.log_le_log (by positivity) hbound
    rwa [Real.log_exp] at this
  rw [Real.log_mul (by norm_num) (ne_of_gt hcos)] at hlog
  have heq := log_cos_sub_eq_capProfile x
  linarith

end GaloisForLFunctions.HTGeometry
