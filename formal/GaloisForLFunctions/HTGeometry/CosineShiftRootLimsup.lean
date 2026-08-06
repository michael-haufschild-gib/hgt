import GaloisForLFunctions.HTGeometry.ZetaShiftDecomposition

/-!
# The oscillating factor of the shifted functional equation

The factor `cos(π(1-s₀+k)/2)` advances by a quarter turn at each step, so it has
period four in `k`.  It may vanish on a whole residue class, but not on all of
them: the first two values are `cos θ` and `-sin θ`, and `sin² + cos² = 1`
forbids both from vanishing.

Periodicity therefore gives boundedness and a frequent positive lower bound, and
the root-limsup law for periodic factors shows that this factor contributes
nothing to the growth of the shifted zeta coefficients.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

section CosineShift

variable (s₀ : ℂ)

/-- The oscillating factor of the shifted functional equation. -/
noncomputable def cosShift (s₀ : ℂ) (k : ℕ) : ℝ :=
  ‖Complex.cos ((Real.pi : ℂ) * (1 - s₀ + (k : ℂ)) / 2)‖

theorem cosShift_nonneg (k : ℕ) : 0 ≤ cosShift s₀ k := norm_nonneg _

/-- **The oscillating factor has period four.** -/
theorem cosShift_periodic (k : ℕ) : cosShift s₀ (k + 4) = cosShift s₀ k := by
  have harg : (Real.pi : ℂ) * (1 - s₀ + ((k + 4 : ℕ) : ℂ)) / 2
      = (Real.pi : ℂ) * (1 - s₀ + (k : ℂ)) / 2 + 2 * (Real.pi : ℂ) := by
    push_cast
    ring
  rw [cosShift, cosShift, harg, Complex.cos_add_two_pi]

/-- **The oscillating factor is positive at index zero or one.**  Both would force
`sin` and `cos` to vanish together. -/
theorem exists_cosShift_pos : 0 < cosShift s₀ 0 ∨ 0 < cosShift s₀ 1 := by
  by_contra hcon
  rw [not_or, not_lt, not_lt] at hcon
  obtain ⟨h0, h1⟩ := hcon
  have hz0 : Complex.cos ((Real.pi : ℂ) * (1 - s₀ + ((0 : ℕ) : ℂ)) / 2) = 0 := by
    have := le_antisymm h0 (cosShift_nonneg s₀ 0)
    rw [cosShift, norm_eq_zero] at this
    exact this
  have hz1 : Complex.cos ((Real.pi : ℂ) * (1 - s₀ + ((1 : ℕ) : ℂ)) / 2) = 0 := by
    have := le_antisymm h1 (cosShift_nonneg s₀ 1)
    rw [cosShift, norm_eq_zero] at this
    exact this
  set θ : ℂ := (Real.pi : ℂ) * (1 - s₀) / 2 with hθ
  have hc : Complex.cos θ = 0 := by
    rw [hθ]
    have : (Real.pi : ℂ) * (1 - s₀ + ((0 : ℕ) : ℂ)) / 2
        = (Real.pi : ℂ) * (1 - s₀) / 2 := by push_cast; ring
    rwa [this] at hz0
  have hs : Complex.sin θ = 0 := by
    have harg : (Real.pi : ℂ) * (1 - s₀ + ((1 : ℕ) : ℂ)) / 2
        = θ + (Real.pi : ℂ) / 2 := by
      rw [hθ]
      push_cast
      ring
    rw [harg, Complex.cos_add_pi_div_two, neg_eq_zero] at hz1
    exact hz1
  have hpyth := Complex.sin_sq_add_cos_sq θ
  rw [hc, hs] at hpyth
  norm_num at hpyth

/-- **The oscillating factor contributes nothing to the root growth.** -/
theorem limsup_cosShift_rpow_inv_eq_one :
    limsup (fun k : ℕ => (cosShift s₀ k) ^ (1 / (k : ℝ))) atTop = 1 := by
  rcases exists_cosShift_pos s₀ with h | h
  · exact limsup_rpow_inv_eq_one_of_periodic (by norm_num)
      (cosShift_periodic s₀) (cosShift_nonneg s₀) h
  · exact limsup_rpow_inv_eq_one_of_periodic (by norm_num)
      (cosShift_periodic s₀) (cosShift_nonneg s₀) h

end CosineShift

end GaloisForLFunctions.HTGeometry
