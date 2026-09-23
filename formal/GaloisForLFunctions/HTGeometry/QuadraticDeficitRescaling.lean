import Mathlib

/-!
# A positive homogeneous deficit is comparable to the squared distance

A continuous function on a finite-dimensional real normed space that is homogeneous of degree two
and strictly positive off the origin is squeezed between two positive multiples of the squared
norm.  The proof is the classical compactness argument: the unit sphere is compact and the function
attains a positive minimum and a finite maximum there, and homogeneity transports the two bounds to
every vector.

The consequence used by a recurrence-exponent statement is that the sublevel set `{Q ≤ ε}` is
squeezed between the balls of radii `√(ε/C)` and `√(ε/c)`.  A deficit threshold `ε` therefore acts
exactly like a distance threshold `√ε`, so a first-hit exponent measured in the deficit is half the
exponent measured in the distance.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Deficit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] {Q : E → ℝ}

theorem deficit_zero_of_homogeneous (hQhom : ∀ (t : ℝ) (z : E), Q (t • z) = t ^ (2 : ℕ) * Q z) : Q 0 = 0 := by
  have h := hQhom 0 0
  simpa using h

/-- **The two-sided comparison.**  A continuous, degree-two homogeneous, positive-off-zero function
is trapped between two positive multiples of the squared norm. -/
theorem exists_deficit_two_sided_bounds (hQc : Continuous Q)
    (hQhom : ∀ (t : ℝ) (z : E), Q (t • z) = t ^ (2 : ℕ) * Q z)
    (hQpos : ∀ z : E, z ≠ 0 → 0 < Q z) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ z : E, c * ‖z‖ ^ (2 : ℕ) ≤ Q z ∧ Q z ≤ C * ‖z‖ ^ (2 : ℕ) := by
  classical
  have hcompact : IsCompact (sphere (0 : E) 1) := isCompact_sphere 0 1
  have hne : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨u, hu, hmin⟩ := hcompact.exists_isMinOn hne hQc.continuousOn
  obtain ⟨v, hv, hmax⟩ := hcompact.exists_isMaxOn hne hQc.continuousOn
  have hune : u ≠ 0 := by
    intro h
    rw [mem_sphere_iff_norm, sub_zero, h, norm_zero] at hu
    exact absurd hu (by norm_num)
  have hcpos : 0 < Q u := hQpos u hune
  have hcC : Q u ≤ Q v := hmin hv
  refine ⟨Q u, Q v, hcpos, hcC, fun z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · rw [deficit_zero_of_homogeneous hQhom, norm_zero]
    constructor <;> simp
  · have hznorm : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    set w : E := ‖z‖⁻¹ • z with hw
    have hwmem : w ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_iff_norm, sub_zero, hw, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (ne_of_gt hznorm)]
    have hzw : z = ‖z‖ • w := by
      rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt hznorm), one_smul]
    have hQz : Q z = ‖z‖ ^ (2 : ℕ) * Q w := by
      conv_lhs => rw [hzw]
      exact hQhom _ _
    refine ⟨?_, ?_⟩
    · rw [hQz]
      have : Q u ≤ Q w := hmin hwmem
      calc Q u * ‖z‖ ^ (2 : ℕ) = ‖z‖ ^ (2 : ℕ) * Q u := by ring
        _ ≤ ‖z‖ ^ (2 : ℕ) * Q w := by
            exact mul_le_mul_of_nonneg_left this (by positivity)
    · rw [hQz]
      have : Q w ≤ Q v := hmax hwmem
      calc ‖z‖ ^ (2 : ℕ) * Q w ≤ ‖z‖ ^ (2 : ℕ) * Q v := mul_le_mul_of_nonneg_left this (by positivity)
        _ = Q v * ‖z‖ ^ (2 : ℕ) := by ring

/-- A deficit threshold forces a distance threshold: the sublevel set lies in the ball of radius
`√(ε/c)`. -/
theorem norm_le_sqrt_of_deficit_le {c ε : ℝ} (hc : 0 < c) {z : E} (hlow : c * ‖z‖ ^ (2 : ℕ) ≤ Q z)
    (h : Q z ≤ ε) : ‖z‖ ≤ Real.sqrt (ε / c) := by
  have hsq : ‖z‖ ^ (2 : ℕ) ≤ ε / c := by
    rw [le_div_iff₀ hc]
    calc ‖z‖ ^ (2 : ℕ) * c = c * ‖z‖ ^ (2 : ℕ) := by ring
      _ ≤ Q z := hlow
      _ ≤ ε := h
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg z)] at this

/-- Conversely, a distance threshold forces a deficit threshold: the ball of radius `√(ε/C)` lies
in the sublevel set. -/
theorem deficit_le_of_norm_le_sqrt {C ε : ℝ} (hC : 0 < C) (hε : 0 ≤ ε) {z : E}
    (hup : Q z ≤ C * ‖z‖ ^ (2 : ℕ)) (h : ‖z‖ ≤ Real.sqrt (ε / C)) : Q z ≤ ε := by
  have hsq : ‖z‖ ^ (2 : ℕ) ≤ ε / C := by
    have h2 : ‖z‖ ^ (2 : ℕ) ≤ Real.sqrt (ε / C) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (norm_nonneg z) h 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  calc Q z ≤ C * ‖z‖ ^ (2 : ℕ) := hup
    _ ≤ C * (ε / C) := mul_le_mul_of_nonneg_left hsq (le_of_lt hC)
    _ = ε := by field_simp

end Deficit

end GaloisForLFunctions.HTGeometry
