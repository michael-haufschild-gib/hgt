import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall
import GaloisForLFunctions.RHTower.OrbitSensitiveContinuationCharge

/-!
# Boundary-pole energy law for the Möbius--Laplace Gamma--Hankel wall

A nonzero meromorphic principal part sampled on vertical lines at horizontal distance
`r_n = (n+1)⁻¹` from its pole has exact squared `L²` energy

`pi * ‖c‖² / r_n = pi * ‖c‖² * (n+1)`.

Thus its line energy tends to infinity and admits no uniform bound.  This is the local analytic
obstruction needed at a zero on the boundary of a Mellin half-plane: Mellin--Plancherel can give a
uniform family of line norms only when the continued quotient has no boundary pole.

The module proves the exact pole-energy core.  It does not assume a zeta zero, identify the full
Möbius Mellin transform with its local principal part, or claim RH.
-/

open Complex MeasureTheory Set Filter

noncomputable section

namespace RHTower

/-- Principal part of a boundary pole sampled on the line at distance `(n+1)⁻¹`. -/
def boundaryPoleApproachProfile (gamma : ℝ) (c : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  fixedLinePoleProfile (((n + 1 : ℕ) : ℝ)⁻¹) 0 gamma c t

/-- Exact inverse-distance energy of the boundary-pole principal part. -/
theorem integral_norm_sq_boundaryPoleApproachProfile
    (gamma : ℝ) (c : ℂ) (n : ℕ) :
    (∫ t : ℝ, ‖boundaryPoleApproachProfile gamma c n t‖ ^ 2) =
      Real.pi * ‖c‖ ^ 2 * (n + 1) := by
  simp_rw [boundaryPoleApproachProfile]
  rw [integral_norm_sq_fixedLinePoleProfile
    (by positivity : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)⁻¹))]
  simp only [sub_zero, div_eq_mul_inv, inv_inv]
  push_cast
  ring

/-- Every nonzero boundary principal part has line energy tending to infinity. -/
theorem tendsto_integral_norm_sq_boundaryPoleApproachProfile
    (gamma : ℝ) {c : ℂ} (hc : c ≠ 0) :
    Tendsto (fun n : ℕ =>
      ∫ t : ℝ, ‖boundaryPoleApproachProfile gamma c n t‖ ^ 2) atTop atTop := by
  simp_rw [integral_norm_sq_boundaryPoleApproachProfile]
  have hscale : 0 < Real.pi * ‖c‖ ^ 2 :=
    mul_pos Real.pi_pos (sq_pos_of_pos (norm_pos_iff.mpr hc))
  have hcast : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact hcast.const_mul_atTop hscale

/-- Any proposed finite line-energy ceiling is crossed by a sufficiently close pole line. -/
theorem exists_integral_norm_sq_boundaryPoleApproachProfile_gt
    (gamma : ℝ) {c : ℂ} (hc : c ≠ 0) (C : ℝ) :
    ∃ n : ℕ, C < ∫ t : ℝ, ‖boundaryPoleApproachProfile gamma c n t‖ ^ 2 := by
  exact Filter.Eventually.exists
    ((tendsto_integral_norm_sq_boundaryPoleApproachProfile gamma hc).eventually_gt_atTop C)

/-- Uniform `L²` control on lines approaching a nonzero boundary pole is impossible. -/
theorem not_exists_uniform_boundaryPoleApproachEnergy_bound
    (gamma : ℝ) {c : ℂ} (hc : c ≠ 0) :
    ¬ ∃ C : ℝ, ∀ n : ℕ,
      (∫ t : ℝ, ‖boundaryPoleApproachProfile gamma c n t‖ ^ 2) ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ :=
    exists_integral_norm_sq_boundaryPoleApproachProfile_gt gamma hc C
  exact (not_lt_of_ge (hC n)) hn

end RHTower
