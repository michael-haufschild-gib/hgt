import GaloisForLFunctions.HTGeometry.GappedEigenlineStability
import GaloisForLFunctions.RHTower.StaticChoiTraceDistanceLaw

/-!
# The gapped eigenline floor is uniform in time

The pure-state trace distance is the density distance rescaled, so it inherits the triangle
inequality; it is blind to phases and preserved by isometries.  A unitary that fixes a line
therefore moves every state by at most twice its distance to that line, whatever the unitary — in
particular whatever the time.

Combined with the gapped-eigenline bound, a state within `√(2δ/Δ)` of a perturbed eigenline never
leaves a projective ball of radius `2√(2δ/Δ)` around itself.  This is the mechanism a Duhamel
estimate cannot see: the eigenline moves once, and is then preserved forever.
-/

namespace HTGeometry

open RHTower

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- **Triangle inequality for the pure-state trace distance**, inherited from the density
distance. -/
theorem pureStateTraceDistance_triangle (a b c : EuclideanSpace ℂ ι)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    pureStateTraceDistance a c ≤ pureStateTraceDistance a b + pureStateTraceDistance b c := by
  rw [pureStateTraceDistance_eq_invSqrtTwo_mul_densityDist a c ha hc,
    pureStateTraceDistance_eq_invSqrtTwo_mul_densityDist a b ha hb,
    pureStateTraceDistance_eq_invSqrtTwo_mul_densityDist b c hb hc, ← mul_add]
  exact mul_le_mul_of_nonneg_left (dist_triangle _ _ _) (by positivity)

/-- The pure-state trace distance is symmetric. -/
theorem pureStateTraceDistance_comm (a b : EuclideanSpace ℂ ι) :
    pureStateTraceDistance a b = pureStateTraceDistance b a := by
  rw [pureStateTraceDistance, pureStateTraceDistance,
    show (inner ℂ b a : ℂ) = starRingEnd ℂ (inner ℂ a b) from (inner_conj_symm b a).symm,
    RCLike.norm_conj]

/-- The pure-state trace distance is blind to phases. -/
theorem pureStateTraceDistance_smul_left (c : ℂ) (hc : ‖c‖ = 1)
    (a b : EuclideanSpace ℂ ι) :
    pureStateTraceDistance (c • a) b = pureStateTraceDistance a b := by
  rw [pureStateTraceDistance, pureStateTraceDistance, inner_smul_left, norm_mul,
    RCLike.norm_conj, hc, one_mul]

/-- A linear isometry preserves the pure-state trace distance. -/
theorem pureStateTraceDistance_isometry
    (U : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι) (a b : EuclideanSpace ℂ ι) :
    pureStateTraceDistance (U a) (U b) = pureStateTraceDistance a b := by
  rw [pureStateTraceDistance, pureStateTraceDistance, U.inner_map_map]

/-- **A unitary fixing a line moves every state by at most twice its distance to that line.**  The
bound does not see the unitary at all beyond the fixed line, so it is uniform over any family of
them. -/
theorem pureStateTraceDistance_apply_le_two_mul
    (U : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (Φ ψ : EuclideanSpace ℂ ι) (hΦ : ‖Φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (c : ℂ) (hc : ‖c‖ = 1) (hUψ : U ψ = c • ψ) :
    pureStateTraceDistance (U Φ) Φ ≤ 2 * pureStateTraceDistance ψ Φ := by
  have hUΦ : ‖U Φ‖ = 1 := by rw [U.norm_map, hΦ]
  have hUψn : ‖U ψ‖ = 1 := by rw [U.norm_map, hψ]
  calc pureStateTraceDistance (U Φ) Φ
      ≤ pureStateTraceDistance (U Φ) (U ψ) + pureStateTraceDistance (U ψ) Φ :=
        pureStateTraceDistance_triangle _ _ _ hUΦ hUψn hΦ
    _ = pureStateTraceDistance Φ ψ + pureStateTraceDistance ψ Φ := by
        rw [pureStateTraceDistance_isometry, hUψ, pureStateTraceDistance_smul_left c hc]
    _ = 2 * pureStateTraceDistance ψ Φ := by
        rw [pureStateTraceDistance_comm Φ ψ]
        ring

/-- The projective deficit bound reads as a trace-distance bound. -/
theorem pureStateTraceDistance_le_sqrt_of_deficit
    (Φ ψ : EuclideanSpace ℂ ι) (r : ℝ)
    (h : 1 - ‖(inner ℂ Φ ψ : ℂ)‖ ^ 2 ≤ r) :
    pureStateTraceDistance ψ Φ ≤ Real.sqrt r := by
  rw [pureStateTraceDistance]
  refine Real.sqrt_le_sqrt ?_
  rw [show (inner ℂ ψ Φ : ℂ) = starRingEnd ℂ (inner ℂ Φ ψ) from (inner_conj_symm ψ Φ).symm,
    RCLike.norm_conj]
  exact h

/-- **The time-uniform gapped floor.**  A gapped eigenvector perturbed by `δ` stays inside a
projective ball of radius `2√(2δ/Δ)` under every unitary that fixes the perturbed eigenline. -/
theorem pureStateTraceDistance_apply_le_of_gap
    (U : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (Φ ψ : EuclideanSpace ℂ ι) (hΦ : ‖Φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (c : ℂ) (hc : ‖c‖ = 1) (hUψ : U ψ = c • ψ)
    (Δ δ : ℝ) (hdef : 1 - ‖(inner ℂ Φ ψ : ℂ)‖ ^ 2 ≤ 2 * δ / Δ) :
    pureStateTraceDistance (U Φ) Φ ≤ 2 * Real.sqrt (2 * δ / Δ) := by
  refine (pureStateTraceDistance_apply_le_two_mul U Φ ψ hΦ hψ c hc hUψ).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pureStateTraceDistance_le_sqrt_of_deficit Φ ψ _ hdef) (by norm_num)

end

end HTGeometry
