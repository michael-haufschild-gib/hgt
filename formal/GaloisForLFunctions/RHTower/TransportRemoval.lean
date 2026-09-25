import GaloisForLFunctions.RHTower.CollisionBudget

/-!
# The transport term is removable; the residual obstruction is diffusion

The field quantity of the backward flow obeys `V_τ = V_zz + 2L·V_z - 2V²`, and the standing
diagnosis is that a rigorous collision lemma loses only through the transport term `2L·V_z`. That
term does not have to be estimated. It is removable.

**Removal.** Along a path with velocity `ż = -2L` the transport term cancels against the convective
derivative exactly: `d/dτ V(z(τ),τ) = V_τ + ż·V_z = V_zz - 2V²`. The characteristics are not an
auxiliary device — `-2L(z) = -2Σ_k (z - x_k)⁻¹` is the Calogero velocity field, so **the zeros
themselves travel along the characteristics of the transport term**. In Lagrangian coordinates the
field equation carries no transport at all.

**What is left, and its sign.** After removal the equation is `dV/dτ = V_zz - 2V²`, and the residual
term is the diffusion. Between two consecutive real zeros `V` tends to `+∞` at both ends, so it has
an interior minimum, where `V_zz ≥ 0`: diffusion opposes the damping there rather than assisting it.
The comparison is not marginal. At the midpoint of a gap `δ` the pair's own contribution gives

```text
V = 8/δ²,      V_zz = 192/δ⁴,      2V² = 128/δ⁴,
```

so diffusion exceeds damping by the factor `3/2`, and `dV/dτ > 0` there.

That computation concerns the pair's *own* singular part, which the gap equation `u' = 4Δu - 8`
already treats exactly, so it does not contradict the collision analysis. What it does show is that
the damping bound cannot be applied to `V` at the gap without first separating the pair's singular
part: on the raw field the nonlinearity does not dominate near a close pair. A rigorous collision
lemma must therefore be run on the regular part `Δ`, and the obstruction to freezing `Δ` is the
diffusion of the surrounding field, not its transport.
-/

namespace RHTower

noncomputable section

/-- **Transport removal.** Along a characteristic with velocity `-2L` the convective derivative
cancels the transport term, leaving diffusion against the damping. -/
theorem transport_removed {V Vz Vzz Vt zdot wdot L : ℝ}
    (hV : Vt = Vzz + 2 * L * Vz - 2 * V ^ (2 : ℕ))
    (hz : zdot = -2 * L)
    (hw : wdot = Vt + zdot * Vz) :
    wdot = Vzz - 2 * V ^ (2 : ℕ) := by
  rw [hw, hV, hz]
  ring

/-- The pair's own field at the midpoint of a gap `δ`. -/
def pairMidpointField (δ : ℝ) : ℝ := 8 / δ ^ (2 : ℕ)

/-- The pair's own field curvature at the midpoint of a gap `δ`. -/
def pairMidpointCurvature (δ : ℝ) : ℝ := 192 / δ ^ (4 : ℕ)

/-- The damping term evaluated on the pair's own midpoint field. -/
theorem pairMidpoint_damping (δ : ℝ) :
    2 * pairMidpointField δ ^ (2 : ℕ) = 128 / δ ^ (4 : ℕ) := by
  rw [pairMidpointField, div_pow]
  ring

/-- **Diffusion beats damping at a close pair.** On the pair's own singular part the curvature
exceeds the damping by the factor `3/2`, so the raw field grows along the characteristic. -/
theorem pairMidpoint_diffusion_gt_damping {δ : ℝ} (hδ : 0 < δ) :
    2 * pairMidpointField δ ^ (2 : ℕ) < pairMidpointCurvature δ := by
  rw [pairMidpoint_damping, pairMidpointCurvature]
  have h : (0 : ℝ) < δ ^ (4 : ℕ) := by positivity
  rw [div_lt_div_iff_of_pos_right h]
  norm_num

/-- The exact factor: curvature is `3/2` times the damping. -/
theorem pairMidpoint_ratio {δ : ℝ} (hδ : 0 < δ) :
    pairMidpointCurvature δ = (3 / 2) * (2 * pairMidpointField δ ^ (2 : ℕ)) := by
  rw [pairMidpoint_damping, pairMidpointCurvature]
  have h : δ ^ (4 : ℕ) ≠ 0 := by positivity
  field_simp
  norm_num

end

end RHTower
