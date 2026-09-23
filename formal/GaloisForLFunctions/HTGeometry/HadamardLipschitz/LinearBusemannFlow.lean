/-
# The Euclidean model: linear Busemann functions (Section 5.1.1)

On a real inner-product space the Busemann function attached to the geodesic ray
`γ(t) = x₀ - t u` (with `‖u‖ = 1`) is the linear functional `b(x) = ⟪u, x⟫`, and its flow is
the translation `Φ_t(x) = x - t u`.  `linearBusemannFlow` packages this as a `BusemannFlow`,
which is the non-vacuity witness for the whole `HadamardLipschitz` development: every
hypothesis of `BusemannFlow`, and the `NPCSpace` structure it lives on, is realised.

`linearLayer_eq` identifies the abstract layer with the explicit Euclidean update
`T(x) = x - τ φ'(⟪ξ, x⟫ + β) ξ` of equation (11).
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.BusemannLayer
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Filter Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Busemann flow of the linear Busemann function `⟪u, ·⟫` on an inner-product space:
translation against the unit vector `u`. -/
noncomputable def linearBusemannFlow (u : E) (hu : ‖u‖ = 1) : BusemannFlow E where
  flow t x := x - t • u
  fn x := ⟪u, x⟫
  flow_add s t _ _ x := by
    module
  dist_flow t ht x := by
    rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs, hu, mul_one,
      abs_of_nonneg ht]
  tendsto_fn x y := by
    set v : E := x - y with hv
    set c : ℝ := ⟪u, v⟫ with hc
    have hclim : ⟪u, y⟫ - ⟪u, x⟫ = -c := by
      rw [hc, hv, inner_sub_right]; ring
    rw [hclim]
    -- rewrite the distance as an explicit quotient for `H > 0`
    have hnormsq : ∀ H : ℝ, ‖v - H • u‖ ^ (2 : ℕ) = ‖v‖ ^ (2 : ℕ) - 2 * H * c + H ^ (2 : ℕ) := by
      intro H
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hu, mul_one,
        sq_abs]
      have hvu : ⟪v, u⟫ = c := by rw [hc]; exact real_inner_comm _ _
      rw [hvu]; ring
    have key : ∀ H : ℝ, 0 < H →
        dist (x - H • u) y - H = (‖v‖ ^ (2 : ℕ) / H - 2 * c) / (‖H⁻¹ • v - u‖ + 1) := by
      intro H hH
      have hsm : H⁻¹ • (v - H • u) = H⁻¹ • v - u := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hH), one_smul]
      have hd : ‖H⁻¹ • v - u‖ = ‖v - H • u‖ / H := by
        rw [← hsm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (inv_pos.mpr hH))]
        field_simp
      have hdist : dist (x - H • u) y = ‖v - H • u‖ := by
        rw [dist_eq_norm, hv]; congr 1; abel
      have hNnn : 0 ≤ ‖v - H • u‖ := norm_nonneg _
      have hden : ‖v - H • u‖ / H + 1 ≠ 0 := by positivity
      rw [hdist, hd, eq_div_iff hden]
      have hsq := hnormsq H
      field_simp
      nlinarith [hsq]
    have heq : (fun H : ℝ => dist (x - H • u) y - H)
        =ᶠ[atTop] fun H : ℝ => (‖v‖ ^ (2 : ℕ) / H - 2 * c) / (‖H⁻¹ • v - u‖ + 1) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH using key H hH
    refine Tendsto.congr' heq.symm ?_
    have hnum : Tendsto (fun H : ℝ => ‖v‖ ^ (2 : ℕ) / H - 2 * c) atTop (𝓝 (0 - 2 * c)) :=
      (Tendsto.div_atTop tendsto_const_nhds tendsto_id).sub tendsto_const_nhds
    have hsmul : Tendsto (fun H : ℝ => H⁻¹ • v) atTop (𝓝 (0 : E)) := by
      have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const v
      simpa using this
    have hden : Tendsto (fun H : ℝ => ‖H⁻¹ • v - u‖ + 1) atTop (𝓝 (‖(0 : E) - u‖ + 1)) :=
      ((continuous_norm.tendsto _).comp (hsmul.sub tendsto_const_nhds)).add tendsto_const_nhds
    have hval : ‖(0 : E) - u‖ + 1 = 2 := by rw [zero_sub, norm_neg, hu]; norm_num
    rw [hval] at hden
    have := hnum.div hden (by norm_num)
    have hfin : (0 - 2 * c) / 2 = -c := by ring
    rwa [hfin] at this

@[simp] theorem linearBusemannFlow_fn (u : E) (hu : ‖u‖ = 1) (x : E) :
    (linearBusemannFlow u hu).fn x = ⟪u, x⟫ := rfl

@[simp] theorem linearBusemannFlow_flow (u : E) (hu : ‖u‖ = 1) (t : ℝ) (x : E) :
    (linearBusemannFlow u hu).flow t x = x - t • u := rfl

/-- Equation (11): the abstract Busemann layer on a Euclidean space is the explicit update
`x ↦ x - a(⟪u,x⟫) u`. -/
theorem linearLayer_eq (u : E) (hu : ‖u‖ = 1) (a : ℝ → ℝ) (x : E) :
    layer (linearBusemannFlow u hu) a x = x - a ⟪u, x⟫ • u := rfl

/-- The Euclidean gradient-descent layer `x ↦ x - τ φ'(⟪ξ, x⟫ + β) ξ` for a nonzero direction
`ξ`, obtained from the unit direction `ξ/‖ξ‖` by absorbing `‖ξ‖` into the scale `λ`. -/
theorem linearLayer_of_direction (ξ : E) (hξ : ξ ≠ 0) (dφ : ℝ → ℝ) (τ β : ℝ) (x : E) :
    layer (linearBusemannFlow (‖ξ‖⁻¹ • ξ) (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        field_simp))
      (fun r => τ * ‖ξ‖ * dφ (‖ξ‖ * r + β)) x
      = x - (τ * dφ (⟪ξ, x⟫ + β)) • ξ := by
  have hnorm : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hinner : ⟪‖ξ‖⁻¹ • ξ, x⟫ = ‖ξ‖⁻¹ * ⟪ξ, x⟫ := real_inner_smul_left ξ x _
  rw [linearLayer_eq]
  congr 1
  rw [hinner]
  have hs : ‖ξ‖ * (‖ξ‖⁻¹ * ⟪ξ, x⟫) = ⟪ξ, x⟫ := by field_simp
  rw [hs, smul_smul]
  congr 1
  field_simp

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
