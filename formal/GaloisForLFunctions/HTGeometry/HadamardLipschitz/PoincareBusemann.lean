/-
# Busemann functions on the Poincaré ball (Section 5.1.2)

For a boundary point `ξ` (‖ξ‖ = 1) the Busemann function of the Poincaré ball is

```
b(x) = log ( ‖ξ - x‖² / (1 - ‖x‖²) ) ,
```

with Euclidean gradient

```
∇b(x) = 2/(1-‖x‖²) · x + 2/‖x-ξ‖² · (x - ξ)
```

and, since the conformal factor is `δ_x = 2/(1-‖x‖²)`, Riemannian gradient
`grad b = δ_x^{-2} ∇b`, i.e.

```
grad b(x) = (1-‖x‖²)/2 · x + (1-‖x‖²)²/(2‖x-ξ‖²) · (x - ξ) .
```

Both formulas are verified here (`hasGradientAt_poincareBusemann`,
`poincareBusemannGrad_eq`), for the ball of an arbitrary real Hilbert space.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Poincaré-ball Busemann function attached to the boundary point `ξ`. -/
noncomputable def poincareBusemann (ξ x : E) : ℝ := Real.log (‖ξ - x‖ ^ 2 / (1 - ‖x‖ ^ 2))

/-- The Euclidean gradient of `poincareBusemann`. -/
noncomputable def poincareBusemannEuclideanGrad (ξ x : E) : E :=
  (2 / (1 - ‖x‖ ^ 2)) • x + (2 / ‖x - ξ‖ ^ 2) • (x - ξ)

/-- The Riemannian gradient of `poincareBusemann` for the Poincaré metric. -/
noncomputable def poincareBusemannGrad (ξ x : E) : E :=
  ((1 - ‖x‖ ^ 2) / 2) • x + ((1 - ‖x‖ ^ 2) ^ 2 / (2 * ‖x - ξ‖ ^ 2)) • (x - ξ)

theorem hasGradientAt_poincareBusemann {ξ x : E} (hξ : ‖ξ‖ = 1) (hx : ‖x‖ < 1) :
    HasGradientAt (poincareBusemann ξ) (poincareBusemannEuclideanGrad ξ x) x := by
  have hxnn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
  have hden : (0:ℝ) < 1 - ‖x‖ ^ 2 := by nlinarith
  have hne : ξ - x ≠ 0 := by
    intro h
    have hxx : ‖ξ‖ < 1 := by rw [(sub_eq_zero.mp h : ξ = x)]; exact hx
    rw [hξ] at hxx; exact absurd hxx (lt_irrefl 1)
  have hnum : (0:ℝ) < ‖ξ - x‖ ^ 2 := by positivity
  -- derivatives of the two pieces
  have hf : HasFDerivAt (fun z : E => ξ - z) (-(ContinuousLinearMap.id ℝ E)) x := by
    simpa using (hasFDerivAt_id x).const_sub ξ
  have hA : HasFDerivAt (fun z : E => ‖ξ - z‖ ^ 2)
      (2 • (innerSL ℝ (ξ - x)).comp (-(ContinuousLinearMap.id ℝ E))) x := hf.norm_sq
  have hB : HasFDerivAt (fun z : E => 1 - ‖z‖ ^ 2) (-(2 • innerSL ℝ x)) x :=
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_sub 1
  have hlogA := hA.log (by simpa using ne_of_gt hnum)
  have hlogB := hB.log (by simpa using ne_of_gt hden)
  have hsub := hlogA.sub hlogB
  -- the two expressions of `b` agree near `x`
  have heq : poincareBusemann ξ
      =ᶠ[𝓝 x] fun z : E => Real.log (‖ξ - z‖ ^ 2) - Real.log (1 - ‖z‖ ^ 2) := by
    filter_upwards [Metric.ball_mem_nhds x (by linarith : (0:ℝ) < 1 - ‖x‖)] with z hz
    have hz1 : ‖z‖ < 1 := by
      have := dist_eq_norm z x ▸ (Metric.mem_ball.mp hz)
      calc ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by simpa using norm_add_le (z - x) x
        _ < (1 - ‖x‖) + ‖x‖ := by linarith
        _ = 1 := by ring
    have hzn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
    have hzden : (0:ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith
    have hzne : ξ - z ≠ 0 := by
      intro h
      have hzz : ‖ξ‖ < 1 := by rw [(sub_eq_zero.mp h : ξ = z)]; exact hz1
      rw [hξ] at hzz; exact absurd hzz (lt_irrefl 1)
    have hznum : (0:ℝ) < ‖ξ - z‖ ^ 2 := by positivity
    rw [poincareBusemann, Real.log_div (ne_of_gt hznum) (ne_of_gt hzden)]
  have hfinal := hsub.congr_of_eventuallyEq heq
  rw [hasGradientAt_iff_hasFDerivAt]
  have hD : (toDual ℝ E) (poincareBusemannEuclideanGrad ξ x)
      = (‖ξ - x‖ ^ 2)⁻¹ • (2 • (innerSL ℝ (ξ - x)).comp (-(ContinuousLinearMap.id ℝ E)))
        - (1 - ‖x‖ ^ 2)⁻¹ • (-(2 • innerSL ℝ x)) := by
    ext y
    have hsymnorm : ‖ξ - x‖ = ‖x - ξ‖ := norm_sub_rev ξ x
    have e1 : (innerSL ℝ (ξ - x)) (-y) = ⟪x - ξ, y⟫ := by
      rw [innerSL_apply_apply, inner_neg_right, show ξ - x = -(x - ξ) by abel, inner_neg_left]
      ring
    simp only [toDual_apply_apply, poincareBusemannEuclideanGrad, inner_add_left,
      real_inner_smul_left, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
      neg_apply, ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul,
      Nat.cast_ofNat, e1, innerSL_apply_apply, hsymnorm]
    field_simp
    ring
  rw [hD]
  exact hfinal

omit [CompleteSpace E] in
/-- The Riemannian gradient is the Euclidean one rescaled by the inverse squared conformal
factor `δ_x^{-2} = (1-‖x‖²)²/4`. -/
theorem poincareBusemannGrad_eq (ξ x : E) (hx : ‖x‖ < 1) (hxi : x ≠ ξ) :
    poincareBusemannGrad ξ x = ((1 - ‖x‖ ^ 2) ^ 2 / 4) • poincareBusemannEuclideanGrad ξ x := by
  have hxnn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
  have hden : (0:ℝ) < 1 - ‖x‖ ^ 2 := by nlinarith
  have hne : x - ξ ≠ 0 := sub_ne_zero.mpr hxi
  have hnum : (0:ℝ) < ‖x - ξ‖ ^ 2 := by positivity
  rw [poincareBusemannGrad, poincareBusemannEuclideanGrad, smul_add, smul_smul, smul_smul]
  congr 1
  · congr 1; field_simp; ring
  · congr 1; field_simp; ring

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
