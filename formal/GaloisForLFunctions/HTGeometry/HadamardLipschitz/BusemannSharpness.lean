/-
# Sharpness of the step-size bound (Appendix B)

The condition `0 ≤ τ λ² M₂ ≤ 2` of Theorem 4.1 cannot be improved.  On a single Busemann flow
line the squared-ReLU layer `T(x) = Φ_{τ b(x)}(x)` acts by the *exact* affine rescaling
`b ↦ (1-τ) b`, so any two points of the line with nonnegative Busemann values satisfy

```
d(T x, T y) = |1 - τ| · d(x, y) ,
```

`flowline_layer_dist_eq`.  Hence the layer is nonexpansive precisely for `0 ≤ τ ≤ 2`, and
`squaredRelu_layer_not_nonexpansive` exhibits, for every `τ > 2`, a concrete pair of points of
the Euclidean model on which the layer is expansive.

The source's Appendix B carries out this computation inside the Poincaré disc `D²`, where the
diametral geodesic is `ρ = tanh(s/2)` and `b_P(ρP) = -2 artanh ρ`.  The argument above isolates
its mechanism: only the Busemann flow line matters, not the ambient curvature — see
`GaloisForLFunctions.HTGeometry.HadamardLipschitz.PoincareDiameter` for the disc arithmetic.
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.Activation
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.LinearBusemannFlow

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open scoped RealInnerProductSpace

variable {X : Type*} [MetricSpace X] [NPCSpace X]

omit [NPCSpace X] in
/-- **Appendix B, abstract form.**  Along one Busemann flow line, the squared-ReLU layer with
step `τ` scales distances by exactly `|1 - τ|`. -/
theorem flowline_layer_dist_eq (F : BusemannFlow X) {τ β₁ β₂ : ℝ} (hτ : 0 ≤ τ)
    (hβ₂ : 0 ≤ β₂) (hβ : β₂ ≤ β₁) (p : X) (hp : F.fn p = β₁) :
    dist (layer F (fun r => τ * relu r) p)
        (layer F (fun r => τ * relu r) (F.flow (β₁ - β₂) p))
      = |1 - τ| * dist p (F.flow (β₁ - β₂) p) := by
  have hβ₁ : 0 ≤ β₁ := le_trans hβ₂ hβ
  have hd : 0 ≤ β₁ - β₂ := by linarith
  have hfn₂ : F.fn (F.flow (β₁ - β₂) p) = β₂ := by
    rw [F.fn_flow hd p, hp]; ring
  have ha₁ : (fun r => τ * relu r) (F.fn p) = τ * β₁ := by
    simp [hp, relu, max_eq_left hβ₁]
  have ha₂ : (fun r => τ * relu r) (F.fn (F.flow (β₁ - β₂) p)) = τ * β₂ := by
    simp [hfn₂, relu, max_eq_left hβ₂]
  have hcomp : F.flow (τ * β₂) (F.flow (β₁ - β₂) p) = F.flow (τ * β₂ + (β₁ - β₂)) p :=
    F.flow_add (τ * β₂) (β₁ - β₂) (by positivity) hd p
  simp only [layer, ha₁, ha₂, hcomp]
  rw [F.dist_flow_flow_abs (by positivity) (by positivity) p,
    F.dist_flow (β₁ - β₂) hd p]
  rw [show τ * β₂ + (β₁ - β₂) - τ * β₁ = (τ - 1) * (β₂ - β₁) by ring, abs_mul,
    abs_of_nonpos (by linarith : β₂ - β₁ ≤ 0), abs_sub_comm]
  ring

/-- For `τ > 2` the squared-ReLU Busemann layer is expansive: a concrete pair of points of the
Euclidean model (the real line with the Busemann function `b(x) = x`) witnesses it. -/
theorem squaredRelu_layer_not_nonexpansive {τ : ℝ} (hτ : 2 < τ) :
    ∃ x y : ℝ, dist x y < dist
      (layer (linearBusemannFlow (1 : ℝ) (by simp)) (fun r => τ * relu r) x)
      (layer (linearBusemannFlow (1 : ℝ) (by simp)) (fun r => τ * relu r) y) := by
  set F := linearBusemannFlow (1 : ℝ) (by simp : ‖(1:ℝ)‖ = 1) with hF
  have hfn : F.fn (1 : ℝ) = 1 := by simp [hF, linearBusemannFlow]
  have hkey := flowline_layer_dist_eq F (τ := τ) (β₁ := 1) (β₂ := 0) (by linarith)
    le_rfl zero_le_one (1 : ℝ) hfn
  refine ⟨(1 : ℝ), F.flow (1 - 0) (1 : ℝ), ?_⟩
  rw [hkey]
  have hd : dist (1 : ℝ) (F.flow (1 - 0) (1 : ℝ)) = 1 - 0 := F.dist_flow (1 - 0) (by norm_num) 1
  rw [hd]
  have habs : (1:ℝ) < |1 - τ| := by
    rw [abs_of_nonpos (by linarith : (1:ℝ) - τ ≤ 0)]
    linarith
  nlinarith [habs]

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
