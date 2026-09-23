/-
# The Euclidean multi-direction layer (Section 5.1.1)

In `ℝⁿ` the Busemann functions attached to a finite family of directions are the linear forms
`x ↦ ⟪ξᵢ, x⟫`, and summing the corresponding potentials gives the layer

```
T(x) = x - τ Ξᵀ φ'(Ξ x + v) ,
```

the layer of a 1-Lipschitz ResNet.  `resnetLayer_nonexpansive` proves it is 1-Lipschitz for
`0 ≤ τ ≤ 2/(Δ ‖Ξ‖²)`, where `Δ` is a Lipschitz constant for `φ'`.  Unlike the general
Busemann case, several directions are mixed inside one exponential; the proof works because
`φ'` acts coordinatewise and is monotone, which makes `Ξᵀ φ'(Ξ · + v)` cocoercive directly —
no convexity of the potential is invoked.

Per Remark 5.1, no sign condition on `φ'` is needed here.
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.ProductGradientLayer
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Finset
open scoped RealInnerProductSpace

/-- Coordinate expression of the Euclidean inner product. -/
theorem euclidean_inner_eq {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) :
    ⟪x, y⟫ = ∑ i, x i * y i := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => by simp [RCLike.inner_apply, mul_comm]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {k : ℕ}

/-- Componentwise application of the activation derivative. -/
noncomputable def actMap (dφ : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 fun i => dφ (z i)

@[simp] theorem actMap_apply (dφ : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    actMap dφ z i = dφ (z i) := rfl

/-- The Euclidean 1-Lipschitz ResNet layer `x ↦ x - τ Ξᵀ φ'(Ξ x + v)`. -/
noncomputable def resnetLayer (dφ : ℝ → ℝ) (A : E →L[ℝ] EuclideanSpace ℝ (Fin k))
    (v : EuclideanSpace ℝ (Fin k)) (τ : ℝ) (x : E) : E :=
  x - τ • (ContinuousLinearMap.adjoint A) (actMap dφ (A x + v))

/-- Coordinatewise cocoercivity of a monotone `Δ`-Lipschitz scalar map. -/
theorem sq_le_mul_of_monotone_lipschitz {dφ : ℝ → ℝ} (hmono : Monotone dφ) {Δ : ℝ}
    (hlip : ∀ a b : ℝ, |dφ a - dφ b| ≤ Δ * |a - b|) (a b : ℝ) :
    (dφ a - dφ b) ^ (2 : ℕ) ≤ Δ * ((dφ a - dφ b) * (a - b)) := by
  rcases le_total b a with h | h
  · have h1 : dφ b ≤ dφ a := hmono h
    have h2 := hlip a b
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ dφ a - dφ b),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)] at h2
    nlinarith [h2, sub_nonneg.mpr h1, sub_nonneg.mpr h]
  · have h1 : dφ a ≤ dφ b := hmono h
    have h2 := hlip a b
    rw [abs_of_nonpos (by linarith : dφ a - dφ b ≤ 0),
      abs_of_nonpos (by linarith : a - b ≤ 0)] at h2
    nlinarith [h2, sub_nonneg.mpr h1, sub_nonneg.mpr h]

/-- **Section 5.1.1.**  The Euclidean multi-direction gradient-descent layer is 1-Lipschitz
for `0 ≤ τ ≤ 2/(Δ‖Ξ‖²)`. -/
theorem resnetLayer_nonexpansive {dφ : ℝ → ℝ} (hmono : Monotone dφ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hlip : ∀ a b : ℝ, |dφ a - dφ b| ≤ Δ * |a - b|)
    (A : E →L[ℝ] EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin k))
    {τ : ℝ} (hτ₀ : 0 ≤ τ) (hτ : τ * ‖A‖ ^ (2 : ℕ) * Δ ≤ 2) (x y : E) :
    ‖resnetLayer dφ A v τ x - resnetLayer dφ A v τ y‖ ≤ ‖x - y‖ := by
  set P : EuclideanSpace ℝ (Fin k) := actMap dφ (A x + v) - actMap dφ (A y + v) with hP
  set D : E := (ContinuousLinearMap.adjoint A) P with hD
  have hdecomp : resnetLayer dφ A v τ x - resnetLayer dφ A v τ y = (x - y) - τ • D := by
    rw [resnetLayer, resnetLayer, hD, hP, map_sub, smul_sub]
    abel
  have hAdiff : A x + v - (A y + v) = A (x - y) := by rw [map_sub]; abel
  -- cocoercivity of the coordinatewise activation
  have hcoord : ∀ i : Fin k,
      P i ^ (2 : ℕ) ≤ Δ * (P i * ((A x + v) i - (A y + v) i)) := by
    intro i
    have := sq_le_mul_of_monotone_lipschitz hmono hlip ((A x + v) i) ((A y + v) i)
    simpa [hP] using this
  have hsum : ‖P‖ ^ (2 : ℕ) ≤ Δ * ⟪P, A x + v - (A y + v)⟫ := by
    rw [euclidean_norm_sq, euclidean_inner_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hc := hcoord i
    have : (A x + v - (A y + v)) i = (A x + v) i - (A y + v) i := by simp
    rw [this]
    linarith [hc]
  have hinner : ⟪D, x - y⟫ = ⟪P, A (x - y)⟫ := ContinuousLinearMap.adjoint_inner_left A (x - y) P
  have hcoerc : ‖P‖ ^ (2 : ℕ) ≤ Δ * ⟪D, x - y⟫ := by
    rw [hinner, ← hAdiff]; exact hsum
  have hnormD : ‖D‖ ≤ ‖A‖ * ‖P‖ := by
    rw [hD]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    have : ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ := ContinuousLinearMap.adjoint.norm_map A
    rw [this]
  have hexp : ‖(x - y) - τ • D‖ ^ (2 : ℕ)
      = ‖x - y‖ ^ (2 : ℕ) - 2 * τ * ⟪x - y, D⟫ + τ ^ (2 : ℕ) * ‖D‖ ^ (2 : ℕ) := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hsymm : ⟪x - y, D⟫ = ⟪D, x - y⟫ := real_inner_comm _ _
  have hPnn : (0:ℝ) ≤ ‖P‖ ^ (2 : ℕ) := sq_nonneg _
  have hAnn : (0:ℝ) ≤ ‖A‖ := norm_nonneg _
  have hDsq : ‖D‖ ^ (2 : ℕ) ≤ ‖A‖ ^ (2 : ℕ) * ‖P‖ ^ (2 : ℕ) := by
    nlinarith [hnormD, norm_nonneg D, mul_nonneg hAnn (norm_nonneg P)]
  have hsq : ‖resnetLayer dφ A v τ x - resnetLayer dφ A v τ y‖ ^ (2 : ℕ) ≤ ‖x - y‖ ^ (2 : ℕ) := by
    rw [hdecomp, hexp, hsymm]
    have hkey : τ ^ (2 : ℕ) * ‖D‖ ^ (2 : ℕ) ≤ 2 * τ * ⟪D, x - y⟫ := by
      have e1 : τ ^ (2 : ℕ) * ‖D‖ ^ (2 : ℕ) ≤ τ ^ (2 : ℕ) * (‖A‖ ^ (2 : ℕ) * ‖P‖ ^ (2 : ℕ)) := by nlinarith [hDsq, sq_nonneg τ]
      have e2 : Δ * (τ ^ (2 : ℕ) * (‖A‖ ^ (2 : ℕ) * ‖P‖ ^ (2 : ℕ))) ≤ Δ * (2 * τ * ⟪D, x - y⟫) := by
        have h1 : τ * (τ * ‖A‖ ^ (2 : ℕ) * Δ) * ‖P‖ ^ (2 : ℕ) ≤ τ * 2 * ‖P‖ ^ (2 : ℕ) := by
          have hnn : 0 ≤ τ * ‖P‖ ^ (2 : ℕ) := mul_nonneg hτ₀ hPnn
          nlinarith [hτ, hnn]
        nlinarith [hcoerc, hτ₀, hPnn, h1]
      nlinarith [e1, e2, hΔ]
    linarith
  nlinarith [hsq, norm_nonneg (resnetLayer dφ A v τ x - resnetLayer dφ A v τ y),
    norm_nonneg (x - y)]

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
