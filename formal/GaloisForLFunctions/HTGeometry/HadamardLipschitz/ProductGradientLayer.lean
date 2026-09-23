/-
# Corollary 4.6: coupled product layers from a convex `L`-smooth coupling

On the product `Mᵐ` of a Hadamard space, let `U : ℝᵐ → ℝ` be convex, `L`-smooth and
componentwise nondecreasing, and let `V(X) = U(b(x¹), …, b(xᵐ))`.  The explicit Riemannian
gradient step `T(X) = exp_X(-τ grad V(X))` is 1-Lipschitz for every `τ ∈ [0, 2/L]`.

This is Theorem 4.4 (`productLayer_sum_sq_le`) fed with the Euclidean cocoercivity input
(`gradientStep_nonexpansive`).
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.BusemannLayer
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.CocoerciveGradientStep

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Finset
open scoped RealInnerProductSpace

/-- Coordinate expression of the Euclidean squared norm. -/
theorem euclidean_norm_sq {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) : ‖v‖ ^ (2 : ℕ) = ∑ i, v i ^ (2 : ℕ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]

variable {X : Type*} [MetricSpace X] [NPCSpace X]

/-- **Corollary 4.6.**  For a convex `L`-smooth coupling `U` with nonnegative gradient, the
coupled Busemann layer of `V = U ∘ B` is 1-Lipschitz on `Mᵐ` for `τ ∈ [0, 2/L]`. -/
theorem productLayer_gradient_sum_sq_le (F : BusemannFlow X) {m : ℕ}
    {U : EuclideanSpace ℝ (Fin m) → ℝ} {G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hG : ∀ z, HasGradientAt U (G z) z) (hU : ConvexOn ℝ Set.univ U) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ a b : EuclideanSpace ℝ (Fin m), ‖G a - G b‖ ≤ L * ‖a - b‖)
    (hposG : ∀ z k, 0 ≤ G z k) {τ : ℝ} (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 2 / L) (x y : Fin m → X) :
    ∑ k, dist
        (productLayerFun F (fun z k => τ * G (WithLp.toLp 2 z) k) x k)
        (productLayerFun F (fun z k => τ * G (WithLp.toLp 2 z) k) y k) ^ (2 : ℕ)
      ≤ ∑ k, dist (x k) (y k) ^ (2 : ℕ) := by
  refine productLayer_sum_sq_le F _ (fun z k => mul_nonneg hτ₀ (hposG _ _)) ?_ x y
  intro z w
  set Z : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 z with hZ
  set W : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 w with hW
  have hstep := gradientStep_nonexpansive hG hU hL hlip hτ₀ hτ Z W
  have hcoordL : ∀ k : Fin m,
      (Z - τ • G Z - (W - τ • G W)) k = (z k - τ * G Z k) - (w k - τ * G W k) := by
    intro k; simp [hZ, hW]
  have hcoordR : ∀ k : Fin m, (Z - W) k = z k - w k := by intro k; simp [hZ, hW]
  have hL2 : ‖Z - τ • G Z - (W - τ • G W)‖ ^ (2 : ℕ)
      = ∑ k, ((z k - τ * G Z k) - (w k - τ * G W k)) ^ (2 : ℕ) := by
    rw [euclidean_norm_sq]
    exact Finset.sum_congr rfl fun k _ => by rw [hcoordL k]
  have hR2 : ‖Z - W‖ ^ (2 : ℕ) = ∑ k, (z k - w k) ^ (2 : ℕ) := by
    rw [euclidean_norm_sq]
    exact Finset.sum_congr rfl fun k _ => by rw [hcoordR k]
  have hsq : ‖Z - τ • G Z - (W - τ • G W)‖ ^ (2 : ℕ) ≤ ‖Z - W‖ ^ (2 : ℕ) := by
    nlinarith [hstep, norm_nonneg (Z - τ • G Z - (W - τ • G W)), norm_nonneg (Z - W)]
  rw [hL2, hR2] at hsq
  exact hsq

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
