/-
# Busemann gradient-descent layers are 1-Lipschitz

The layer of a manifold-valued 1-Lipschitz network is
```
T(x) = exp_x(-τ grad V(x)),   V(x) = φ(λ b(x) + β),
```
which, because `grad b` generates the Busemann flow, is the *variable-time* flow
`T(x) = Φ_{a(b(x))}(x)` with `a(r) = τ λ φ'(λ r + β)`.

`layer_nonexpansive` is the main theorem: `T` is 1-Lipschitz as soon as `a ≥ 0` and
`r ↦ r - a(r)` is 1-Lipschitz.  In the differentiable setting the latter is exactly the
step-size condition `0 ≤ τ λ² φ'' ≤ 2`, recorded as `activation_layer_nonexpansive`.

`productLayer_dist_le` is the product-manifold generalisation: on `Mᵐ` with the ℓ²-product
metric, the coupled layer `T(X)_k = Φ_{a_k(b(x¹),…,b(xᵐ))}(x_k)` is 1-Lipschitz whenever
`a ≥ 0` componentwise and `z ↦ z - a(z)` is 1-Lipschitz for the Euclidean norm on `ℝᵐ`.

The proofs use only `BusemannFlow.dist_flow_flow_sq_le`; no regularity of `a` is needed,
which strengthens the source statements (there `a` is assumed Lipschitz and `φ ∈ C^{1,1}`).
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.BusemannFlow
import Mathlib.Analysis.Normed.Lp.PiLp

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Filter Topology Finset

variable {X : Type*} [MetricSpace X] [NPCSpace X]

/-- The Busemann gradient-descent layer `T(x) = Φ_{a(b(x))}(x)`. -/
def layer (F : BusemannFlow X) (a : ℝ → ℝ) (x : X) : X := F.flow (a (F.fn x)) x

/-- The admissibility condition on the time reparametrisation: nonnegative flow times, and
`r ↦ r - a r` nonexpansive.  In the smooth case this is `0 ≤ a' ≤ 2`. -/
structure ScalarAdmissible (a : ℝ → ℝ) : Prop where
  /-- Flow times are nonnegative. -/
  nonneg : ∀ r, 0 ≤ a r
  /-- `r ↦ r - a r` is 1-Lipschitz. -/
  residual : ∀ u v : ℝ, |(u - a u) - (v - a v)| ≤ |u - v|

/-- The smooth criterion `0 ≤ a' ≤ 2` implies admissibility. -/
theorem scalarAdmissible_of_monotone {a : ℝ → ℝ} (h0 : ∀ r, 0 ≤ a r) (h1 : Monotone a)
    (h2 : Monotone fun r => 2 * r - a r) : ScalarAdmissible a := by
  refine ⟨h0, fun u v => ?_⟩
  rcases le_total u v with hle | hle
  · have hA : a u ≤ a v := h1 hle
    have hB : 2 * u - a u ≤ 2 * v - a v := h2 hle
    rw [abs_of_nonpos (by linarith : u - v ≤ 0)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hA : a v ≤ a u := h1 hle
    have hB : 2 * v - a v ≤ 2 * u - a u := h2 hle
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u - v)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Theorem 4.1.**  A Busemann gradient-descent layer with admissible time
reparametrisation is 1-Lipschitz. -/
theorem layer_nonexpansive (F : BusemannFlow X) {a : ℝ → ℝ} (ha : ScalarAdmissible a) (x y : X) :
    dist (layer F a x) (layer F a y) ≤ dist x y := by
  have hmain := F.dist_flow_flow_sq_le (ha.nonneg (F.fn x)) (ha.nonneg (F.fn y)) x y
  have hres := ha.residual (F.fn x) (F.fn y)
  have hsq : ((F.fn x - a (F.fn x)) - (F.fn y - a (F.fn y))) ^ 2 ≤ (F.fn x - F.fn y) ^ 2 := by
    nlinarith [sq_abs ((F.fn x - a (F.fn x)) - (F.fn y - a (F.fn y))), sq_abs (F.fn x - F.fn y),
      abs_nonneg ((F.fn x - a (F.fn x)) - (F.fn y - a (F.fn y))), abs_nonneg (F.fn x - F.fn y),
      hres]
  have hgoal : dist (layer F a x) (layer F a y) ^ 2 ≤ dist x y ^ 2 := by
    simp only [layer]; nlinarith [hmain, hsq]
  nlinarith [hgoal, dist_nonneg (x := layer F a x) (y := layer F a y),
    dist_nonneg (x := x) (y := y)]

/-- **Theorem 4.1, activation form.**  For a potential `V(x) = φ(λ b(x) + β)` with `φ` convex,
nondecreasing, and `φ'` globally `M₂`-Lipschitz, the explicit Riemannian gradient step is
1-Lipschitz whenever `0 ≤ τ λ² M₂ ≤ 2`. -/
theorem activation_layer_nonexpansive (F : BusemannFlow X) (dφ : ℝ → ℝ) (τ lam β M₂ : ℝ)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (hnonneg : ∀ s, 0 ≤ dφ s) (hmono : Monotone dφ)
    (hlip : ∀ u v : ℝ, |dφ u - dφ v| ≤ M₂ * |u - v|) (hstep : τ * lam ^ 2 * M₂ ≤ 2) (x y : X) :
    dist (layer F (fun r => τ * lam * dφ (lam * r + β)) x)
         (layer F (fun r => τ * lam * dφ (lam * r + β)) y) ≤ dist x y := by
  refine layer_nonexpansive F (scalarAdmissible_of_monotone ?_ ?_ ?_) x y
  · intro r; exact mul_nonneg (mul_nonneg hτ hlam) (hnonneg _)
  · intro u v huv
    have : lam * u + β ≤ lam * v + β := by nlinarith
    have := hmono this
    nlinarith [mul_nonneg hτ hlam]
  · intro u v huv
    have hbound : dφ (lam * v + β) - dφ (lam * u + β) ≤ M₂ * (lam * (v - u)) := by
      have h1 : dφ (lam * v + β) - dφ (lam * u + β)
          ≤ |dφ (lam * v + β) - dφ (lam * u + β)| := le_abs_self _
      have h2 := hlip (lam * v + β) (lam * u + β)
      have h3 : |lam * v + β - (lam * u + β)| = lam * (v - u) := by
        rw [show lam * v + β - (lam * u + β) = lam * (v - u) by ring,
          abs_of_nonneg (by nlinarith)]
      rw [h3] at h2
      linarith
    have hkey : τ * lam * (dφ (lam * v + β) - dφ (lam * u + β)) ≤ τ * lam ^ 2 * M₂ * (v - u) := by
      have hcoef : 0 ≤ τ * lam := mul_nonneg hτ hlam
      nlinarith [hbound, hcoef]
    simp only
    nlinarith [hkey, hstep, sub_nonneg.mpr huv]

/-- Compositions of layers stay 1-Lipschitz (Remark 4.3). -/
theorem layer_comp_nonexpansive (F : BusemannFlow X) {a b : ℝ → ℝ}
    (ha : ScalarAdmissible a) (hb : ScalarAdmissible b) (x y : X) :
    dist (layer F b (layer F a x)) (layer F b (layer F a y)) ≤ dist x y :=
  (layer_nonexpansive F hb _ _).trans (layer_nonexpansive F ha x y)

section Product

variable {m : ℕ}

/-- The coupled product layer of `Theorem 4.4`: on `Mᵐ`, each component flows for a time
depending on the whole vector of Busemann values. -/
def productLayerFun (F : BusemannFlow X) (a : (Fin m → ℝ) → (Fin m → ℝ))
    (x : Fin m → X) (k : Fin m) : X :=
  F.flow (a (fun j => F.fn (x j)) k) (x k)

/-- **Theorem 4.4, sum form.**  The coupled product layer does not increase the sum of squared
componentwise distances, provided each flow time is nonnegative and `z ↦ z - a z` is
nonexpansive for the Euclidean norm on `ℝᵐ`. -/
theorem productLayer_sum_sq_le (F : BusemannFlow X) (a : (Fin m → ℝ) → (Fin m → ℝ))
    (ha : ∀ z k, 0 ≤ a z k)
    (hR : ∀ z w : Fin m → ℝ,
      ∑ k, ((z k - a z k) - (w k - a w k)) ^ 2 ≤ ∑ k, (z k - w k) ^ 2)
    (x y : Fin m → X) :
    ∑ k, dist (productLayerFun F a x k) (productLayerFun F a y k) ^ 2
      ≤ ∑ k, dist (x k) (y k) ^ 2 := by
  set bx : Fin m → ℝ := fun j => F.fn (x j) with hbx
  set by' : Fin m → ℝ := fun j => F.fn (y j) with hby
  have hcomp : ∀ k : Fin m,
      dist (productLayerFun F a x k) (productLayerFun F a y k) ^ 2
        ≤ dist (x k) (y k) ^ 2
          - 2 * (a bx k - a by' k) * (bx k - by' k) + (a bx k - a by' k) ^ 2 := by
    intro k
    exact F.dist_flow_flow_sq_le (ha _ _) (ha _ _) (x k) (y k)
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hcomp k)
  have hsplit : ∑ k, (dist (x k) (y k) ^ 2
        - 2 * (a bx k - a by' k) * (bx k - by' k) + (a bx k - a by' k) ^ 2)
      = (∑ k, dist (x k) (y k) ^ 2)
        + ∑ k, ((a bx k - a by' k) ^ 2 - 2 * (a bx k - a by' k) * (bx k - by' k)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hneg : ∑ k, ((a bx k - a by' k) ^ 2 - 2 * (a bx k - a by' k) * (bx k - by' k)) ≤ 0 := by
    have h1 := hR bx by'
    have h2 : ∑ k, ((bx k - a bx k) - (by' k - a by' k)) ^ 2
        = ∑ k, ((bx k - by' k) ^ 2
            + ((a bx k - a by' k) ^ 2 - 2 * (a bx k - a by' k) * (bx k - by' k))) :=
      Finset.sum_congr rfl (fun k _ => by ring)
    rw [h2, Finset.sum_add_distrib] at h1
    linarith
  rw [hsplit] at hsum
  linarith

omit [NPCSpace X] in
/-- The `ℓ²`-product distance on `Mᵐ` in squared form. -/
theorem piLp_dist_sq (x y : PiLp 2 (fun _ : Fin m => X)) :
    dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2 := by
  have hd := PiLp.dist_eq_sum (α := fun _ : Fin m => X) (p := 2) (by norm_num) x y
  have hpow : ∀ i : Fin m, dist (x i) (y i) ^ ((2 : ENNReal).toReal) = dist (x i) (y i) ^ 2 := by
    intro i
    rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsum : ∑ i, dist (x i) (y i) ^ ((2 : ENNReal).toReal) = ∑ i, dist (x i) (y i) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => hpow i)
  rw [hd, hsum]
  have hnn : 0 ≤ ∑ i, dist (x i) (y i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  rw [show (1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt hnn

/-- **Theorem 4.4.**  On the product `Mᵐ` with the `ℓ²`-product metric the coupled Busemann
layer is 1-Lipschitz. -/
theorem productLayer_dist_le (F : BusemannFlow X) (a : (Fin m → ℝ) → (Fin m → ℝ))
    (ha : ∀ z k, 0 ≤ a z k)
    (hR : ∀ z w : Fin m → ℝ,
      ∑ k, ((z k - a z k) - (w k - a w k)) ^ 2 ≤ ∑ k, (z k - w k) ^ 2)
    (X₀ Y₀ : PiLp 2 (fun _ : Fin m => X)) :
    dist (WithLp.toLp 2 (productLayerFun F a (fun k => X₀ k)))
        (WithLp.toLp 2 (productLayerFun F a (fun k => Y₀ k))) ≤ dist X₀ Y₀ := by
  have hkey := productLayer_sum_sq_le F a ha hR (fun k => X₀ k) (fun k => Y₀ k)
  have h1 : dist (WithLp.toLp 2 (productLayerFun F a (fun k => X₀ k)))
      (WithLp.toLp 2 (productLayerFun F a (fun k => Y₀ k))) ^ 2
      = ∑ k, dist (productLayerFun F a (fun k => X₀ k) k)
          (productLayerFun F a (fun k => Y₀ k) k) ^ 2 := piLp_dist_sq _ _
  have h2 : dist X₀ Y₀ ^ 2 = ∑ k, dist (X₀ k) (Y₀ k) ^ 2 := piLp_dist_sq _ _
  nlinarith [hkey, h1, h2, dist_nonneg (x := WithLp.toLp 2 (productLayerFun F a
    (fun k => X₀ k))) (y := WithLp.toLp 2 (productLayerFun F a (fun k => Y₀ k))),
    dist_nonneg (x := X₀) (y := Y₀)]

/-- **Remark 4.5.**  For `m = 1` the product criterion reduces to the scalar one. -/
theorem scalarAdmissible_iff_product (a : ℝ → ℝ) :
    (∀ u v : ℝ, |(u - a u) - (v - a v)| ≤ |u - v|)
      ↔ ∀ u v : ℝ, ((u - a u) - (v - a v)) ^ 2 ≤ (u - v) ^ 2 := by
  constructor
  · intro h u v
    nlinarith [h u v, sq_abs ((u - a u) - (v - a v)), sq_abs (u - v),
      abs_nonneg ((u - a u) - (v - a v)), abs_nonneg (u - v)]
  · intro h u v
    nlinarith [h u v, sq_abs ((u - a u) - (v - a v)), sq_abs (u - v),
      abs_nonneg ((u - a u) - (v - a v)), abs_nonneg (u - v)]

end Product

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
