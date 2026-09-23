/-
# Convex `L`-smooth potentials: the Euclidean gradient step is 1-Lipschitz

The Euclidean input of Corollary 4.6 — *for convex `L`-smooth `U`, the map
`z ↦ z - τ ∇U(z)` is nonexpansive for `τ ∈ [0, 2/L]`* — is proved here from scratch, since
mathlib carries no multivariate convex analysis of this kind.  The chain is the classical one:

* `inner_gradient_le` — first-order convexity `f(z) ≥ f(y) + ⟪∇f(y), z - y⟫`, obtained from the
  monotonicity of difference quotients along the segment;
* `descent_lemma` — `f(y) ≤ f(x) + ⟪∇f(x), y-x⟫ + (L/2)‖y-x‖²` for `L`-Lipschitz `∇f`,
  obtained by showing that the error function is antitone on `[0,1]` (this keeps the sharp
  constant `L/2`, which a mean-value argument would lose);
* `baillon_haddad` — cocoercivity `‖∇f(x) - ∇f(y)‖² ≤ L ⟪∇f(x) - ∇f(y), x - y⟫`;
* `gradientStep_nonexpansive` — the conclusion.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Function

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

/-- Derivative of a real quadratic. -/
theorem hasDerivAt_quadratic (c₀ c₁ c₂ t : ℝ) :
    HasDerivAt (fun s : ℝ => c₀ + c₁ * s + c₂ * s ^ (2 : ℕ)) (c₁ + 2 * c₂ * t) t := by
  have h1 : HasDerivAt (fun s : ℝ => c₀ + c₁ * s) c₁ t := by
    simpa using ((hasDerivAt_id t).const_mul c₁).const_add c₀
  have h2 : HasDerivAt (fun s : ℝ => c₂ * s ^ (2 : ℕ)) (c₂ * (2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul c₂
  have h3 : HasDerivAt (fun s : ℝ => c₀ + c₁ * s + c₂ * s ^ (2 : ℕ)) (c₁ + c₂ * (2 * t)) t := h1.add h2
  rw [show c₁ + 2 * c₂ * t = c₁ + c₂ * (2 * t) by ring]
  exact h3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The derivative of `f` along the line `s ↦ y + s v`. -/
theorem hasDerivAt_along {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z)
    (y v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • v)) (⟪g (y + t • v), v⟫) t := by
  have h1 : HasDerivAt (fun s : ℝ => y + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  exact (hg (y + t • v)).hasFDerivAt.comp_hasDerivAt t h1

/-- **First-order convexity.**  A convex differentiable function lies above its tangent
hyperplanes. -/
theorem inner_gradient_le {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z)
    (hf : ConvexOn ℝ Set.univ f) (y z : E) : f y + ⟪g y, z - y⟫ ≤ f z := by
  have hd0 := hasDerivAt_along hg y (z - y) 0
  have hz : y + (0:ℝ) • (z - y) = y := by module
  rw [hz] at hd0
  have h0 : (fun s : ℝ => f (y + s • (z - y))) 0 = f y := by simp
  have h1 : (fun s : ℝ => f (y + s • (z - y))) 1 = f z := by
    simp only [one_smul]
    congr 1
    abel
  have hconv : ∀ t : ℝ, 0 < t → t < 1 →
      f (y + t • (z - y)) ≤ (1 - t) * f y + t * f z := by
    intro t ht0 ht1
    have hpt : (1 - t) • y + t • z = y + t • (z - y) := by module
    have hc := hf.2 (Set.mem_univ y) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - t)
      ht0.le (by ring)
    rw [hpt] at hc
    simpa [smul_eq_mul] using hc
  have hslope : Tendsto (slope (fun s : ℝ => f (y + s • (z - y))) 0) (𝓝[>] (0:ℝ))
      (𝓝 (⟪g y, z - y⟫)) :=
    (hasDerivAt_iff_tendsto_slope.mp hd0).mono_left
      (nhdsWithin_mono _ fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_gt hx))
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),
      slope (fun s : ℝ => f (y + s • (z - y))) 0 t ≤ f z - f y := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have hc := hconv t ht0 ht1
    rw [slope_def_field, hz, sub_zero, div_le_iff₀ ht0]
    nlinarith [hc]
  have := le_of_tendsto hslope hbound
  linarith

/-- **Descent lemma.**  If `∇f` is `L`-Lipschitz then `f` is majorised by its tangent
paraboloid with curvature `L`. -/
theorem descent_lemma {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z) {L : ℝ}
    (hlip : ∀ a b : E, ‖g a - g b‖ ≤ L * ‖a - b‖) (x y : E) :
    f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ (2 : ℕ) := by
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => f (x + s • (y - x))
        - (f x + ⟪g x, y - x⟫ * s + L / 2 * ‖y - x‖ ^ (2 : ℕ) * s ^ (2 : ℕ)))
      (⟪g (x + t • (y - x)), y - x⟫
        - (⟪g x, y - x⟫ + 2 * (L / 2 * ‖y - x‖ ^ (2 : ℕ)) * t)) t := fun t =>
    (hasDerivAt_along hg x (y - x) t).sub
      (hasDerivAt_quadratic (f x) (⟪g x, y - x⟫) (L / 2 * ‖y - x‖ ^ (2 : ℕ)) t)
  have hdiffble : Differentiable ℝ
      (fun s : ℝ => f (x + s • (y - x))
        - (f x + ⟪g x, y - x⟫ * s + L / 2 * ‖y - x‖ ^ (2 : ℕ) * s ^ (2 : ℕ))) :=
    fun t => (hderiv t).differentiableAt
  have hnonpos : ∀ t : ℝ, 0 ≤ t →
      deriv (fun s : ℝ => f (x + s • (y - x))
        - (f x + ⟪g x, y - x⟫ * s + L / 2 * ‖y - x‖ ^ (2 : ℕ) * s ^ (2 : ℕ))) t ≤ 0 := by
    intro t ht
    rw [(hderiv t).deriv]
    have hinner : ⟪g (x + t • (y - x)), y - x⟫ - ⟪g x, y - x⟫
        = ⟪g (x + t • (y - x)) - g x, y - x⟫ := by rw [inner_sub_left]
    have hcs : ⟪g (x + t • (y - x)) - g x, y - x⟫
        ≤ ‖g (x + t • (y - x)) - g x‖ * ‖y - x‖ := real_inner_le_norm _ _
    have hL := hlip (x + t • (y - x)) x
    have hnormsub : ‖x + t • (y - x) - x‖ = t * ‖y - x‖ := by
      rw [show x + t • (y - x) - x = t • (y - x) by abel, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht]
    rw [hnormsub] at hL
    nlinarith [hinner, hcs, hL, norm_nonneg (y - x)]
  have hanti : AntitoneOn
      (fun s : ℝ => f (x + s • (y - x))
        - (f x + ⟪g x, y - x⟫ * s + L / 2 * ‖y - x‖ ^ (2 : ℕ) * s ^ (2 : ℕ))) (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hdiffble.continuous.continuousOn
      hdiffble.differentiableOn ?_
    intro t ht
    rw [interior_Icc] at ht
    exact hnonpos t ht.1.le
  have hle := hanti (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
    (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) zero_le_one
  simp only at hle
  have hz0 : x + (0:ℝ) • (y - x) = x := by module
  have hz1 : x + (1:ℝ) • (y - x) = y := by module
  rw [hz0, hz1] at hle
  simp only [mul_zero, mul_one, one_pow] at hle
  linarith [hle]

/-- **Baillon–Haddad.**  The gradient of a convex `L`-smooth function is `1/L`-cocoercive. -/
theorem baillon_haddad {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z)
    (hf : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ a b : E, ‖g a - g b‖ ≤ L * ‖a - b‖) (x y : E) :
    ‖g x - g y‖ ^ (2 : ℕ) ≤ L * ⟪g x - g y, x - y⟫ := by
  have key : ∀ w u : E,
      f w ≤ f u - ⟪g w, u - w⟫ - 1 / (2 * L) * ‖g u - g w‖ ^ (2 : ℕ) := by
    intro w u
    have hgq : ∀ z : E, HasGradientAt (fun z : E => f z - ⟪g w, z⟫) (g z - g w) z := by
      intro z
      rw [hasGradientAt_iff_hasFDerivAt]
      have h1 : HasFDerivAt (fun z : E => ⟪g w, z⟫) (toDual ℝ E (g w)) z :=
        (toDual ℝ E (g w)).hasFDerivAt
      have h3 : (toDual ℝ E) (g z - g w) = (toDual ℝ E) (g z) - (toDual ℝ E) (g w) :=
        map_sub _ _ _
      rw [h3]
      exact (hg z).hasFDerivAt.sub h1
    have hqlip : ∀ a b : E, ‖g a - g w - (g b - g w)‖ ≤ L * ‖a - b‖ := by
      intro a b
      rw [show g a - g w - (g b - g w) = g a - g b by abel]
      exact hlip a b
    have hpconv : ConvexOn ℝ Set.univ (fun z : E => f z - ⟪g w, z⟫) := by
      refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
      have hf2 := hf.2 (Set.mem_univ a) (Set.mem_univ b) hs ht hst
      simp only [smul_eq_mul]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      simp only [smul_eq_mul] at hf2
      linarith [hf2]
    have hmin : ∀ z : E, f w - ⟪g w, w⟫ ≤ f z - ⟪g w, z⟫ := by
      intro z
      have hgw := inner_gradient_le hgq hpconv w z
      rw [show g w - g w = (0 : E) by abel] at hgw
      simpa using hgw
    have hdesc := descent_lemma hgq hqlip u (u - (1 / L) • (g u - g w))
    rw [show u - (1 / L) • (g u - g w) - u = -((1 / L) • (g u - g w)) by abel] at hdesc
    have hinner : ⟪g u - g w, -((1 / L) • (g u - g w))⟫
        = -(1 / L) * ‖g u - g w‖ ^ (2 : ℕ) := by
      rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      ring
    have hnorm : ‖-((1 / L) • (g u - g w))‖ ^ (2 : ℕ) = (1 / L) ^ (2 : ℕ) * ‖g u - g w‖ ^ (2 : ℕ) := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
    rw [hinner, hnorm] at hdesc
    have hchain := (hmin (u - (1 / L) • (g u - g w))).trans hdesc
    have harith : f u - ⟪g w, u⟫ + -(1 / L) * ‖g u - g w‖ ^ (2 : ℕ)
        + L / 2 * ((1 / L) ^ (2 : ℕ) * ‖g u - g w‖ ^ (2 : ℕ))
        = f u - ⟪g w, u⟫ - 1 / (2 * L) * ‖g u - g w‖ ^ (2 : ℕ) := by
      field_simp
      ring
    rw [harith] at hchain
    rw [show ⟪g w, u - w⟫ = ⟪g w, u⟫ - ⟪g w, w⟫ by rw [inner_sub_right]]
    linarith [hchain]
  have h1 := key x y
  have h2 := key y x
  rw [norm_sub_rev (g y) (g x)] at h1
  rw [show ⟪g x, y - x⟫ = -⟪g x, x - y⟫ by
    rw [show y - x = -(x - y) by abel, inner_neg_right]] at h1
  have hB : ⟪g x - g y, x - y⟫ = ⟪g x, x - y⟫ - ⟪g y, x - y⟫ := by rw [inner_sub_left]
  have hsum : 1 / L * ‖g x - g y‖ ^ (2 : ℕ) ≤ ⟪g x - g y, x - y⟫ := by
    rw [hB]
    have hq : 1 / (2 * L) + 1 / (2 * L) = 1 / L := by field_simp; ring
    nlinarith [h1, h2, hq]
  have hmul := mul_le_mul_of_nonneg_left hsum hL.le
  rw [show L * (1 / L * ‖g x - g y‖ ^ (2 : ℕ)) = ‖g x - g y‖ ^ (2 : ℕ) by field_simp] at hmul
  exact hmul

/-- **The Euclidean input of Corollary 4.6.**  For convex `L`-smooth `f`, the gradient step
`z ↦ z - τ ∇f(z)` is 1-Lipschitz whenever `0 ≤ τ ≤ 2/L`. -/
theorem gradientStep_nonexpansive {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z)
    (hf : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ a b : E, ‖g a - g b‖ ≤ L * ‖a - b‖) {τ : ℝ} (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 2 / L)
    (x y : E) : ‖x - τ • g x - (y - τ • g y)‖ ≤ ‖x - y‖ := by
  have hbh := baillon_haddad hg hf hL hlip x y
  have hdecomp : x - τ • g x - (y - τ • g y) = (x - y) - τ • (g x - g y) := by
    rw [smul_sub]; abel
  have hexp : ‖(x - y) - τ • (g x - g y)‖ ^ (2 : ℕ)
      = ‖x - y‖ ^ (2 : ℕ) - 2 * τ * ⟪x - y, g x - g y⟫ + τ ^ (2 : ℕ) * ‖g x - g y‖ ^ (2 : ℕ) := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hsymm : ⟪x - y, g x - g y⟫ = ⟪g x - g y, x - y⟫ := real_inner_comm _ _
  have hτL : τ * L ≤ 2 := by rw [le_div_iff₀ hL] at hτ; linarith
  have hsq : ‖x - τ • g x - (y - τ • g y)‖ ^ (2 : ℕ) ≤ ‖x - y‖ ^ (2 : ℕ) := by
    rw [hdecomp, hexp, hsymm]
    have hnn : (0:ℝ) ≤ ‖g x - g y‖ ^ (2 : ℕ) := sq_nonneg _
    have e1 : 0 ≤ τ * (L * ⟪g x - g y, x - y⟫ - ‖g x - g y‖ ^ (2 : ℕ)) :=
      mul_nonneg hτ₀ (by linarith)
    have e2 : 0 ≤ τ * ((2 - τ * L) * ‖g x - g y‖ ^ (2 : ℕ)) :=
      mul_nonneg hτ₀ (mul_nonneg (by linarith) hnn)
    have hkey : 0 ≤ L * (2 * τ * ⟪g x - g y, x - y⟫ - τ ^ (2 : ℕ) * ‖g x - g y‖ ^ (2 : ℕ)) := by
      nlinarith [e1, e2]
    have h3 : 0 ≤ 2 * τ * ⟪g x - g y, x - y⟫ - τ ^ (2 : ℕ) * ‖g x - g y‖ ^ (2 : ℕ) := by
      by_contra hcon
      push Not at hcon
      nlinarith [hkey, hL, hcon]
    linarith
  nlinarith [hsq, norm_nonneg (x - τ • g x - (y - τ • g y)), norm_nonneg (x - y)]

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
