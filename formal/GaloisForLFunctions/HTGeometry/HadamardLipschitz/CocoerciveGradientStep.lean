/-
# Convex `L`-smooth potentials: the Euclidean gradient step is 1-Lipschitz

The Euclidean input of Corollary 4.6 — *for convex `L`-smooth `U`, the map
`z ↦ z - τ ∇U(z)` is nonexpansive for `τ ∈ [0, 2/L]`* — is proved here from scratch, since
mathlib carries no multivariate convex-analysis of this kind.  The chain is the classical one:

* `inner_gradient_le` — first-order convexity `f(z) ≥ f(y) + ⟪∇f(y), z - y⟫`, obtained from
  the monotonicity of difference quotients along the segment;
* `descent_lemma` — `f(y) ≤ f(x) + ⟪∇f(x), y-x⟫ + (L/2)‖y-x‖²` for `L`-Lipschitz `∇f`,
  obtained by showing that the error function is antitone on `[0,1]` (this keeps the sharp
  constant `L/2`, which a mean-value argument would lose);
* `baillon_haddad` — cocoercivity `‖∇f(x) - ∇f(y)‖² ≤ L ⟪∇f(x) - ∇f(y), x - y⟫`;
* `gradientStep_nonexpansive` — the conclusion.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Function

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

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
  set v : E := z - y with hv
  set h : ℝ → ℝ := fun s => f (y + s • v) with hh
  have hd : HasDerivAt h (⟪g y, v⟫) 0 := by
    have := hasDerivAt_along hg y v 0
    simpa [hh] using this
  have h0 : h 0 = f y := by simp [hh]
  have h1 : h 1 = f z := by simp [hh, hv]
  have hconv : ∀ t : ℝ, 0 < t → t < 1 → h t ≤ (1 - t) * f y + t * f z := by
    intro t ht0 ht1
    have hpt : (1 - t) • y + t • z = y + t • v := by rw [hv]; module
    have := hf.2 (Set.mem_univ y) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - t)
      ht0.le (by ring)
    rw [hpt] at this
    simpa [hh, smul_eq_mul] using this
  have hslope : Tendsto (slope h 0) (𝓝[>] (0:ℝ)) (𝓝 (⟪g y, v⟫)) :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), slope h 0 t ≤ f z - f y := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have hc := hconv t ht0 ht1
    rw [slope_def_field, h0]
    rw [div_le_iff₀ (by simpa using ht0)]
    nlinarith [hc]
  have := le_of_tendsto hslope hbound
  linarith

/-- **Descent lemma.**  If `∇f` is `L`-Lipschitz then `f` is majorised by its tangent
paraboloid with curvature `L`. -/
theorem descent_lemma {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z) {L : ℝ}
    (hlip : ∀ a b : E, ‖g a - g b‖ ≤ L * ‖a - b‖) (x y : E) :
    f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set v : E := y - x with hv
  set ψ : ℝ → ℝ := fun t => f (x + t • v) - (f x + t * ⟪g x, v⟫ + L / 2 * ‖v‖ ^ 2 * t ^ 2)
    with hψ
  have hderiv : ∀ t : ℝ,
      HasDerivAt ψ (⟪g (x + t • v), v⟫ - (⟪g x, v⟫ + L * ‖v‖ ^ 2 * t)) t := by
    intro t
    have hA := hasDerivAt_along hg x v t
    have hB : HasDerivAt (fun s : ℝ => f x + s * ⟪g x, v⟫ + L / 2 * ‖v‖ ^ 2 * s ^ 2)
        (⟪g x, v⟫ + L * ‖v‖ ^ 2 * t) t := by
      have h1 : HasDerivAt (fun s : ℝ => f x + s * ⟪g x, v⟫) (⟪g x, v⟫) t := by
        simpa using ((hasDerivAt_id t).mul_const (⟪g x, v⟫)).const_add (f x)
      have h2 : HasDerivAt (fun s : ℝ => L / 2 * ‖v‖ ^ 2 * s ^ 2)
          (L * ‖v‖ ^ 2 * t) t := by
        have := (hasDerivAt_pow 2 t).const_mul (L / 2 * ‖v‖ ^ 2)
        simp only [Nat.cast_ofNat, pow_one] at this
        convert this using 1
        ring
      simpa using h1.add h2
    simpa [hψ] using hA.sub hB
  have hdiffble : Differentiable ℝ ψ := fun t => (hderiv t).differentiableAt
  have hnonpos : ∀ t : ℝ, 0 ≤ t → deriv ψ t ≤ 0 := by
    intro t ht
    rw [(hderiv t).deriv]
    have hinner : ⟪g (x + t • v), v⟫ - ⟪g x, v⟫ = ⟪g (x + t • v) - g x, v⟫ := by
      rw [inner_sub_left]
    have hcs : ⟪g (x + t • v) - g x, v⟫ ≤ ‖g (x + t • v) - g x‖ * ‖v‖ := real_inner_le_norm _ _
    have hL := hlip (x + t • v) x
    have hnormsub : ‖x + t • v - x‖ = t * ‖v‖ := by
      rw [show x + t • v - x = t • v by abel, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    rw [hnormsub] at hL
    have hvnn : 0 ≤ ‖v‖ := norm_nonneg v
    nlinarith [hinner, hcs, hL, hvnn]
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hdiffble.continuous.continuousOn
      (hdiffble.differentiableOn) ?_
    intro t ht
    rw [interior_Icc] at ht
    exact hnonpos t ht.1.le
  have hle := hanti (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
    (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) zero_le_one
  have h0 : ψ 0 = 0 := by simp [hψ]
  have h1 : ψ 1 = f y - (f x + ⟪g x, v⟫ + L / 2 * ‖v‖ ^ 2) := by
    simp [hψ, hv]
  rw [h0, h1] at hle
  have : ‖v‖ ^ 2 = ‖y - x‖ ^ 2 := by rw [hv]
  linarith [hle, this.le, this.ge]

/-- **Baillon–Haddad.**  The gradient of a convex `L`-smooth function is `1/L`-cocoercive. -/
theorem baillon_haddad {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z)
    (hf : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ a b : E, ‖g a - g b‖ ≤ L * ‖a - b‖) (x y : E) :
    ‖g x - g y‖ ^ 2 ≤ L * ⟪g x - g y, x - y⟫ := by
  -- for a fixed `w`, the tilted function `f - ⟪g w, ·⟫` is convex, `L`-smooth, and minimised
  -- at `w`
  have key : ∀ w u : E, f w ≤ f u - ⟪g w, u - w⟫ - 1 / (2 * L) * ‖g u - g w‖ ^ 2 := by
    intro w u
    set p : E → ℝ := fun z => f z - ⟪g w, z⟫ with hp
    set q : E → E := fun z => g z - g w with hq
    have hgq : ∀ z, HasGradientAt p (q z) z := by
      intro z
      have h1 : HasGradientAt (fun z : E => ⟪g w, z⟫) (g w) z := by
        have : HasFDerivAt (fun z : E => ⟪g w, z⟫) (toDual ℝ E (g w)) z :=
          (toDual ℝ E (g w)).hasFDerivAt
        exact this
      exact (hg z).sub h1
    have hqlip : ∀ a b : E, ‖q a - q b‖ ≤ L * ‖a - b‖ := by
      intro a b
      have : q a - q b = g a - g b := by rw [hq]; abel
      rw [this]; exact hlip a b
    have hpconv : ConvexOn ℝ Set.univ p := by
      refine hf.sub ?_
      exact ⟨convex_univ, fun a _ b _ s t hs ht hst => by
        simp only [inner_add_right, real_inner_smul_right, smul_eq_mul]
        exact le_of_eq (by ring)⟩
    -- `w` is a global minimiser of `p`
    have hmin : ∀ z : E, p w ≤ p z := by
      intro z
      have := inner_gradient_le hgq hpconv w z
      have hq0 : q w = 0 := by rw [hq]; abel
      rw [hq0] at this
      simpa using this
    -- descent step from `u`
    have hdesc := descent_lemma hgq hqlip u (u - (1 / L) • q u)
    have hsub : u - (1 / L) • q u - u = -((1 / L) • q u) := by abel
    rw [hsub] at hdesc
    have hinner : ⟪q u, -((1 / L) • q u)⟫ = -(1 / L) * ‖q u‖ ^ 2 := by
      rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      ring
    have hnorm : ‖-((1 / L) • q u)‖ ^ 2 = (1 / L) ^ 2 * ‖q u‖ ^ 2 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
      norm_num
    rw [hinner, hnorm] at hdesc
    have hchain := (hmin (u - (1 / L) • q u)).trans hdesc
    have hLne : L ≠ 0 := ne_of_gt hL
    have harith : p u + -(1 / L) * ‖q u‖ ^ 2 + L / 2 * ((1 / L) ^ 2 * ‖q u‖ ^ 2)
        = p u - 1 / (2 * L) * ‖q u‖ ^ 2 := by
      field_simp
      ring
    rw [harith] at hchain
    have hpw : p w = f w - ⟪g w, w⟫ := rfl
    have hpu : p u = f u - ⟪g w, u⟫ := rfl
    rw [hpw, hpu] at hchain
    have hqu : ‖q u‖ = ‖g u - g w‖ := rfl
    rw [hqu] at hchain
    have hsplit : ⟪g w, u - w⟫ = ⟪g w, u⟫ - ⟪g w, w⟫ := by rw [inner_sub_right]
    rw [hsplit]
    linarith
  have h1 := key x y
  have h2 := key y x
  have hs1 : ‖g y - g x‖ = ‖g x - g y‖ := norm_sub_rev _ _
  rw [hs1] at h1
  have hd1 : ⟪g x, y - x⟫ = -⟪g x - g y, x - y⟫ + ⟪g y, y - x⟫ - ⟪g y, y - x⟫ + ⟪g x, y - x⟫ := by
    ring
  have hexp : ⟪g x - g y, x - y⟫ = ⟪g x, x - y⟫ - ⟪g y, x - y⟫ := by rw [inner_sub_left]
  have hxy : ⟪g x, y - x⟫ = -⟪g x, x - y⟫ := by
    rw [show y - x = -(x - y) by abel, inner_neg_right]
  have hyx : ⟪g y, x - y⟫ = -⟪g y, y - x⟫ := by
    rw [show x - y = -(y - x) by abel, inner_neg_right]
  have hLpos : 0 < 2 * L := by linarith
  rw [hxy] at h1
  rw [hyx] at hexp
  have hfinal : 1 / L * ‖g x - g y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫ := by
    rw [hexp]
    have := h1
    have := h2
    have hq : 1 / (2 * L) + 1 / (2 * L) = 1 / L := by field_simp; ring
    nlinarith [h1, h2, hq]
  rw [ge_iff_le, ← sub_nonneg] at hfinal ⊢
  have hLne : L ≠ 0 := ne_of_gt hL
  nlinarith [hfinal, hL]

/-- **The Euclidean input of Corollary 4.6.**  For convex `L`-smooth `f`, the gradient step
`z ↦ z - τ ∇f(z)` is 1-Lipschitz whenever `0 ≤ τ ≤ 2/L`. -/
theorem gradientStep_nonexpansive {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z)
    (hf : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ a b : E, ‖g a - g b‖ ≤ L * ‖a - b‖) {τ : ℝ} (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 2 / L)
    (x y : E) : ‖x - τ • g x - (y - τ • g y)‖ ≤ ‖x - y‖ := by
  have hbh := baillon_haddad hg hf hL hlip x y
  have hdecomp : x - τ • g x - (y - τ • g y) = (x - y) - τ • (g x - g y) := by
    rw [smul_sub]; abel
  have hexp : ‖(x - y) - τ • (g x - g y)‖ ^ 2
      = ‖x - y‖ ^ 2 - 2 * τ * ⟪x - y, g x - g y⟫ + τ ^ 2 * ‖g x - g y‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hsymm : ⟪x - y, g x - g y⟫ = ⟪g x - g y, x - y⟫ := real_inner_comm _ _
  have hτL : τ * L ≤ 2 := by
    rw [le_div_iff₀ hL] at hτ; linarith
  have hsq : ‖x - τ • g x - (y - τ • g y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [hdecomp, hexp, hsymm]
    nlinarith [hbh, sq_nonneg (‖g x - g y‖), hτ₀, hτL, hL, sq_nonneg τ]
  nlinarith [hsq, norm_nonneg (x - τ • g x - (y - τ • g y)), norm_nonneg (x - y)]

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
