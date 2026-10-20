import GaloisForLFunctions.RHTower.FiniteEulerProductKroneckerWeylLimitLaw
import GaloisForLFunctions.RHTower.PhasedEulerProductsApproximateExponentialsOfHardyFunctions
import GaloisForLFunctions.RHTower.ArgumentVariation

/-!
# Universality of the finite Euler products on discs of the strip

Let `z₀` and `ρ` satisfy `1/2 ≤ Re z₀`, `2ρ − 2Re z₀ < −1`, `3ρ < 1 − Re z₀`, and let `K` be the
closed disc `|z − z₀| ≤ ρ r₁` with `r₁ < 1`.  For every target of the form
`g(z) = exp(L((z − z₀)/ρ))` with `L` in the Hardy space of the disc `|z − z₀| < ρ`, every `ε > 0`
and every `y₀'`, there is a cutoff `y ≥ y₀'` such that the heights `τ` at which the finite Euler
product `E_y(· + iτ)` is within `ε` of `g` on `K` have positive lower density
(`exists_pos_density_eulerTargetReturnSet_exp`): the phases supplied by the exp/log bridge make the
approximating phase set nonempty, and the Kronecker–Weyl visiting law does the rest.

In particular, if `ζ` has no zero on a disc `|z − z₀| < ρ R₂` with `R₂ > 1` lying in `Re z < 1`,
then `ζ` itself is such a target (its analytic logarithm on the larger disc lies in the Hardy
space), and the finite Euler products approximate `ζ` on `K` at a positive lower density of
heights (`exists_pos_density_eulerTargetReturnSet_zeta`).  This is Voronin-type universality for
the finite Euler products, with the target `ζ|_K` that the Bagchi self-return criterion needs.
-/

open Complex Filter Topology Finset Metric MeasureTheory Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## Phases on the primes -/

/-- Unimodular complex phases indexed by `ℕ`, read on the primes as points of the circle. -/
def circleOfUnimodular (ω : ℕ → ℂ) (hω : ∀ n, ‖ω n‖ = 1) (p : Nat.Primes) : Circle :=
  ⟨ω p, mem_sphere_zero_iff_norm.mpr (hω p)⟩

theorem coe_circleOfUnimodular (ω : ℕ → ℂ) (hω : ∀ n, ‖ω n‖ = 1) (p : Nat.Primes) :
    ((circleOfUnimodular ω hω p : Circle) : ℂ) = ω p := rfl

/-- The prime index set `primesLE y`, pushed to `ℕ`, is the set of primes below `y + 1`. -/
theorem map_val_primesLE (y : ℕ) :
    (primesLE y).map ⟨Subtype.val, Subtype.val_injective⟩ = (range (y + 1)).filter Nat.Prime := by
  ext n
  simp only [mem_map, Function.Embedding.coeFn_mk, mem_filter, mem_range]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨by have := (mem_primesLE y p).mp hp; omega, p.2⟩
  · rintro ⟨hn, hp⟩
    exact ⟨⟨n, hp⟩, (mem_primesLE y ⟨n, hp⟩).mpr (by simpa using Nat.lt_succ_iff.mp hn), rfl⟩

/-- The phased Euler product with `ℕ`-indexed phases is the product over the primes below
`y + 1`. -/
theorem eulerPhaseProduct_circleOfUnimodular (y : ℕ) (ω : ℕ → ℂ) (hω : ∀ n, ‖ω n‖ = 1)
    (z : ℂ) :
    eulerPhaseProduct y (circleOfUnimodular ω hω) z
      = ∏ n ∈ (range (y + 1)).filter Nat.Prime, (1 - ω n * (n : ℂ) ^ (-z))⁻¹ := by
  rw [eulerPhaseProduct, ← map_val_primesLE, Finset.prod_map]
  rfl

/-! ## Universality for exponential targets -/

/-- Points of the closed disc `|z − z₀| ≤ ρ r₁` have real part at least `Re z₀ − ρ r₁`. -/
theorem re_ge_of_mem_closedBall_center {z₀ z : ℂ} {ρ r₁ : ℝ}
    (hz : z ∈ closedBall z₀ (ρ * r₁)) : z₀.re - ρ * r₁ ≤ z.re := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h := Complex.abs_re_le_norm (z - z₀)
  rw [Complex.sub_re] at h
  linarith [(abs_le.mp h).1]

/-- **Universality of the finite Euler products for exponential targets.**  For `L` in the Hardy
space of the disc, the heights at which `E_y(· + iτ)` is within `ε` of `exp(L((· − z₀)/ρ))` on the
closed disc `|z − z₀| ≤ ρ r₁` have positive lower density, for a suitable cutoff `y ≥ y₀'`. -/
theorem exists_pos_density_eulerTargetReturnSet_exp (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 ≤ z₀.re) (hρσ₁ : 2 * ρ - 2 * z₀.re < -1) (hρσ₂ : 3 * ρ < 1 - z₀.re)
    (L : HardyDisk) {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) {ε : ℝ} (hε : 0 < ε) (y₀' : ℕ) :
    ∃ y : ℕ, y₀' ≤ y ∧ ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (eulerTargetReturnSet y (fun z => Complex.exp (hardyFun L ((z - z₀) / ρ)))
        (closedBall z₀ (ρ * r₁)) ε ∩ Icc 0 T) := by
  obtain ⟨y, hy, ω, hω, happrox⟩ :=
    exists_unimodular_eulerProduct_approx_exp z₀ hρ hσ hρσ₁ hρσ₂ L hr₁0 hr₁ hε y₀'
  have hρr : ρ * r₁ < z₀.re := by nlinarith
  refine ⟨y, hy, exists_pos_density_eulerTargetReturnSet y (isCompact_closedBall _ _)
    (fun z hz => ?_) ?_ ⟨circleOfUnimodular ω hω, fun z hz => ?_⟩⟩
  · have := re_ge_of_mem_closedBall_center hz
    linarith
  · have hmaps : MapsTo (fun z : ℂ => (z - z₀) / ρ) (closedBall z₀ (ρ * r₁)) (ball 0 1) := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le,
        div_lt_one hρ]
      nlinarith
    have hinner : ContinuousOn (fun z : ℂ => hardyFun L ((z - z₀) / ρ)) (closedBall z₀ (ρ * r₁)) :=
      (differentiableOn_hardyFun L).continuousOn.comp
        ((continuousOn_id.sub continuousOn_const).div_const _) hmaps
    exact Complex.continuous_exp.comp_continuousOn hinner
  · rw [mem_closedBall, dist_eq_norm] at hz
    have hq : ‖(z - z₀) / ρ‖ ≤ r₁ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le, div_le_iff₀ hρ]
      linarith
    have h := happrox _ hq
    have hz' : z₀ + ρ * ((z - z₀) / ρ) = z := by
      field_simp
    rw [hz'] at h
    rw [eulerPhaseProduct_circleOfUnimodular, norm_sub_rev]
    exact h

/-! ## The zeta target on a zero-free disc -/

/-- **Universality of the finite Euler products with target `ζ`.**  If `ζ` has no zero on the disc
`|z − z₀| < ρ R₂`, `R₂ > 1`, which lies in `Re z < 1`, then for every `ε > 0` and `y₀'` there is
`y ≥ y₀'` such that the heights at which `E_y(· + iτ)` is within `ε` of `ζ` on the closed disc
`|z − z₀| ≤ ρ r₁` have positive lower density. -/
theorem exists_pos_density_eulerTargetReturnSet_zeta (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 ≤ z₀.re) (hρσ₁ : 2 * ρ - 2 * z₀.re < -1) (hρσ₂ : 3 * ρ < 1 - z₀.re)
    {R₂ : ℝ} (hR₂ : 1 < R₂) (hR₂1 : z₀.re + ρ * R₂ < 1)
    (hζ : ∀ z ∈ ball z₀ (ρ * R₂), riemannZeta z ≠ 0)
    {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) {ε : ℝ} (hε : 0 < ε) (y₀' : ℕ) :
    ∃ y : ℕ, y₀' ≤ y ∧ ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (eulerTargetReturnSet y riemannZeta (closedBall z₀ (ρ * r₁)) ε ∩ Icc 0 T) := by
  -- the analytic logarithm of `ζ` on the larger disc
  have hρR₂ : 0 < ρ * R₂ := by positivity
  have hne1 : ∀ z ∈ ball z₀ (ρ * R₂), z ≠ 1 := by
    intro z hz h1
    rw [mem_ball, dist_eq_norm] at hz
    have h := Complex.abs_re_le_norm (z - z₀)
    rw [Complex.sub_re, h1, Complex.one_re] at h
    linarith [(abs_le.mp h).2]
  have hζan : AnalyticOnNhd ℂ riemannZeta (ball z₀ (ρ * R₂)) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt) isOpen_ball
  obtain ⟨f, hf, hexpf⟩ := exists_analyticOnNhd_exp_eq_ball hρR₂ hζan hζ
  -- the logarithm in the disc coordinate, on a closed disc of radius `R > 1`
  set R : ℝ := (1 + R₂) / 2 with hR
  have hR1 : 1 < R := by rw [hR]; linarith
  have hRR₂ : R < R₂ := by rw [hR]; linarith
  set F : ℂ → ℂ := fun q => f (z₀ + ρ * q) with hF
  have hmaps : MapsTo (fun q : ℂ => z₀ + ρ * q) (closedBall 0 R) (ball z₀ (ρ * R₂)) := by
    intro q hq
    rw [mem_closedBall, dist_zero_right] at hq
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hρ.le]
    nlinarith
  have hFdiff : DifferentiableOn ℂ F (closedBall 0 R) :=
    hf.differentiableOn.comp
      ((differentiableOn_const _).add ((differentiableOn_const _).mul differentiableOn_id)) hmaps
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn
    (hFdiff.continuousOn.mono sphere_subset_closedBall)
  have hBcirc : ∀ θ : ℝ, ‖F (circleMap 0 R θ)‖ ≤ B := fun θ =>
    hB _ (circleMap_mem_sphere _ (by linarith) θ)
  set L : HardyDisk := hardyDiskOfAnalytic F hR1 hBcirc with hL
  have hLfun : ∀ q : ℂ, ‖q‖ < 1 → hardyFun L q = F q := fun q hq =>
    hardyFun_hardyDiskOfAnalytic hR1 hFdiff hBcirc hq
  -- on the closed disc `|z − z₀| ≤ ρ r₁` the exponential target is `ζ`
  have htarget : ∀ z ∈ closedBall z₀ (ρ * r₁),
      Complex.exp (hardyFun L ((z - z₀) / ρ)) = riemannZeta z := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hq : ‖(z - z₀) / ρ‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le, div_lt_one hρ]
      nlinarith
    have hz' : z₀ + ρ * ((z - z₀) / ρ) = z := by field_simp
    have hzball : z ∈ ball z₀ (ρ * R₂) := by
      rw [mem_ball, dist_eq_norm]
      nlinarith
    rw [hLfun _ hq, hF]
    simp only
    rw [hz']
    exact hexpf z hzball
  -- universality for the exponential target, transported to `ζ`
  obtain ⟨y, hy, c, hc, hev⟩ :=
    exists_pos_density_eulerTargetReturnSet_exp z₀ hρ hσ hρσ₁ hρσ₂ L hr₁0 hr₁ hε y₀'
  refine ⟨y, hy, c, hc, ?_⟩
  have hset : eulerTargetReturnSet y (fun z => Complex.exp (hardyFun L ((z - z₀) / ρ)))
      (closedBall z₀ (ρ * r₁)) ε
      = eulerTargetReturnSet y riemannZeta (closedBall z₀ (ρ * r₁)) ε := by
    ext τ
    simp only [eulerTargetReturnSet, mem_setOf_eq]
    constructor
    · intro h z hz
      rw [← htarget z hz]
      exact h z hz
    · intro h z hz
      rw [htarget z hz]
      exact h z hz
  rw [← hset]
  exact hev

end RHTower
