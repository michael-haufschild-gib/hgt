import GaloisForLFunctions.RHTower.PhasedEulerProductsApproximateExponentialsOnDiscUnions
import GaloisForLFunctions.RHTower.UniformEulerTargetDensityOnZeroFreeDiscs
import GaloisForLFunctions.RHTower.ZetaDiscUniformCarlsonTail

/-!
# Euler-target heights for `ζ` on a finite union of discs, uniformly in the cutoff

Fix finitely many discs `|s − z i| < ρ i` with a common floor `σ₁ ≤ Re (z i) − ρ i`, `σ₁ > 1/2`,
and `Re (z i) + ρ i ≤ b < 1`, and let `K = ⋃_i closedBall (z i) (ρ i r₁)`, `r₁ < 1`.  Suppose `ζ`
has no zero on a disc `ball c₀ R₀` containing all the discs `closedBall (z i) (ρ i R₂)`,
`R₂ > 1`, which lie in `Re s < 1`.

* **Universality with target `ζ` on `K`** (`exists_pos_density_eulerTargetReturnSet_zeta_union`):
  for every `ε > 0` and `y₀'` there is `y ≥ y₀'` such that the heights at which `E_y(· + iτ)` is
  within `ε` of `ζ` on all of `K` have positive lower density.  The target is `exp L` with
  `L = ℓ + (−log(1 − s) + iπ)`, where `ℓ` is an analytic logarithm of `(s − 1)ζ(s)` on
  `ball c₀ R₀` and `−log(1 − s)` is analytic on a disc of the half plane `Re s < 1` containing the
  discs; both tuples lie in `primeSpan`, so the joint phased Euler product approximation applies,
  and the Kronecker–Weyl law for the compact `K` gives the density.

* **Uniformity in the cutoff** (`exists_uniform_pos_density_eulerTargetReturnSet_zeta_union`):
  the density constant can be taken independent of `y` for all large `y`.  The single-disc
  argument runs with the random linear prime sum taken in the direct sum `DiscTuple ι`: Chebyshev
  controls its norm, hence every component at once, and the per-disc stability lemma then holds
  on every disc.
-/

open Complex Filter Topology Finset Metric MeasureTheory Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

variable {ι : Type*} [Fintype ι]

/-! ## Points of the disc union -/

theorem re_le_of_mem_closedBall_center {z₀ z : ℂ} {r : ℝ} (hz : z ∈ closedBall z₀ r) :
    z.re ≤ z₀.re + r := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h := Complex.abs_re_le_norm (z - z₀)
  rw [Complex.sub_re] at h
  linarith [(abs_le.mp h).2]

omit [Fintype ι] in
/-- Points of the disc union have real part above the common floor. -/
theorem pos_re_of_mem_iUnion_closedBall (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 < ρ i) {σ₁ : ℝ}
    (hσ₁ : 1 / 2 < σ₁) (hσ₁le : ∀ i, σ₁ ≤ (z i).re - ρ i) {r₁ : ℝ} (hr₁ : r₁ < 1) :
    ∀ s ∈ ⋃ i, closedBall (z i) (ρ i * r₁), 0 < s.re := by
  intro s hs
  obtain ⟨i, hsi⟩ := mem_iUnion.mp hs
  have h1 := re_ge_of_mem_closedBall_center hsi
  have h2 : ρ i * r₁ ≤ ρ i * 1 := mul_le_mul_of_nonneg_left hr₁.le (hρ i).le
  linarith [hσ₁le i]

omit [Fintype ι] in
/-- Points of the disc union are different from `1`. -/
theorem ne_one_of_mem_iUnion_closedBall (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 < ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) {r₁ : ℝ} (hr₁ : r₁ < 1) :
    ∀ s ∈ ⋃ i, closedBall (z i) (ρ i * r₁), s ≠ 1 := by
  intro s hs h1
  obtain ⟨i, hsi⟩ := mem_iUnion.mp hs
  have h2 := re_le_of_mem_closedBall_center hsi
  have h3 : ρ i * r₁ ≤ ρ i * 1 := mul_le_mul_of_nonneg_left hr₁.le (hρ i).le
  rw [h1, Complex.one_re] at h2
  linarith [hb i]

omit [Fintype ι] in
/-- `ζ` is continuous on the disc union. -/
theorem continuousOn_riemannZeta_iUnion_closedBall (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 < ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) {r₁ : ℝ} (hr₁ : r₁ < 1) :
    ContinuousOn riemannZeta (⋃ i, closedBall (z i) (ρ i * r₁)) := fun s hs =>
  (differentiableAt_riemannZeta
    (ne_one_of_mem_iUnion_closedBall z hρ hb hb1 hr₁ s hs)).continuousAt.continuousWithinAt

/-! ## The logarithm of `ζ` as a tuple of the closed span -/

/-- **A tuple of `primeSpan` whose exponential is `ζ` on the discs.**  If `ζ` has no zero on
`ball c₀ R₀ ⊇ closedBall (z i) (ρ i R)` and the discs lie in `Re s < 1`, there is
`L ∈ primeSpan` with `exp (L_i(q)) = ζ (z i + ρ i q)` for `|q| < 1`. -/
theorem exists_mem_primeSpan_exp_eq_zeta (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) {R : ℝ} (hR : 1 < R)
    (hR1 : ∀ i, (z i).re + ρ i * R < 1) {c₀ : ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hsub : ∀ i, ‖z i - c₀‖ + ρ i * R < R₀) (hζ : ∀ s ∈ ball c₀ R₀, riemannZeta s ≠ 0) :
    ∃ L ∈ primeSpan z hρ, ∀ i, ∀ q : ℂ, ‖q‖ < 1 →
      Complex.exp (hardyFun (L i) q) = riemannZeta (z i + ρ i * q) := by
  -- the analytic logarithm of `(s − 1) ζ(s)` on the zero-free disc
  have hg : AnalyticOnNhd ℂ zetaPoleFilled (ball c₀ R₀) :=
    differentiable_zetaPoleFilled.differentiableOn.analyticOnNhd isOpen_ball
  have hg0 : ∀ s ∈ ball c₀ R₀, zetaPoleFilled s ≠ 0 := by
    intro s hs
    by_cases h1 : s = 1
    · rw [h1]
      show Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1 1 ≠ 0
      rw [Function.update_self]
      exact one_ne_zero
    · rw [zetaPoleFilled_of_ne h1]
      exact mul_ne_zero (sub_ne_zero.mpr h1) (hζ s hs)
  obtain ⟨ℓ, hℓ, hexpℓ⟩ := exists_analyticOnNhd_exp_eq_ball hR₀ hg hg0
  obtain ⟨t₁, ht₁, ht₁fun⟩ :=
    exists_mem_primeSpan_of_differentiableOn_ball z hρ hb hb1 hR hsub hℓ.differentiableOn
  -- the branch `−log(1 − s) + iπ` on a disc of the half plane `Re s < 1`
  obtain ⟨c₂, R₂, hsub₂, hre₂⟩ := exists_ball_re_lt_of_forall_lt z (r := fun i => ρ i * R)
    (β := 1) hR1
  have hF₂ : DifferentiableOn ℂ (fun s : ℂ => -Complex.log (1 - s) + Real.pi * I)
      (ball c₂ R₂) := by
    refine (((differentiableOn_const _).sub differentiableOn_id).clog fun s hs => ?_).neg.add
      (differentiableOn_const _)
    rw [Complex.mem_slitPlane_iff]
    left
    have := hre₂ s (ball_subset_closedBall hs)
    show 0 < (1 - s).re
    rw [Complex.sub_re, Complex.one_re]
    linarith
  obtain ⟨t₂, ht₂, ht₂fun⟩ :=
    exists_mem_primeSpan_of_differentiableOn_ball z hρ hb hb1 hR hsub₂ hF₂
  refine ⟨t₁ + t₂, Submodule.add_mem _ ht₁ ht₂, fun i q hq => ?_⟩
  have hqR : q ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hy₀ : z i + ρ i * q ∈ ball c₀ R₀ := mapsTo_disc_coordinate z hρ hsub i hqR
  have hy₂ : z i + ρ i * q ∈ ball c₂ R₂ := mapsTo_disc_coordinate z hρ hsub₂ i hqR
  have hre1 : (z i + ρ i * q).re < 1 := hre₂ _ (ball_subset_closedBall hy₂)
  have hne1 : z i + ρ i * q ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hre1
    exact lt_irrefl _ hre1
  have hne1' : 1 - (z i + ρ i * q) ≠ 0 := by
    intro h
    exact hne1 (by linear_combination -h)
  rw [PiLp.add_apply, hardyFun_add _ _ hq, ht₁fun i q hq, ht₂fun i q hq, Complex.exp_add,
    hexpℓ _ hy₀, Complex.exp_add, Complex.exp_neg, Complex.exp_log hne1', Complex.exp_pi_mul_I,
    zetaPoleFilled_of_ne hne1]
  field_simp
  ring

/-! ## Universality with target `ζ` on the disc union -/

/-- **Universality of the finite Euler products with target `ζ` on a finite union of discs.**
With the common floor `σ₁` and ceiling `b`, a zero-free disc `ball c₀ R₀` containing all
`closedBall (z i) (ρ i R₂)`, `R₂ > 1`, lying in `Re s < 1`: for every `ε > 0` and `y₀'` there is
`y ≥ y₀'` such that the heights at which `E_y(· + iτ)` is within `ε` of `ζ` on
`⋃_i closedBall (z i) (ρ i r₁)` have positive lower density. -/
theorem exists_pos_density_eulerTargetReturnSet_zeta_union (z : ι → ℂ) {ρ : ι → ℝ}
    (hρ : ∀ i, 0 < ρ i) {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁) (hσ₁le : ∀ i, σ₁ ≤ (z i).re - ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1)
    {R₂ : ℝ} (hR₂ : 1 < R₂) (hρR₂ : ∀ i, ρ i * R₂ < (z i).re)
    (hR₂1 : ∀ i, (z i).re + ρ i * R₂ < 1) {c₀ : ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hsub : ∀ i, ‖z i - c₀‖ + ρ i * R₂ < R₀) (hζ : ∀ s ∈ ball c₀ R₀, riemannZeta s ≠ 0)
    {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) {ε : ℝ} (hε : 0 < ε) (y₀' : ℕ) :
    ∃ y : ℕ, y₀' ≤ y ∧ ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (eulerTargetReturnSet y riemannZeta (⋃ i, closedBall (z i) (ρ i * r₁)) ε
        ∩ Icc 0 T) := by
  have hρ' : ∀ i, 0 ≤ ρ i := fun i => (hρ i).le
  -- the Hardy-extension radius
  set R : ℝ := (1 + R₂) / 2 with hRdef
  have hR : 1 < R := by rw [hRdef]; linarith
  have hRR₂ : R < R₂ := by rw [hRdef]; linarith
  have hsubR : ∀ i, ‖z i - c₀‖ + ρ i * R < R₀ := fun i => by
    have := hsub i
    have h2 : ρ i * R ≤ ρ i * R₂ := mul_le_mul_of_nonneg_left hRR₂.le (hρ' i)
    linarith
  have hR1 : ∀ i, (z i).re + ρ i * R < 1 := fun i => by
    have := hR₂1 i
    have h2 : ρ i * R ≤ ρ i * R₂ := mul_le_mul_of_nonneg_left hRR₂.le (hρ' i)
    linarith
  have hρR : ∀ i, ρ i * R < (z i).re := fun i => by
    have := hρR₂ i
    have h2 : ρ i * R ≤ ρ i * R₂ := mul_le_mul_of_nonneg_left hRR₂.le (hρ' i)
    linarith
  -- the logarithm of `ζ` as a tuple of the closed span
  obtain ⟨L, hL, hexpL⟩ := exists_mem_primeSpan_exp_eq_zeta z hρ' hb hb1 hR hR1 hR₀ hsubR hζ
  -- the joint phased Euler product approximation
  obtain ⟨y, hy, ω, hω, happrox⟩ := exists_unimodular_eulerProduct_approx_exp_tuple z hρ hσ₁ hσ₁le
    hb hb1 hR hρR hL hr₁0 hr₁ hε y₀'
  refine ⟨y, hy, exists_pos_density_eulerTargetReturnSet y
    (isCompact_iUnion fun i => isCompact_closedBall _ _)
    (pos_re_of_mem_iUnion_closedBall z hρ hσ₁ hσ₁le hr₁)
    (continuousOn_riemannZeta_iUnion_closedBall z hρ hb hb1 hr₁)
    ⟨circleOfUnimodular ω hω, fun s hs => ?_⟩⟩
  obtain ⟨i, hsi⟩ := mem_iUnion.mp hs
  rw [mem_closedBall, dist_eq_norm] at hsi
  have hρi : (ρ i : ℂ) ≠ 0 := by exact_mod_cast (hρ i).ne'
  have hq : ‖(s - z i) / ρ i‖ ≤ r₁ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hρ' i), div_le_iff₀ (hρ i)]
    linarith
  have hs' : z i + ρ i * ((s - z i) / ρ i) = s := by
    rw [mul_div_cancel₀ _ hρi]
    ring
  have h := happrox i _ hq
  rw [hs', hexpL i _ (lt_of_le_of_lt hq hr₁), hs'] at h
  rw [eulerPhaseProduct_circleOfUnimodular, norm_sub_rev]
  exact h

/-! ## The random prime sum in the direct sum -/

/-- The tuple of prime vectors `(u_p^{(i)})_i` indexed by the primes. -/
def primeVectorTuple (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (p : Nat.Primes) :
    DiscTuple ι :=
  WithLp.toLp 2 fun i => primeVectorOf (z i) (hρ i) p

theorem torusPrimePhaseSum_primeVectorTuple_apply (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    (B : Finset Nat.Primes) (x : UnitAddTorus Nat.Primes) (i : ι) :
    (torusPrimePhaseSum B (primeVectorTuple z hρ) x) i
      = torusPrimePhaseSum B (primeVectorOf (z i) (hρ i)) x := by
  unfold torusPrimePhaseSum
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rfl

/-- The remainder constant is antitone in the real-part floor. -/
theorem eulerRemainderConstant_anti {σ₁ σ₂ : ℝ} (h0 : 0 < σ₁) (h : σ₁ ≤ σ₂) :
    (1 - (2 : ℝ) ^ (-σ₂))⁻¹ / 2 ≤ (1 - (2 : ℝ) ^ (-σ₁))⁻¹ / 2 := by
  have h1 : (2 : ℝ) ^ (-σ₂) ≤ (2 : ℝ) ^ (-σ₁) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 := two_rpow_neg_lt_one h0
  gcongr

/-- The squared norm of a prime vector tuple is at most `card ι · p^{−2σ₁}`. -/
theorem norm_primeVectorTuple_sq_le (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) {σ₁ : ℝ}
    (hσ₁le : ∀ i, σ₁ ≤ (z i).re - ρ i) (p : Nat.Primes) :
    ‖primeVectorTuple z hρ p‖ ^ 2 ≤ Fintype.card ι * ((p : ℕ) : ℝ) ^ (-(2 * σ₁)) := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_le
  calc ∑ i, ‖(primeVectorTuple z hρ p) i‖ ^ 2
      ≤ ∑ _i : ι, ((p : ℕ) : ℝ) ^ (-(2 * σ₁)) := by
        refine sum_le_sum fun i _ => ?_
        refine (norm_primeVectorOf_sq_le (z i) (hρ i) p).trans ?_
        exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith [hσ₁le i])
    _ = Fintype.card ι * ((p : ℕ) : ℝ) ^ (-(2 * σ₁)) := by
        rw [sum_const, card_univ, nsmul_eq_mul]

/-! ## Uniform lower density of the Euler-target heights on the disc union -/

/-- **Positive lower density of the Euler-target heights on a finite union of discs, uniformly in
the cutoff.**  Under the hypotheses of `exists_pos_density_eulerTargetReturnSet_zeta_union`,
there are `c > 0` and `y₁` such that for every `y ≥ y₁` the heights at which `E_y(· + iτ)` is
within `ε` of `ζ` on `⋃_i closedBall (z i) (ρ i r₁)` have lower density at least `c`. -/
theorem exists_uniform_pos_density_eulerTargetReturnSet_zeta_union (z : ι → ℂ) {ρ : ι → ℝ}
    (hρ : ∀ i, 0 < ρ i) {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁) (hσ₁le : ∀ i, σ₁ ≤ (z i).re - ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1)
    {R₂ : ℝ} (hR₂ : 1 < R₂) (hρR₂ : ∀ i, ρ i * R₂ < (z i).re)
    (hR₂1 : ∀ i, (z i).re + ρ i * R₂ < 1) {c₀ : ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hsub : ∀ i, ‖z i - c₀‖ + ρ i * R₂ < R₀) (hζ : ∀ s ∈ ball c₀ R₀, riemannZeta s ≠ 0)
    {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (eulerTargetReturnSet y riemannZeta (⋃ i, closedBall (z i) (ρ i * r₁)) ε
        ∩ Icc 0 T) := by
  have hρ' : ∀ i, 0 ≤ ρ i := fun i => (hρ i).le
  have hσ₁pos : 0 < σ₁ := by linarith
  set K : Set ℂ := ⋃ i, closedBall (z i) (ρ i * r₁) with hKdef
  have hK : IsCompact K := isCompact_iUnion fun i => isCompact_closedBall _ _
  have hre : ∀ s ∈ K, 0 < s.re := pos_re_of_mem_iUnion_closedBall z hρ hσ₁ hσ₁le hr₁
  have hζc : ContinuousOn riemannZeta K :=
    continuousOn_riemannZeta_iUnion_closedBall z hρ hb hb1 hr₁
  have hsubK : ∀ i, closedBall (z i) (ρ i * r₁) ⊆ K := fun i =>
    subset_iUnion (fun i => closedBall (z i) (ρ i * r₁)) i
  -- a bound for `ζ` on the union
  obtain ⟨M', hM'⟩ := hK.exists_bound_of_continuousOn hζc
  set M : ℝ := max M' 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMK : ∀ s ∈ K, ‖riemannZeta s‖ ≤ M := fun s hs => (hM' s hs).trans (le_max_left _ _)
  -- the constants
  set K₁ : ℝ := Real.sqrt ((1 - r₁ ^ 2)⁻¹) with hK₁
  have hK₁0 : 0 ≤ K₁ := Real.sqrt_nonneg _
  have hK₁1 : 0 < K₁ + 1 := by linarith
  set A₀ : ℝ := M + ε / 2 + 1 with hA₀
  have hA₀pos : 0 < A₀ := by rw [hA₀]; linarith
  set δ : ℝ := min ((K₁ + 1)⁻¹) (ε / (8 * A₀ * (K₁ + 1))) with hδ
  have hδpos : 0 < δ := lt_min (inv_pos.mpr hK₁1) (div_pos hε (by positivity))
  have hδ1 : (K₁ + 1) * δ ≤ 1 := by
    calc (K₁ + 1) * δ ≤ (K₁ + 1) * (K₁ + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left (by rw [hδ]; exact min_le_left _ _) hK₁1.le
      _ = 1 := mul_inv_cancel₀ hK₁1.ne'
  have hδ2 : 2 * (M + ε / 2) * ((K₁ + 1) * δ) ≤ ε / 4 := by
    have h1 : (K₁ + 1) * δ ≤ ε / (8 * A₀) := by
      calc (K₁ + 1) * δ ≤ (K₁ + 1) * (ε / (8 * A₀ * (K₁ + 1))) :=
            mul_le_mul_of_nonneg_left (by rw [hδ]; exact min_le_right _ _) hK₁1.le
        _ = ε / (8 * A₀) := by field_simp
    have h2 : M + ε / 2 ≤ A₀ := by rw [hA₀]; linarith
    calc 2 * (M + ε / 2) * ((K₁ + 1) * δ) ≤ 2 * A₀ * (ε / (8 * A₀)) :=
          mul_le_mul (by linarith) h1 (by positivity) (by positivity)
      _ = ε / 4 := by
          field_simp
          ring
  -- the tails: a common majorant for the remainders and the squared prime vectors
  set C₁ : ℝ := (1 - (2 : ℝ) ^ (-σ₁))⁻¹ / 2 with hC₁
  have hC₁0 : 0 ≤ C₁ := eulerRemainderConstant_nonneg hσ₁pos
  set C : ℝ := Fintype.card ι + C₁ with hC
  have hC0 : 0 ≤ C := by positivity
  have hCcard : (Fintype.card ι : ℝ) ≤ C := by rw [hC]; linarith
  have hCrem : ∀ i, (1 - (2 : ℝ) ^ (-((z i).re - ρ i)))⁻¹ / 2 ≤ C := fun i => by
    rw [hC]
    have := eulerRemainderConstant_anti hσ₁pos (hσ₁le i)
    have h0 : (0 : ℝ) ≤ Fintype.card ι := by positivity
    linarith
  set δ' : ℝ := min δ (δ ^ 2 / 2) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδpos (by positivity)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hδ'le2 : δ' ≤ δ ^ 2 / 2 := min_le_right _ _
  obtain ⟨y₀, -, hy₀⟩ := exists_remainder_tail_le hσ₁ hC0 hδ'pos 0
  -- the base phases, at a stage `y₁ ≥ y₀`
  obtain ⟨y₁, hy₁, c₁, hc₁, hev₁⟩ := exists_pos_density_eulerTargetReturnSet_zeta_union z hρ hσ₁
    hσ₁le hb hb1 hR₂ hρR₂ hR₂1 hR₀ hsub hζ hr₁0 hr₁ (half_pos hε) y₀
  have hne : (eulerTargetReturnSet y₁ riemannZeta K (ε / 2)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    obtain ⟨T, hT, hTpos⟩ := (hev₁.and (eventually_gt_atTop (0 : ℝ))).exists
    rw [hemp, Set.empty_inter, measure_empty, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hT
    exact absurd hT (not_le.mpr (mul_pos hc₁ hTpos))
  obtain ⟨τ₀, hτ₀⟩ := hne
  -- the base event `A`: phases of the primes `≤ y₁` approximating `ζ` within `ε/2` on `K`
  set A : Set (UnitAddTorus Nat.Primes) := unitTorusHomeomorphCircles Nat.Primes ⁻¹'
    eulerPhaseTargetSet y₁ riemannZeta K (ε / 2) with hA
  have hAopen : IsOpen A :=
    (Homeomorph.isOpen_preimage _).mpr (isOpen_eulerPhaseTargetSet y₁ hK hre hζc _)
  have hAne : A.Nonempty := by
    refine ⟨(unitTorusHomeomorphCircles Nat.Primes).symm (circlePhaseFlow primeFrequency τ₀), ?_⟩
    rw [hA, Set.mem_preimage, Homeomorph.apply_symm_apply]
    simp only [eulerPhaseTargetSet, Set.mem_setOf_eq]
    intro s hs
    rw [eulerPhaseProduct_circlePhaseFlow]
    exact hτ₀ s hs
  have hApos : 0 < (torusHaar Nat.Primes A).toReal :=
    ENNReal.toReal_pos (hAopen.measure_pos _ hAne).ne' (measure_ne_top _ _)
  refine ⟨(torusHaar Nat.Primes A).toReal / 4, by positivity, y₁, fun y hy => ?_⟩
  -- the block event `B_y`: the random linear prime sum of the primes in `(y₁, y]` is small
  set Bl : Finset Nat.Primes := primesLE y \ primesLE y₁ with hBl
  set u : Nat.Primes → DiscTuple ι := primeVectorTuple z hρ' with hu
  set By : Set (UnitAddTorus Nat.Primes) := {x | ‖torusPrimePhaseSum Bl u x‖ < δ} with hBy
  have hByopen : IsOpen By := isOpen_lt (continuous_torusPrimePhaseSum Bl u).norm continuous_const
  have htail : ∀ N, ∑ n ∈ Finset.Ico (y₁ + 1) N, C * (n : ℝ) ^ (-(2 * σ₁)) ≤ δ' := by
    intro N
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico_left (by omega)) fun n _ _ => by positivity) (hy₀ N)
  -- Chebyshev: `Haar(B_y) ≥ 1/2`
  have hsumsq : ∑ p ∈ Bl, ‖u p‖ ^ 2 ≤ δ ^ 2 / 2 := by
    calc ∑ p ∈ Bl, ‖u p‖ ^ 2 ≤ ∑ p ∈ Bl, C * ((p : ℕ) : ℝ) ^ (-(2 * σ₁)) :=
          sum_le_sum fun p _ => (norm_primeVectorTuple_sq_le z hρ' hσ₁le p).trans
            (mul_le_mul_of_nonneg_right hCcard (by positivity))
      _ ≤ ∑ n ∈ Finset.Ico (y₁ + 1) (y + 1), C * (n : ℝ) ^ (-(2 * σ₁)) :=
          sum_primesLE_sdiff_le_sum_Ico
            (F := fun n : ℕ => C * (n : ℝ) ^ (-(2 * σ₁))) (fun n => by positivity) y₁ y
      _ ≤ δ' := htail _
      _ ≤ δ ^ 2 / 2 := hδ'le2
  have hBy_half : ENNReal.ofReal (1 / 2) ≤ torusHaar Nat.Primes By := by
    have hcompl : torusHaar Nat.Primes Byᶜ ≤ ENNReal.ofReal (1 / 2) := by
      have hc : Byᶜ = {x | δ ≤ ‖torusPrimePhaseSum Bl u x‖} := by
        ext x
        simp [hBy, not_lt]
      rw [hc]
      refine (measure_torusPrimePhaseSum_ge_le Bl u hδpos).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h1 : torusHaar Nat.Primes By = 1 - torusHaar Nat.Primes Byᶜ := by
      rw [← prob_compl_eq_one_sub hByopen.measurableSet.compl, compl_compl]
    rw [h1]
    calc ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := by
          rw [ENNReal.ofReal_div_of_pos (two_pos : (0 : ℝ) < 2), ENNReal.ofReal_one,
            ENNReal.ofReal_ofNat, one_div, ENNReal.one_sub_inv_two]
      _ ≤ 1 - torusHaar Nat.Primes Byᶜ := tsub_le_tsub_left hcompl 1
  -- `A` and `B_y` are cylinders over disjoint blocks of primes, hence independent
  have hAdet : ∀ x, blockExtendTorus (primesLE y₁) (torusBlockRestrict (primesLE y₁) x) ∈ A
      ↔ x ∈ A := by
    intro x
    have hprod : ∀ s, eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes
        (blockExtendTorus (primesLE y₁) (torusBlockRestrict (primesLE y₁) x))) s
        = eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) s := by
      intro s
      unfold eulerPhaseProduct
      refine prod_congr rfl fun p hp => ?_
      rw [unitTorusHomeomorphCircles_apply_congr (blockExtendTorus_torusBlockRestrict_apply _ x hp)]
    simp only [hA, Set.mem_preimage, eulerPhaseTargetSet, Set.mem_setOf_eq, hprod]
  have hBdet : ∀ x, blockExtendTorus Bl (torusBlockRestrict Bl x) ∈ By ↔ x ∈ By := by
    intro x
    simp only [hBy, Set.mem_setOf_eq]
    rw [torusPrimePhaseSum_congr u fun p hp => blockExtendTorus_torusBlockRestrict_apply Bl x hp]
  have hAB : torusHaar Nat.Primes (A ∩ By) = torusHaar Nat.Primes A * torusHaar Nat.Primes By := by
    rw [eq_setOf_torusBlockRestrict_mem_of_determined hAdet,
      eq_setOf_torusBlockRestrict_mem_of_determined hBdet]
    exact torusHaar_inter_eq_mul_of_disjoint_blocks Finset.disjoint_sdiff
      (isOpen_blockExtendTorus_preimage _ hAopen).measurableSet
      (isOpen_blockExtendTorus_preimage _ hByopen).measurableSet
  -- `A ∩ B_y` lies in the target phases at stage `y`, on every disc at once
  have hsubAB : A ∩ By ⊆ unitTorusHomeomorphCircles Nat.Primes ⁻¹'
      eulerPhaseTargetSet y riemannZeta K ε := by
    rintro x ⟨hxA, hxB⟩
    rw [Set.mem_preimage]
    show ∀ s ∈ K, ‖eulerPhaseProduct y (unitTorusHomeomorphCircles Nat.Primes x) s - riemannZeta s‖ < ε
    intro s hs
    obtain ⟨i, hsi⟩ := mem_iUnion.mp hs
    have hxA' : ∀ s ∈ closedBall (z i) (ρ i * r₁),
        ‖eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) s - riemannZeta s‖
          < ε / 2 := fun s hs => hxA s (hsubK i hs)
    have hxB' : ‖torusPrimePhaseSum Bl (primeVectorOf (z i) (hρ' i)) x‖ < δ := by
      rw [← torusPrimePhaseSum_primeVectorTuple_apply z hρ' Bl x i]
      exact lt_of_le_of_lt (PiLp.norm_apply_le _ i) hxB
    refine norm_eulerPhaseProduct_sub_lt_of_block (z i) (hρ i) (by linarith [hσ₁le i]) hr₁0 hr₁
      hy x (fun s hs => hMK s (hsubK i hs)) hxA' hxB' ?_ hδ1 hδ2 hε s hsi
    refine le_trans ?_ ((htail (y + 1)).trans hδ'le)
    refine sum_le_sum fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ n := by
      have := (Finset.mem_Ico.mp hn).1
      exact_mod_cast (by omega : 1 ≤ n)
    have hexp : (n : ℝ) ^ (-(2 * ((z i).re - ρ i))) ≤ (n : ℝ) ^ (-(2 * σ₁)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hσ₁le i])
    exact mul_le_mul (hCrem i) hexp (by positivity) hC0
  -- the target phases at stage `y` have Haar measure at least `Haar(A)/2`
  have hUy : (torusHaar Nat.Primes A).toReal / 4
      < (torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹'
          eulerPhaseTargetSet y riemannZeta K ε)).toReal := by
    have h1 : torusHaar Nat.Primes A * ENNReal.ofReal (1 / 2)
        ≤ torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹'
          eulerPhaseTargetSet y riemannZeta K ε) := by
      calc torusHaar Nat.Primes A * ENNReal.ofReal (1 / 2)
          ≤ torusHaar Nat.Primes A * torusHaar Nat.Primes By := by gcongr
        _ = torusHaar Nat.Primes (A ∩ By) := hAB.symm
        _ ≤ _ := measure_mono hsubAB
    have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at h2
    linarith
  rw [eulerTargetReturnSet_eq_preimage]
  exact eventually_ofReal_mul_le_volume_preimage_primeFlow
    (isOpen_eulerPhaseTargetSet y hK hre hζc ε) hUy

end RHTower
