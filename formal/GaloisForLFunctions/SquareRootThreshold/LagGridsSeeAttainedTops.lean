import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyMeasuresTheAbscissa

/-!
# Lag grids see attained tops

The one-parameter family `f_v = κ_w(t + v/2) − κ_w(t − v/2)` decides the line from any tail of
lags `v ≥ V` (`onLine_iff_lag_twoBump_nonneg_of_lt_one`). A lag grid `v = kℓ`, `k ≥ N`, that is,
a geometric progression of prime windows `X = e^{kℓ}`, decides it too, unless the off-line depths
have no largest value.

* **Cesàro means on the unit disc** (`tendsto_mean_tsum_geom`). For `Σ|q_t| < ∞`, `|w_t| ≤ 1` and
  `|u| = 1`, the Cesàro means of `ū^k Σ_t q_t w_t^k` tend to `Σ_{w_t = u} q_t`.
* **A one-sided bound controls every frequency** (`norm_tsum_ite_le_of_limsup_nonpos`). If the
  real sequence `b_k = Σ_t q_t w_t^k` has `limsup b_k ≤ 0`, the Cesàro means of `|b_k|` tend to
  `−μ`, `μ = Σ_{w_t = 1} q_t`. Hence `|Σ_{w_t = u} q_t| ≤ −Re μ` for every `|u| = 1`.
* **Grids see attained tops** (`exists_re_gt_of_grid_lag_ge`). Normalize `2 Re S(kℓ)` by the top
  depth `D`: `b_k = Σ_z D(z) e^{(z − D)kℓ}`. A one-sided bound on the grid gives
  `limsup b_k ≤ 0`. The frequency `1` collects the real top exponents, whose coefficients have
  positive real part, so `Re μ ≥ 0`. Off the countably many resonant steps,
  `(x − y)ℓ ∈ 2πℤ` for distinct zero heights `x, y` (`resonantSteps`), the frequency of a top
  zero `ρ₀` collects `ρ₀ − ½` alone, and its coefficient is not zero. So under a grid bound every
  zero right of the line is exceeded by a deeper one: the off-line depths form a chain.

**Criteria** (`onLine_iff_topAttained_and_grid_lag_nonneg`,
`zeta_onLine_iff_topAttained_and_grid_primeWindow_nonneg`). For all but countably many widths
and grid steps, all zeros lie on the line iff the off-line zeros, if any, include one of largest
real part, and the grid tests are Weil nonnegative. For `ζ`, these are the window functionals at
`X = e^{kℓ}`, `k ≥ N`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Cesàro means on the unit disc -/

/-- **Cesàro means of an exponential sum on the unit disc.** For `Σ_t |q_t| < ∞`, `|w_t| ≤ 1` and
`|u| = 1`, the Cesàro means of `ū^k Σ_t q_t w_t^k` tend to `Σ_{w_t = u} q_t`. -/
theorem tendsto_mean_tsum_geom {ι : Type*} [Countable ι] {q w : ι → ℂ}
    (hq : Summable fun t => ‖q t‖) (hw : ∀ t, ‖w t‖ ≤ 1) {u : ℂ} (hu : ‖u‖ = 1) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, conj u ^ k * ∑' t, q t * w t ^ k)
      atTop (𝓝 (∑' t, if w t = u then q t else 0)) := by
  classical
  have huu : u * conj u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp
  have hwu : ∀ t, ‖w t * conj u‖ ≤ 1 := fun t => by
    rw [norm_mul, Complex.norm_conj, hu, mul_one]; exact hw t
  have hiff : ∀ t, w t * conj u = 1 ↔ w t = u := fun t => by
    constructor
    · intro h
      calc w t = w t * (conj u * u) := by rw [mul_comm (conj u) u, huu, mul_one]
        _ = u := by rw [← mul_assoc, h, one_mul]
    · intro h; rw [h, huu]
  have hsum : ∀ k : ℕ, Summable fun t => q t * (w t * conj u) ^ k := fun k =>
    Summable.of_norm_bounded hq fun t => by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hwu t))
  have hrw : ∀ N : ℕ, (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, conj u ^ k * ∑' t, q t * w t ^ k =
      ∑' t, q t * ((N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, (w t * conj u) ^ k) := fun N => by
    have e : ∀ k : ℕ, conj u ^ k * ∑' t, q t * w t ^ k = ∑' t, q t * (w t * conj u) ^ k :=
      fun k => by
        rw [← tsum_mul_left]
        exact tsum_congr fun t => by ring
    simp_rw [e]
    rw [← Summable.tsum_finsetSum fun k _ => hsum k, ← tsum_mul_left]
    refine tsum_congr fun t => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hrw]
  refine tendsto_tsum_of_dominated_convergence hq (fun t => ?_) (Eventually.of_forall fun N t => ?_)
  · by_cases h : w t = u
    · rw [if_pos h]
      have h1 : w t * conj u = 1 := (hiff t).mpr h
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [h1]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [inv_mul_cancel₀ (by exact_mod_cast hN.ne'), mul_one]
    · rw [if_neg h]
      simpa using (tendsto_geom_mean (hwu t) fun h1 => h ((hiff t).mp h1)).const_mul (q t)
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_geom_mean_le (hwu t) N)

/-- `|x| = 2 max(x, 0) − x`. -/
theorem abs_eq_two_mul_max_sub (x : ℝ) : |x| = 2 * max x 0 - x := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, max_eq_left h]; ring
  · rw [abs_of_nonpos h, max_eq_right h]; ring

/-- **A one-sided bound makes the mean of `|b_k|` equal to minus its mean.** If
`limsup b_k ≤ 0` and the Cesàro means of `b_k` tend to `μ`, those of `|b_k|` tend to `−μ`. -/
theorem tendsto_mean_abs_of_limsup_nonpos {b : ℕ → ℝ}
    (hb : ∀ ε > 0, ∀ᶠ k : ℕ in atTop, b k ≤ ε) {μ : ℝ}
    (hμ : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, b k) atTop (𝓝 μ)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, |b k|) atTop (𝓝 (-μ)) := by
  have hpos : Tendsto (fun k => max (b k) 0) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.mp (hb (ε / 2) (half_pos hε))
    refine ⟨K, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_right _ _)]
    exact (max_le (hK k hk) (half_pos hε).le).trans_lt (half_lt_self hε)
  have h := ((hpos.cesaro).const_mul 2).sub hμ
  rw [mul_zero, zero_sub] at h
  refine h.congr fun N => ?_
  simp_rw [abs_eq_two_mul_max_sub]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **A one-sided bound controls every frequency.** Let `b_k = Σ_t q_t w_t^k` be real, with
`Σ|q_t| < ∞`, `|w_t| ≤ 1` and `limsup b_k ≤ 0`. Then `|Σ_{w_t = u} q_t| ≤ −Re Σ_{w_t = 1} q_t`
for every `|u| = 1`. -/
theorem norm_tsum_ite_le_of_limsup_nonpos {ι : Type*} [Countable ι] {q w : ι → ℂ}
    (hq : Summable fun t => ‖q t‖) (hw : ∀ t, ‖w t‖ ≤ 1)
    (hreal : ∀ k : ℕ, (∑' t, q t * w t ^ k).im = 0)
    (hb : ∀ ε > 0, ∀ᶠ k : ℕ in atTop, (∑' t, q t * w t ^ k).re ≤ ε) {u : ℂ} (hu : ‖u‖ = 1) :
    ‖∑' t, if w t = u then q t else 0‖ ≤ -(∑' t, if w t = 1 then q t else 0).re := by
  classical
  set b : ℕ → ℝ := fun k => (∑' t, q t * w t ^ k).re with hbdef
  have hB : ∀ k, ∑' t, q t * w t ^ k = (b k : ℂ) := fun k =>
    Complex.ext rfl (by rw [Complex.ofReal_im]; exact hreal k)
  have h1 := tendsto_mean_tsum_geom hq hw (u := 1) (by simp)
  simp only [map_one, one_pow, one_mul] at h1
  have hμ : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, b k) atTop
      (𝓝 (∑' t, if w t = 1 then q t else 0).re) := by
    refine ((Complex.continuous_re.tendsto _).comp h1).congr fun N => ?_
    simp only [Function.comp, hB]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_sum,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have habs := tendsto_mean_abs_of_limsup_nonpos hb hμ
  refine le_of_tendsto_of_tendsto (tendsto_mean_tsum_geom hq hw hu).norm habs
    (Eventually.of_forall fun N => ?_)
  beta_reduce
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
    (by positivity)
  rw [norm_mul, norm_pow, Complex.norm_conj, hu, one_pow, one_mul, hB, Complex.norm_real,
    Real.norm_eq_abs, Complex.ofReal_re]

/-! ### Resonant grid steps -/

/-- The heights of the zeros, their negatives, and `0`. -/
def zeroHeights (Z : ZeroConfig) : Set ℝ :=
  insert 0 ((fun ρ : ℂ => ρ.im) '' Z.carrier ∪ (fun ρ : ℂ => -ρ.im) '' Z.carrier)

/-- The grid steps at which two distinct zero heights resonate: `(x − y)ℓ ∈ 2πℤ`. -/
def resonantSteps (Z : ZeroConfig) : Set ℝ :=
  {ℓ | ∃ x ∈ zeroHeights Z, ∃ y ∈ zeroHeights Z, x ≠ y ∧ ∃ n : ℤ, ℓ * (x - y) = 2 * π * n}

theorem countable_resonantSteps (Z : ZeroConfig) : (resonantSteps Z).Countable := by
  have hH : (zeroHeights Z).Countable :=
    (((carrier_countable Z).image _).union ((carrier_countable Z).image _)).insert 0
  refine (hH.biUnion fun x _ => hH.biUnion fun y _ => Set.countable_iUnion fun n : ℤ =>
    Set.Subsingleton.countable (s := {ℓ : ℝ | x ≠ y ∧ ℓ * (x - y) = 2 * π * n})
      fun ℓ₁ h₁ ℓ₂ h₂ => mul_right_cancel₀ (sub_ne_zero.mpr h₁.1) (h₁.2.trans h₂.2.symm)).mono ?_
  rintro ℓ ⟨x, hx, y, hy, hxy, n, hn⟩
  simp only [Set.mem_iUnion]
  exact ⟨x, hx, y, hy, n, hxy, hn⟩

/-- Off the resonant steps, the grid frequency `e^{(z − D)ℓ}` determines the exponent. -/
theorem eq_of_cexp_eq_of_not_resonant {Z : ZeroConfig} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hres : ℓ ∉ resonantSteps Z) {z z' : ℂ} (hz : z.im ∈ zeroHeights Z)
    (hz' : z'.im ∈ zeroHeights Z) {D : ℝ} (h : cexp ((z - D) * ℓ) = cexp ((z' - D) * ℓ)) :
    z = z' := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hre := congrArg Complex.re hn
  have him := congrArg Complex.im hn
  simp at hre him
  apply Complex.ext
  · exact hre.resolve_right hℓ.ne'
  · by_contra hne
    exact hres ⟨z.im, hz, z'.im, hz', hne, n, by linarith⟩

theorem im_mem_zeroHeights_of_evenCoeff_ne_zero {Z : ZeroConfig} {b : ℝ → ℂ} {z : ℂ}
    (hz : evenCoeff Z b z ≠ 0) : z.im ∈ zeroHeights Z := by
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · exact Or.inr (Or.inl ⟨_, h, by simp⟩)
  · exact Or.inr (Or.inr ⟨_, h, by simp⟩)

/-! ### Lag grids see attained tops -/

/-- **Lag grids see attained tops.** Let `Z` be tempered, `w > 0` a width whose transform
vanishes at no `γ_ρ` of an off-line zero, and `ℓ > 0` a non-resonant grid step. If `Re W ≥ −C` on
the tests `κ_w(t + kℓ/2) − κ_w(t − kℓ/2)` for all `k ≥ N`, then every zero right of the critical
line is exceeded in real part by another zero. -/
theorem exists_re_gt_of_grid_lag_ge (Z : ZeroConfig) (hZ : TemperedConfig Z) {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps Z) {C : ℝ} {N : ℕ}
    (hm : ∀ k : ℕ, N ≤ k → -C ≤ (Z.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
      (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hre₀ : 1 / 2 < ρ₀.re) :
    ∃ ρ ∈ Z.carrier, ρ₀.re < ρ.re := by
  classical
  by_contra hno
  push Not at hno
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs := modScaledBump_support hw 0
  set D := ρ₀.re - 1 / 2 with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
  haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
  have hDs : Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
    have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hreD : ∀ z : ι, (z : ℂ).re ≤ D := fun z => by
    rcases mem_of_evenCoeff_ne_zero z.2 with h | h
    · have := hno _ h; simp at this; linarith
    · have := hno _ h; simp at this; linarith
  -- the grid frequencies `e^{(z − D)ℓ}` lie in the unit disc
  set W : ι → ℂ := fun z => cexp (((z : ℂ) - D) * ℓ) with hWdef
  have hWre : ∀ z : ι, ‖W z‖ = Real.exp (((z : ℂ).re - D) * ℓ) := fun z => by
    rw [hWdef, Complex.norm_exp]; simp
  have hWn : ∀ z : ι, ‖W z‖ ≤ 1 := fun z => by
    rw [hWre, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hreD z]) hℓ.le
  -- the normalized grid values
  have hgrid : ∀ k : ℕ, ∑' z : ι, evenCoeff Z b z * W z ^ k =
      ((Real.exp (-D * (k * ℓ)) * (2 * (lagStructure Z b (k * ℓ)).re) : ℝ) : ℂ) := fun k => by
    have hsub :
        Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * ((k * ℓ : ℝ) : ℂ))) ⊆ ι :=
      fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * ((k * ℓ : ℝ) : ℂ)) = 0 by
        rw [h0, zero_mul])
    rw [Complex.ofReal_mul, (two_re_lagStructure_eq Z hZ hb hbs (k * ℓ)).2,
      ← tsum_subtype_eq_of_support_subset hsub, ← tsum_mul_left]
    refine tsum_congr fun z => ?_
    have e : W z ^ k = cexp (((-D * (k * ℓ) : ℝ) : ℂ)) * cexp ((z : ℂ) * ((k * ℓ : ℝ) : ℂ)) := by
      rw [hWdef, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e, Complex.ofReal_exp]
    ring
  have hreal : ∀ k : ℕ, (∑' z : ι, evenCoeff Z b z * W z ^ k).im = 0 := fun k => by
    rw [hgrid, Complex.ofReal_im]
  have hlim : ∀ ε > 0, ∀ᶠ k : ℕ in atTop, (∑' z : ι, evenCoeff Z b z * W z ^ k).re ≤ ε := by
    intro ε hε
    set A := max (2 * (lagStructure Z b 0).re + C) 0 with hA
    have hexp : Tendsto (fun k : ℕ => Real.exp (-D * (k * ℓ)) * A) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => -D * (k * ℓ)) atTop atBot := by
        have : Tendsto (fun k : ℕ => D * ℓ * (k : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos hD0 hℓ)
        refine (tendsto_neg_atTop_atBot.comp this).congr fun k => ?_
        simp only [Function.comp]
        ring
      simpa using (Real.tendsto_exp_atBot.comp h1).mul_const A
    filter_upwards [eventually_ge_atTop N, (tendsto_order.1 hexp).2 ε hε] with k hk hk'
    rw [hgrid, Complex.ofReal_re]
    have h := hm k hk
    rw [re_W_lag_eq Z hZ hb hbs] at h
    have h2 : 2 * (lagStructure Z b (k * ℓ)).re ≤ A := by
      rw [hA]; exact (by linarith : _ ≤ _).trans (le_max_left _ _)
    exact (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le).trans hk'.le
  -- the top zero `ρ₀` and its frequency
  set z₀ : ℂ := ρ₀ - 1 / 2 with hz₀def
  have hz₀ : evenCoeff Z b z₀ ≠ 0 :=
    evenCoeff_modScaledBump_zero_sub_half_ne_zero Z hw hρ₀ (hgood ρ₀ hρ₀ (ne_of_gt hre₀))
  have hz₀re : z₀.re = D := by rw [hz₀def, hD]; simp
  have hWz₀ : ‖W ⟨z₀, hz₀⟩‖ = 1 := by
    rw [hWre]; simp only [hz₀re, sub_self, zero_mul, Real.exp_zero]
  have hsumι : Summable fun z : ι => ‖evenCoeff Z b z‖ := hDs.subtype ι
  have key := norm_tsum_ite_le_of_limsup_nonpos hsumι hWn hreal hlim hWz₀
  -- only `z₀` sits at its frequency
  have hL : (∑' z : ι, if W z = W ⟨z₀, hz₀⟩ then evenCoeff Z b z else 0) =
      evenCoeff Z b z₀ := by
    rw [tsum_eq_single ⟨z₀, hz₀⟩ fun z hz => if_neg fun h => hz (Subtype.ext
      (eq_of_cexp_eq_of_not_resonant hℓ hres (im_mem_zeroHeights_of_evenCoeff_ne_zero z.2)
        (im_mem_zeroHeights_of_evenCoeff_ne_zero hz₀) h)), if_pos rfl]
  -- the frequency `1` carries real top exponents only, with positive coefficients
  have hR : 0 ≤ (∑' z : ι, if W z = 1 then evenCoeff Z b z else 0).re := by
    rw [Complex.re_tsum (f := fun z : ι => if W z = 1 then evenCoeff Z b z else 0)
      (Summable.of_norm_bounded hsumι fun z => by split_ifs <;> simp)]
    refine tsum_nonneg fun z => ?_
    split_ifs with h
    · have h0 : (z : ℂ) = (D : ℂ) := eq_of_cexp_eq_of_not_resonant hℓ hres
        (im_mem_zeroHeights_of_evenCoeff_ne_zero z.2) (by simp [zeroHeights])
        (h.trans (by simp))
      have him : (z : ℂ).im = 0 := by rw [h0, Complex.ofReal_im]
      have hmem : (1 / 2 + (z : ℂ)) ∈ Z.carrier :=
        (mem_of_evenCoeff_ne_zero z.2).elim id fun h' => by
          rwa [show conj (z : ℂ) = z from Complex.ext (by simp) (by simp [him])] at h'
      exact (re_evenCoeff_modScaledBump_zero_pos Z hw hmem him).le
    · simp
  rw [hL] at key
  have := norm_pos_iff.mpr hz₀
  linarith

/-- **Lag grids decide the line up to chains.** Let `Z` be tempered, `w` a width whose transform
vanishes at no `γ_ρ` of an off-line zero, and `ℓ > 0` a non-resonant grid step. All zeros lie on
the critical line iff the zeros right of the line, if any, include one of largest real part, and
`Re W ≥ 0` on `κ_w(t + kℓ/2) − κ_w(t − kℓ/2)` for all `k ≥ N`. -/
theorem onLine_iff_topAttained_and_grid_lag_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps Z) (N : ℕ) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ↔
      ((∃ ρ ∈ Z.carrier, 1 / 2 < ρ.re) → ∃ ρ₀ ∈ Z.carrier, ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) ∧
        ∀ k : ℕ, N ≤ k → 0 ≤ (Z.W (twoBump (modScaledBump w 0) (k * ℓ) (-1))
          (twoBump (modScaledBump w 0) (k * ℓ) (-1))).re := by
  constructor
  · intro hon
    refine ⟨fun ⟨ρ, hρ, hre⟩ => absurd (hon ρ hρ) (ne_of_gt hre), fun k _ =>
      weil_nonneg_of_onLine Z hon _⟩
  · rintro ⟨htop, hm⟩ ρ hρ
    by_contra hre
    obtain ⟨t, ht, -⟩ := exists_rightZero_of_offLine Z hρ hre
    obtain ⟨ρ₀, hρ₀, hmax⟩ := htop ⟨t, ht.1, ht.2⟩
    obtain ⟨ρ', hρ', hgt⟩ := exists_re_gt_of_grid_lag_ge Z hZ hw hgood hℓ hres (C := 0)
      (fun k hk => by rw [neg_zero]; exact hm k hk) hρ₀ (lt_of_lt_of_le ht.2 (hmax t ht.1))
    exact absurd (hmax ρ' hρ') (not_le.mpr hgt)

/-- **For `ζ`: a geometric progression of prime windows decides the line, up to chains.** For all
but countably many widths `w ∈ (0, ½ log 2)`, all but countably many grid steps `ℓ > 0` and every
`N`, RH holds iff the zeros right of the line, if any, include one of largest real part, and the
window functionals `P_v` of `κ_w(t + v/2) − κ_w(t − v/2)` are nonnegative at `v = kℓ`, `k ≥ N`:
the windows at `X = e^{kℓ}`. -/
theorem zeta_onLine_iff_topAttained_and_grid_primeWindow_nonneg :
    ∃ E : Set ℝ, E.Countable ∧ ∃ E' : Set ℝ, E'.Countable ∧ ∀ w : ℝ, 0 < w →
      2 * w < Real.log 2 → w ∉ E → ∀ ℓ : ℝ, 0 < ℓ → ℓ ∉ E' → ∀ N : ℕ,
        ((∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) ↔
          ((∃ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re) →
              ∃ ρ₀ ∈ zetaZeroConfig.carrier, ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ ρ₀.re) ∧
            ∀ k : ℕ, N ≤ k → 0 ≤ (lagPrimeWindowRHS (k * ℓ) w
              (EF.weilTest (twoBump (modScaledBump w 0) (k * ℓ) (-1))
                (twoBump (modScaledBump w 0) (k * ℓ) (-1)))).re) := by
  refine ⟨_, countable_bad_widths zetaZeroConfig, _, countable_resonantSteps zetaZeroConfig,
    fun w hw hw2 hwE ℓ hℓ hres N => ?_⟩
  have hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  rw [onLine_iff_topAttained_and_grid_lag_nonneg _ temperedConfig_zetaZeroConfig hw hgood hℓ hres N]
  refine and_congr_right fun _ => forall_congr' fun k => imp_congr_right fun _ => ?_
  have hv : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le
  rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) (k * ℓ) (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) (k * ℓ) ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) (k * ℓ) (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv]

end GaloisForLFunctions.SquareRootThreshold
