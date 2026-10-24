import GaloisForLFunctions.SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDegreeFiltrationOfTheHodgeDefect
import GaloisForLFunctions.RHTower.PrimeBlindKernelSpectral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Hodge defect of `ζ` is finite at every degree

The Hodge defect at degree `a` (`hodgeDefectAt`) counts the negative squares of Weil's form on
tests supported in `[−a, a]`. Over `𝔽_q` it is `0` or `∞` at every degree: the scaling surface of
a curve is a lag lattice, and an impure curve already has infinite defect from the window degree
`(2g − 1) log q/2` on (`hodgeDefectAt_curveConfig`); the same holds for every lag lattice
(`hodgeDefectAt_lagFormula`). For `ζ` the defect is finite at every degree, unconditionally.

**Theorem** (`hodgeDefectAt_zeta_le`, `hodgeDefectAt_zeta_lt_top`). For `a ≥ 0`,
`hodgeDefectAt ζ a ≤ 1 + 2T(a)(2a + 2)/π` with `T(a) = 4(e^{2E} − 1)`, `E = 10 + 68e^a`.

The mechanism is the archimedean place together with the Euler product.
* *Horizon.* On tests of aperture `a` whose transform vanishes at the pole `i/2`, Weil's form is
  the symbol integral `∫ |h_F|²(μ + P_X)`, `X = e^{2a}`; the Euler product bounds the prime symbol
  by `68√X`, and the archimedean symbol grows like `log|τ|`, so `μ + P_X ≥ E/2π` above `T(a)`
  (`RHTower.mu_add_PX_ge`). A test with `W(F, F) < 0` therefore carries more than half of its
  spectral mass below the horizon: `π‖F‖² < ∫_{−T}^{T} |h_F|²`
  (`pi_mul_integral_lt_of_re_W_neg`).
* *Bessel count.* Such tests form a space of dimension at most `2T(2a + 2)/π`: in an orthonormal
  basis each vector carries mass `> π` below the horizon, and at each frequency Bessel's inequality
  bounds the total by the square norm `2a + 2` of the cut-off character
  (`finrank_mul_le_of_concentrated`).
* One pole condition costs one dimension.

For negative spaces with a margin, `Re W ≤ −ε‖f‖²`, the corpus bounds the dimension by the number
of off-line pairs below a height `exp(O(e^a + log(1/ε)))` (`RHTower.zeta_weil_negative_index_le`);
that bound degenerates as `ε → 0`. The count here needs no margin and is uniform at each degree.

So the Hodge defect of `ℤ` is filtered by finite numbers: at each degree only finitely many
right zeros can be seen, and if there are infinitely many, the degree at which `n` of them are
seen tends to infinity with `n`, at least like `log log n`. A lag lattice, a fake curve or an
impure curve has no archimedean place and no Euler-product bound on its prime symbol, and its
defect jumps to `∞` at a finite degree.
-/

open Complex MeasureTheory Set Filter Zeta23 GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate InnerProductSpace Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Bessel's inequality counts concentrated directions -/

/-- **Bessel count.** Let `Ψ` map a finite-dimensional space `U` into an inner product space and
let `φ τ` have square norm at most `c`. If every nonzero `x ∈ U` has
`κ‖Ψ x‖² < ∫_{−T}^{T} |⟪Ψ x, φ τ⟫|²`, then `dim U · κ ≤ 2Tc`: an orthonormal basis of `Ψ U`
consists of `dim U` vectors each carrying more than `κ`, and at each `τ` Bessel's inequality
bounds their total by `‖φ τ‖²`. -/
theorem finrank_mul_le_of_concentrated {M E : Type*} [AddCommGroup M] [Module ℂ M]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (U : Submodule ℂ M) [FiniteDimensional ℂ U]
    (Ψ : M →ₗ[ℂ] E) (φ : ℝ → E) {κ T c : ℝ} (hT : 0 ≤ T) (hφ : ∀ τ, ‖φ τ‖ ^ 2 ≤ c)
    (hcont : ∀ x ∈ U, Continuous fun τ => ⟪Ψ x, φ τ⟫_ℂ)
    (hconc : ∀ x ∈ U, x ≠ 0 → κ * ‖Ψ x‖ ^ 2 < ∫ τ in (-T)..T, ‖⟪Ψ x, φ τ⟫_ℂ‖ ^ 2) :
    (Module.finrank ℂ U : ℝ) * κ ≤ 2 * T * c := by
  set Ψ' : U →ₗ[ℂ] E := Ψ.domRestrict U with hΨ'
  have hinj : Function.Injective Ψ' := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    by_contra hy0
    have hy0' : (y : M) ≠ 0 := fun h => hy0 (Subtype.ext h)
    have hΨ : Ψ y = 0 := hy
    have h := hconc y y.2 hy0'
    simp [hΨ] at h
  set V := LinearMap.range Ψ'
  have hrank : Module.finrank ℂ V = Module.finrank ℂ U := LinearMap.finrank_range_of_inj hinj
  set b := stdOrthonormalBasis ℂ V
  have hon : Orthonormal ℂ (fun j => (b j : E)) := b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hpre : ∀ j, ∃ y ∈ U, Ψ y = (b j : E) ∧ y ≠ 0 := by
    intro j
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (b j).2
    refine ⟨y, y.2, hy, fun h0 => ?_⟩
    have hnorm : ‖(b j : E)‖ = 1 := hon.1 j
    have hb : (b j : E) = 0 := by
      rw [← hy, hΨ', LinearMap.domRestrict_apply, h0, map_zero]
    rw [hb, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hcj : ∀ j, Continuous fun τ => ⟪(b j : E), φ τ⟫_ℂ := by
    intro j
    obtain ⟨y, hyU, hy, -⟩ := hpre j
    rw [← hy]
    exact hcont y hyU
  have hlow : ∀ j, κ < ∫ τ in (-T)..T, ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2 := by
    intro j
    obtain ⟨y, hyU, hy, hy0⟩ := hpre j
    have h := hconc y hyU hy0
    rwa [hy, hon.1 j, one_pow, mul_one] at h
  have hii : ∀ j, IntervalIntegrable (fun τ => ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2) volume (-T) T :=
    fun j => ((hcj j).norm.pow 2).intervalIntegrable _ _
  have hsum : ∑ j, ∫ τ in (-T)..T, ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2 ≤ 2 * T * c := by
    rw [← intervalIntegral.integral_finsetSum fun j _ => hii j]
    calc ∫ τ in (-T)..T, ∑ j, ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2
        ≤ ∫ _τ in (-T)..T, c := by
          refine intervalIntegral.integral_mono_on (by linarith)
            ((continuous_finsetSum _ fun j _ => (hcj j).norm.pow 2).intervalIntegrable _ _)
            intervalIntegrable_const fun τ _ => ?_
          exact (hon.sum_inner_products_le (φ τ) (s := Finset.univ)).trans (hφ τ)
      _ = 2 * T * c := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hκ : (Module.finrank ℂ V : ℝ) * κ ≤ ∑ j, ∫ τ in (-T)..T, ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2 := by
    have h : ∑ _j : Fin (Module.finrank ℂ V), κ ≤
        ∑ j, ∫ τ in (-T)..T, ‖⟪(b j : E), φ τ⟫_ℂ‖ ^ 2 :=
      Finset.sum_le_sum fun j _ => (hlow j).le
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  rw [← hrank]
  linarith

/-! ### The archimedean horizon -/

/-- The horizon frequency `T(a) = 4(e^{2E} − 1)`, `E = 10 + 68e^a`: above it the symbol
`μ + P_X` of aperture `a` is at least `E/2π`. -/
def horizonFreq (a : ℝ) : ℝ :=
  4 * (Real.exp (2 * RHTower.horizonExponent (Real.exp (2 * a))) - 1)

theorem horizonFreq_nonneg (a : ℝ) : 0 ≤ horizonFreq a := by
  have hE := RHTower.horizonExponent_pos (Real.exp (2 * a))
  have h : 1 ≤ Real.exp (2 * RHTower.horizonExponent (Real.exp (2 * a))) :=
    Real.one_le_exp (by linarith)
  unfold horizonFreq
  linarith

/-- The symbol dominates the step `(E − 2E·1_{[−T, T]})/2π`. -/
theorem step_le_mu_add_PX (a τ : ℝ) :
    (RHTower.horizonExponent (Real.exp (2 * a)) -
        2 * RHTower.horizonExponent (Real.exp (2 * a)) *
          (Icc (-horizonFreq a) (horizonFreq a)).indicator (fun _ => (1 : ℝ)) τ) / (2 * π) ≤
      mu τ + PX (Real.exp (2 * a)) τ := by
  set E := RHTower.horizonExponent (Real.exp (2 * a)) with hEdef
  have hT := horizonFreq_nonneg a
  refine le_trans ?_ (RHTower.mu_add_PX_ge (Real.exp_pos _).le τ)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  by_cases hτ : τ ∈ Icc (-horizonFreq a) (horizonFreq a)
  · rw [indicator_of_mem hτ]
    have : 0 ≤ Real.log (1 + |τ| / 4) :=
      Real.log_nonneg (by have := abs_nonneg τ; linarith)
    linarith
  · rw [indicator_of_notMem hτ]
    have hTτ : horizonFreq a < |τ| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hτ
      rcases hτ with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hlog : 2 * E < Real.log (1 + |τ| / 4) := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      unfold horizonFreq at hTτ
      rw [← hEdef] at hTτ
      linarith
    linarith

/-- **The band inequality.** If `F ∈ C²` is supported in `[−a, a]` and `h_F(i/2) = 0`, then
`Re W_ζ(F, F) ≥ E‖F‖² − (E/π)∫_{−T}^{T} |h_F|²` with `T = T(a)`, `E = 10 + 68e^a`: the pole terms
vanish, the symbol is at least `−E/2π` below the horizon and `E/2π` above it, and
`∫|h_F|² = 2π‖F‖²`. -/
theorem re_W_zeta_ge_band {a : ℝ} {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hFs : tsupport F ⊆ Icc (-a) a) (hp : paperFT F (I / 2) = 0) :
    RHTower.horizonExponent (Real.exp (2 * a)) * (∫ u, ‖F u‖ ^ 2) -
        RHTower.horizonExponent (Real.exp (2 * a)) / π *
          ∫ τ in (-horizonFreq a)..horizonFreq a, ‖paperFT F τ‖ ^ 2 ≤
      (zetaZeroConfig.W F F).re := by
  have hFc : HasCompactSupport F :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport F) hFs
  set E := RHTower.horizonExponent (Real.exp (2 * a)) with hEdef
  set T := horizonFreq a with hTdef
  have hT : 0 ≤ T := horizonFreq_nonneg a
  have hfac := EF.paperFT_weilTest hF.continuous hF.continuous hFc hFc
  have hpole1 : paperFT (EF.weilTest F F) (I / 2) = 0 := by rw [hfac, hp, zero_mul]
  have hpole2 : paperFT (EF.weilTest F F) (-I / 2) = 0 := by
    have hc : (starRingEnd ℂ) (-I / 2) = I / 2 := by
      rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
    rw [hfac, hc, hp, map_zero, mul_zero]
  have hWeq := GaloisForLFunctions.SquareRootThreshold.zetaZeroConfig_W_eq_pole_add_integral hF hFs
  rw [hpole1, hpole2, zero_add, zero_add] at hWeq
  set N : ℝ → ℝ := fun τ => ‖paperFT F τ‖ ^ 2 with hNdef
  set g : ℝ → ℝ := fun τ => N τ * (mu τ + PX (Real.exp (2 * a)) τ) with hgdef
  have hgeq : ∀ τ : ℝ, paperFT (EF.weilTest F F) τ * ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ) =
      ((g τ : ℝ) : ℂ) := by
    intro τ
    rw [RHTower.paperFT_weilTest_self_ofReal hF.continuous hFc, hgdef, hNdef]
    push_cast
    ring
  have hreW : (zetaZeroConfig.W F F).re = ∫ τ, g τ := by
    rw [hWeq]
    simp_rw [hgeq]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have hg_int : Integrable g := by
    have h := (RHTower.integrable_paperFT_mul_mu_add_PX
      (EF.weilTest_contDiff hF hF.continuous hFc) (EF.weilTest_hasCompactSupport hFc hFc)
      (2 * a)).re
    refine h.congr (Eventually.of_forall fun τ => ?_)
    simp only [hgeq]
    exact Complex.ofReal_re _
  have hN : Integrable N := RHTower.integrable_normSq_paperFT hF hFs
  have hNi : Integrable ((Icc (-T) T).indicator N) := hN.indicator measurableSet_Icc
  set s : ℝ → ℝ := fun τ => E / (2 * π) * N τ - E / π * (Icc (-T) T).indicator N τ with hsdef
  have hs_int : Integrable s := (hN.const_mul _).sub (hNi.const_mul _)
  have hpt : ∀ τ, s τ ≤ g τ := by
    intro τ
    have hstep := step_le_mu_add_PX a τ
    rw [← hEdef, ← hTdef] at hstep
    have hN0 : 0 ≤ N τ := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hstep hN0
    have hπ : 0 < π := Real.pi_pos
    by_cases hτ : τ ∈ Icc (-T) T
    · rw [indicator_of_mem hτ] at hmul
      simp only [hsdef, hgdef, indicator_of_mem hτ]
      have : N τ * ((E - 2 * E * 1) / (2 * π)) = E / (2 * π) * N τ - E / π * N τ := by
        field_simp
      linarith
    · rw [indicator_of_notMem hτ] at hmul
      simp only [hsdef, hgdef, indicator_of_notMem hτ]
      have : N τ * ((E - 2 * E * 0) / (2 * π)) = E / (2 * π) * N τ - E / π * 0 := by
        ring
      linarith
  have hle : ∫ τ, s τ ≤ ∫ τ, g τ := integral_mono hs_int hg_int hpt
  have hplan : ∫ τ, N τ = 2 * π * ∫ u, ‖F u‖ ^ 2 := RHTower.integral_norm_sq_paperFT_eq hF hFs
  have hind : ∫ τ, (Icc (-T) T).indicator N τ = ∫ τ in (-T)..T, N τ := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      integral_indicator measurableSet_Icc]
  have hs_eq : ∫ τ, s τ =
      E / (2 * π) * (2 * π * ∫ u, ‖F u‖ ^ 2) - E / π * ∫ τ in (-T)..T, N τ := by
    rw [hsdef, integral_sub (hN.const_mul _) (hNi.const_mul _), integral_const_mul,
      integral_const_mul, hplan, hind]
  have hπ : 0 < π := Real.pi_pos
  have h1 : E / (2 * π) * (2 * π * ∫ u, ‖F u‖ ^ 2) = E * ∫ u, ‖F u‖ ^ 2 := by
    field_simp
  have hJ : (∫ τ in (-T)..T, N τ) = intervalIntegral N (-T) T volume := rfl
  rw [hJ] at hs_eq
  rw [hreW]
  linarith

theorem pi_mul_lt_of_band {E A J W : ℝ} (hE : 0 < E) (hband : E * A - E / π * J ≤ W)
    (hW : W < 0) : π * A < J := by
  have hπ := Real.pi_pos
  have h1 : E * A < E * (J / π) := by
    have : E / π * J = E * (J / π) := by ring
    linarith
  have h3 : A < J / π := lt_of_mul_lt_mul_left h1 hE.le
  rw [lt_div_iff₀ hπ] at h3
  linarith

/-- **Weil-negative tests live below the horizon.** If `F ∈ C²` is supported in `[−a, a]`,
`h_F(i/2) = 0` and `Re W_ζ(F, F) < 0`, then `π‖F‖² < ∫_{−T}^{T} |h_F|²` with `T = T(a)`. -/
theorem pi_mul_integral_lt_of_re_W_neg {a : ℝ} {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hFs : tsupport F ⊆ Icc (-a) a) (hp : paperFT F (I / 2) = 0)
    (hW : (zetaZeroConfig.W F F).re < 0) :
    π * ∫ u, ‖F u‖ ^ 2 < ∫ τ in (-horizonFreq a)..horizonFreq a, ‖paperFT F τ‖ ^ 2 := by
  exact pi_mul_lt_of_band (RHTower.horizonExponent_pos _) (re_W_zeta_ge_band hF hFs hp) hW

/-! ### The cut-off character and the `L²` realization of a test family -/

/-- A continuous cut-off equal to `1` on `[−a, a]`, with values in `[0, 1]`, vanishing outside
`[−a − 1, a + 1]`. -/
def plateau (a u : ℝ) : ℝ := max 0 (min 1 (a + 1 - |u|))

theorem continuous_plateau (a : ℝ) : Continuous (plateau a) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

theorem plateau_eq_one {a u : ℝ} (hu : u ∈ Icc (-a) a) : plateau a u = 1 := by
  have h : |u| ≤ a := abs_le.mpr hu
  unfold plateau
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem plateau_nonneg (a u : ℝ) : 0 ≤ plateau a u := le_max_left _ _

theorem plateau_le_one (a u : ℝ) : plateau a u ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem plateau_eq_zero {a u : ℝ} (hu : u ∉ Icc (-(a + 1)) (a + 1)) : plateau a u = 0 := by
  have h : a + 1 < |u| := by
    by_contra h
    exact hu (abs_le.mp (not_lt.mp h))
  unfold plateau
  rw [max_eq_left (min_le_of_right_le (by linarith))]

theorem hasCompactSupport_plateau (a : ℝ) : HasCompactSupport (plateau a) :=
  HasCompactSupport.intro isCompact_Icc fun _ hu => plateau_eq_zero hu

/-- The cut-off character `u ↦ plateau_a(u) e^{iτu}`. -/
def cutChar (a τ : ℝ) : ℝ → ℂ := fun u => (plateau a u : ℂ) * cexp (I * τ * u)

theorem continuous_cutChar (a τ : ℝ) : Continuous (cutChar a τ) :=
  (continuous_ofReal.comp (continuous_plateau a)).mul (by fun_prop)

theorem hasCompactSupport_cutChar (a τ : ℝ) : HasCompactSupport (cutChar a τ) :=
  (hasCompactSupport_plateau a).comp_left Complex.ofReal_zero |>.mul_right

theorem memLp_two {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    MemLp g 2 (volume : Measure ℝ) :=
  hg.memLp_of_hasCompactSupport hgc

/-- The `L²` inner product of two `L²` representatives. -/
theorem inner_toLp {g h : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ))
    (hh : MemLp h 2 (volume : Measure ℝ)) :
    ⟪hg.toLp g, hh.toLp h⟫_ℂ = ∫ u, conj (g u) * h u := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp] with u hu1 hu2
  rw [hu1, hu2, RCLike.inner_apply]
  ring

theorem norm_toLp_sq {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    ‖hg.toLp g‖ ^ 2 = ∫ u, ‖g u‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_toLp]
  have h2 : ∫ u, conj (g u) * g u = ((∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext u
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [h2]
  exact Complex.ofReal_re _

/-- The cut-off character in `L²`. -/
def cutCharL2 (a τ : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_two (continuous_cutChar a τ) (hasCompactSupport_cutChar a τ)).toLp (cutChar a τ)

theorem norm_cutCharL2_sq_le {a : ℝ} (ha : 0 ≤ a) (τ : ℝ) : ‖cutCharL2 a τ‖ ^ 2 ≤ 2 * a + 2 := by
  rw [cutCharL2, norm_toLp_sq]
  have hpt : ∀ u, ‖cutChar a τ u‖ ^ 2 ≤
      (Icc (-(a + 1)) (a + 1)).indicator (fun _ => (1 : ℝ)) u := by
    intro u
    have hn : ‖cutChar a τ u‖ = plateau a u := by
      rw [cutChar, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (plateau_nonneg a u),
        show I * (τ : ℂ) * (u : ℂ) = ((τ * u : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [hn]
    by_cases hu : u ∈ Icc (-(a + 1)) (a + 1)
    · rw [indicator_of_mem hu]
      have h0 := plateau_nonneg a u
      have h1 := plateau_le_one a u
      nlinarith
    · rw [indicator_of_notMem hu, plateau_eq_zero hu]
      norm_num
  have hint2 : Integrable ((Icc (-(a + 1)) (a + 1)).indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp) (by simp))
  have hint1 : Integrable fun u => ‖cutChar a τ u‖ ^ 2 :=
    hint2.mono' ((continuous_cutChar a τ).norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hpt u)
  calc ∫ u, ‖cutChar a τ u‖ ^ 2
      ≤ ∫ u, (Icc (-(a + 1)) (a + 1)).indicator (fun _ => (1 : ℝ)) u :=
        integral_mono hint1 hint2 hpt
    _ = 2 * a + 2 := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
        Real.volume_real_Icc_of_le (by linarith)]
      ring

/-- The conjugate of the combination `Σ conj(x_i) f_i`, linear in `x`. -/
def conjCombo {n : ℕ} (f : Fin n → ℝ → ℂ) (x : Fin n → ℂ) : ℝ → ℂ :=
  fun u => ∑ i, x i * conj (f i u)

theorem continuous_conjCombo {n : ℕ} (f : Fin n → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (x : Fin n → ℂ) : Continuous (conjCombo f x) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul ((hf i).star)

theorem hasCompactSupport_conjCombo {n : ℕ} (f : Fin n → ℝ → ℂ)
    (hfc : ∀ i, HasCompactSupport (f i)) (x : Fin n → ℂ) : HasCompactSupport (conjCombo f x) := by
  have h : conjCombo f x = ∑ i, x i • fun u => conj (f i u) := by
    funext u
    simp [conjCombo]
  rw [h]
  exact hasCompactSupport_sum_smul _ (fun i => (hfc i).comp_left (map_zero _)) x

/-- The `L²` realization `x ↦ [conj(Σ conj(x_i) f_i)]` of a family of continuous compactly
supported tests, a `ℂ`-linear map. -/
def comboL2 {n : ℕ} (f : Fin n → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) : (Fin n → ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun x := (memLp_two (continuous_conjCombo f hf x) (hasCompactSupport_conjCombo f hfc x)).toLp
    (conjCombo f x)
  map_add' x y := by
    rw [← MemLp.toLp_add]
    refine (MemLp.toLp_eq_toLp_iff _ _).mpr (Eventually.of_forall fun u => ?_)
    simp [conjCombo, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine (MemLp.toLp_eq_toLp_iff _ _).mpr (Eventually.of_forall fun u => ?_)
    simp [conjCombo, Finset.mul_sum, mul_assoc]

theorem comboL2_apply {n : ℕ} (f : Fin n → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (x : Fin n → ℂ) :
    comboL2 f hf hfc x = (memLp_two (continuous_conjCombo f hf x)
      (hasCompactSupport_conjCombo f hfc x)).toLp (conjCombo f x) := rfl

theorem conj_conjCombo {n : ℕ} (f : Fin n → ℝ → ℂ) (x : Fin n → ℂ) (u : ℝ) :
    conj (conjCombo f x u) = (∑ i, conj (x i) • f i) u := by
  simp [conjCombo, map_sum, Finset.sum_apply]

theorem norm_comboL2_sq {n : ℕ} (f : Fin n → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (x : Fin n → ℂ) :
    ‖comboL2 f hf hfc x‖ ^ 2 = ∫ u, ‖(∑ i, conj (x i) • f i) u‖ ^ 2 := by
  rw [comboL2_apply, norm_toLp_sq]
  congr 1
  funext u
  rw [← conj_conjCombo, Complex.norm_conj]

/-- Against the cut-off character, the realization reads the transform of the combination. -/
theorem inner_comboL2_cutCharL2 {n : ℕ} {a : ℝ} (f : Fin n → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a)
    (x : Fin n → ℂ) (τ : ℝ) :
    ⟪comboL2 f hf hfc x, cutCharL2 a τ⟫_ℂ = paperFT (∑ i, conj (x i) • f i) τ := by
  rw [comboL2_apply, cutCharL2, inner_toLp, paperFT]
  congr 1
  funext u
  rw [conj_conjCombo, cutChar]
  by_cases hu : u ∈ Icc (-a) a
  · rw [plateau_eq_one hu]
    push_cast
    ring
  · have h0 : (∑ i, conj (x i) • f i) u = 0 := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : f i u = 0 := image_eq_zero_of_notMem_tsupport fun h => hu (hfs i h)
      rw [this, mul_zero]
    rw [h0, zero_mul, zero_mul]

/-! ### The count -/

/-- One linear condition costs at most one dimension. -/
theorem finrank_le_finrank_inf_ker_add_one {n : ℕ} (U : Submodule ℂ (Fin n → ℂ))
    (ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ) :
    Module.finrank ℂ U ≤ Module.finrank ℂ (U ⊓ LinearMap.ker ℓ : Submodule ℂ (Fin n → ℂ)) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker ℓ)
  have h2 : Module.finrank ℂ (U ⊔ LinearMap.ker ℓ : Submodule ℂ (Fin n → ℂ)) ≤ n := by
    simpa using Submodule.finrank_le (U ⊔ LinearMap.ker ℓ)
  have h3 := LinearMap.finrank_range_add_finrank_ker ℓ
  have h4 : Module.finrank ℂ (LinearMap.range ℓ) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range ℓ)
  have h5 : Module.finrank ℂ (Fin n → ℂ) = n := by simp
  omega

/-- A combination of tests supported in `[−a, a]` is supported in `[−a, a]`. -/
theorem tsupport_sum_smul_subset {n : ℕ} {a : ℝ} (f : Fin n → ℝ → ℂ)
    (hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a) (c : Fin n → ℂ) :
    tsupport (∑ i, c i • f i) ⊆ Icc (-a) a := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hu'
  apply hu
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [image_eq_zero_of_notMem_tsupport fun h => hu' (hfs i h), mul_zero]

/-- On the pole-free part of a negative subspace of the Weil Gram matrix, the `L²` realization
concentrates below the horizon. -/
theorem conc_comboL2 {a : ℝ} {n : ℕ} (f : Fin n → ℝ → ℂ) (hfd : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a)
    {x : Fin n → ℂ} (hp : evalFunctional f (I / 2) x = 0)
    (hneg : hermQuad (zeroGram zetaZeroConfig f) x < 0) :
    π * ‖comboL2 f (fun i => (hfd i).continuous) hfc x‖ ^ 2 <
      ∫ τ in (-horizonFreq a)..horizonFreq a,
        ‖⟪comboL2 f (fun i => (hfd i).continuous) hfc x, cutCharL2 a τ⟫_ℂ‖ ^ 2 := by
  have hfcont : ∀ i, Continuous (f i) := fun i => (hfd i).continuous
  have hFd : ContDiff ℝ 2 (∑ i, conj (x i) • f i) := contDiff_sum_smul f hfd _
  have hFs := tsupport_sum_smul_subset f hfs (fun i => conj (x i))
  have hpF : paperFT (∑ i, conj (x i) • f i) (I / 2) = 0 := by
    have h := evalFunctional_eq f hfcont hfc (I / 2) x
    rw [hp] at h
    exact (map_eq_zero (starRingEnd ℂ)).mp h.symm
  have hW : (zetaZeroConfig.W (∑ i, conj (x i) • f i) (∑ i, conj (x i) • f i)).re < 0 := by
    rw [← hermQuad_zeroGram_of_tempered zetaZeroConfig
      GaloisForLFunctions.SquareRootThreshold.temperedConfig_zetaZeroConfig f hfd hfc x]
    exact hneg
  have hconc := pi_mul_integral_lt_of_re_W_neg hFd hFs hpF hW
  have hint : ∫ τ in (-horizonFreq a)..horizonFreq a,
        ‖⟪comboL2 f hfcont hfc x, cutCharL2 a τ⟫_ℂ‖ ^ 2 =
      ∫ τ in (-horizonFreq a)..horizonFreq a, ‖paperFT (∑ i, conj (x i) • f i) τ‖ ^ 2 := by
    congr 1
    funext τ
    rw [inner_comboL2_cutCharL2 f hfcont hfc hfs x τ]
  rw [norm_comboL2_sq, hint]
  exact hconc

/-- **The Hodge defect of `ζ` at degree `a` is finite.** Every finite family of `C²` tests
supported in `[−a, a]`, `a ≥ 0`, has at most `1 + 2T(a)(2a + 2)/π` negative squares in its Weil
Gram matrix. -/
theorem negIndex_zeroGram_zeta_le {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (f : Fin n → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i) ∧ tsupport (f i) ⊆ Icc (-a) a) :
    (hermNegIndex (zeroGram zetaZeroConfig f) : ℝ) ≤ 1 + 2 * horizonFreq a * (2 * a + 2) / π := by
  have hfd : ∀ i, ContDiff ℝ 2 (f i) := fun i => (hf i).1
  have hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a := fun i => (hf i).2
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hfs i)
  have hfcont : ∀ i, Continuous (f i) := fun i => (hfd i).continuous
  obtain ⟨U, hUrank, hU⟩ := exists_isPosDefOn_finrank_eq_posIndex (-zeroGram zetaZeroConfig f)
  have hneg : ∀ x ∈ U, x ≠ 0 → hermQuad (zeroGram zetaZeroConfig f) x < 0 := fun x hx hx0 => by
    have h := hU x hx hx0
    rw [hermQuad_neg] at h
    linarith
  have hdim := finrank_le_finrank_inf_ker_add_one U (evalFunctional f (I / 2))
  have hcount : (Module.finrank ℂ (U ⊓ LinearMap.ker (evalFunctional f (I / 2)) :
      Submodule ℂ (Fin n → ℂ)) : ℝ) * π ≤ 2 * horizonFreq a * (2 * a + 2) := by
    refine finrank_mul_le_of_concentrated _ (comboL2 f hfcont hfc) (cutCharL2 a)
      (horizonFreq_nonneg a) (norm_cutCharL2_sq_le ha) (fun x _ => ?_)
      (fun x hx hx0 => conc_comboL2 f hfd hfc hfs hx.2 (hneg x hx.1 hx0))
    have h : (fun τ => ⟪comboL2 f hfcont hfc x, cutCharL2 a τ⟫_ℂ) =
        fun τ : ℝ => paperFT (∑ i, conj (x i) • f i) τ :=
      funext fun τ => inner_comboL2_cutCharL2 f hfcont hfc hfs x τ
    rw [h]
    exact RHTower.WeilOneSided.continuous_paperFT_real_arg
      ((contDiff_sum_smul f hfd _).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_sum_smul f hfc _))
  have hπ : 0 < π := Real.pi_pos
  have hle : (Module.finrank ℂ (U ⊓ LinearMap.ker (evalFunctional f (I / 2)) :
      Submodule ℂ (Fin n → ℂ)) : ℝ) ≤ 2 * horizonFreq a * (2 * a + 2) / π := by
    rw [le_div_iff₀ hπ]
    exact hcount
  have hk : hermNegIndex (zeroGram zetaZeroConfig f) = Module.finrank ℂ U := hUrank.symm
  have hcast : (hermNegIndex (zeroGram zetaZeroConfig f) : ℝ) ≤
      (Module.finrank ℂ (U ⊓ LinearMap.ker (evalFunctional f (I / 2)) :
        Submodule ℂ (Fin n → ℂ)) : ℝ) + 1 := by
    rw [hk]
    exact_mod_cast hdim
  linarith

/-- **The degree filtration of `ζ` is finite**: `hodgeDefectAt ζ a ≤ ⌊1 + 2T(a)(2a + 2)/π⌋`. -/
theorem hodgeDefectAt_zeta_le {a : ℝ} (ha : 0 ≤ a) :
    hodgeDefectAt zetaZeroConfig a ≤ (⌊1 + 2 * horizonFreq a * (2 * a + 2) / π⌋₊ : ℕ∞) :=
  iSup₂_le fun _ f => iSup_le fun hf =>
    ENat.coe_le_coe.mpr (Nat.le_floor (negIndex_zeroGram_zeta_le ha f hf))

/-- At every degree only finitely many right zeros of `ζ` are visible. -/
theorem hodgeDefectAt_zeta_lt_top (a : ℝ) : hodgeDefectAt zetaZeroConfig a < ⊤ := by
  have h0 : hodgeDefectAt zetaZeroConfig (max a 0) < ⊤ :=
    (hodgeDefectAt_zeta_le (le_max_right a 0)).trans_lt (ENat.coe_lt_top _)
  exact (hodgeDefectAt_mono zetaZeroConfig (le_max_left a 0)).trans_lt h0

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
