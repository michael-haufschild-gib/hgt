import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeIndexOfZetaHoldsAwayFromLowFrequencies
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheGenusIsTheApertureOfTheRadical

/-!
# The near radical of `ζ` is finite-dimensional; the radical of a curve is not

The near radical at level `a` is the space of `C²` tests supported in `[−a, a]`, with transform
vanishing at the pole, on which Weil's form is small: `Re W(f, f) ≤ ε‖f‖²`. The corpus constructs
near-radical spaces of dimension `≥ (2 − η)e^{2a}` with `ε` super-exponentially small
(`RHTower.zeta_weil_near_radical_sharp_count`); the upper half of the Landau–Widom law was open.

**Theorem** (`finrank_le_of_re_W_le`, `zeta_near_radical_finrank_le`). Unconditionally, every such
space has dimension at most `#D_{a,ε}`, the number of points of the low-frequency grid of the
`ε`-horizon `T_ε(a) = 4(e^{2E + 4πε} − 1)`, `E = 10 + 68e^a`. Above `T_ε(a)` the symbol `μ + P_X`
exceeds `E/2π + 2ε`, so a test with `Re W ≤ ε‖f‖²` keeps at least half its spectral mass below
the horizon (`pi_mul_integral_le_of_re_W_le`); a test whose transform vanishes on the grid has
band mass at most `‖f‖²` (`integral_band_le_of_lowGridOf`). The two are incompatible unless
`f = 0`, so the grid samples are injective on the near radical.

**Over `𝔽_q` the radical itself is infinite-dimensional.** On the scaling surface of a curve with
`d` distinct eigenvalues, beyond the genus aperture `d log q/2` there are numerically trivial
tests (`exists_radical_test_iff`), and their translates inside `[−a, a]` are linearly independent
(`linearIndependent_translate`), so the exact radical at aperture `a` has every finite dimension
(`curve_radical_finrank_ge`). Infinite genus over `ℤ` (no compact test is numerically trivial,
`InfiniteGenusLaw`) comes with finite near radicals at every level; finite genus over `𝔽_q` comes
with an infinite radical beyond the genus aperture.
-/

open Complex MeasureTheory Set Filter Zeta23 GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### The horizon at level `ε` -/

/-- The `ε`-horizon `T_ε(a) = 4(e^{2E + 4πε} − 1)`, `E = 10 + 68e^a`. -/
def horizonFreqEps (a ε : ℝ) : ℝ :=
  4 * (Real.exp (2 * RHTower.horizonExponent (Real.exp (2 * a)) + 4 * π * ε) - 1)

theorem horizonFreqEps_nonneg (a : ℝ) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ horizonFreqEps a ε := by
  have hE := RHTower.horizonExponent_pos (Real.exp (2 * a))
  have h : 1 ≤ Real.exp (2 * RHTower.horizonExponent (Real.exp (2 * a)) + 4 * π * ε) :=
    Real.one_le_exp (by positivity)
  unfold horizonFreqEps
  linarith

/-- The symbol dominates the step `((E + 4πε) − (2E + 4πε)·1_{[−T_ε, T_ε]})/2π`. -/
theorem stepEps_le_mu_add_PX (a : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (τ : ℝ) :
    ((RHTower.horizonExponent (Real.exp (2 * a)) + 4 * π * ε) -
        (2 * RHTower.horizonExponent (Real.exp (2 * a)) + 4 * π * ε) *
          (Icc (-horizonFreqEps a ε) (horizonFreqEps a ε)).indicator (fun _ => (1 : ℝ)) τ) /
        (2 * π) ≤
      mu τ + PX (Real.exp (2 * a)) τ := by
  set E := RHTower.horizonExponent (Real.exp (2 * a)) with hEdef
  have hT := horizonFreqEps_nonneg a hε
  refine le_trans ?_ (RHTower.mu_add_PX_ge (Real.exp_pos _).le τ)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  by_cases hτ : τ ∈ Icc (-horizonFreqEps a ε) (horizonFreqEps a ε)
  · rw [indicator_of_mem hτ]
    have : 0 ≤ Real.log (1 + |τ| / 4) :=
      Real.log_nonneg (by have := abs_nonneg τ; linarith)
    linarith
  · rw [indicator_of_notMem hτ]
    have hTτ : horizonFreqEps a ε < |τ| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hτ
      rcases hτ with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hlog : 2 * E + 4 * π * ε < Real.log (1 + |τ| / 4) := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      unfold horizonFreqEps at hTτ
      rw [← hEdef] at hTτ
      linarith
    linarith

/-- **Small Weil energy lives below the `ε`-horizon.** If `F ∈ C²` is supported in `[−a, a]`,
`h_F(i/2) = 0` and `Re W_ζ(F, F) ≤ ε‖F‖²` with `ε ≥ 0`, then `π‖F‖² ≤ ∫_{−T_ε}^{T_ε} |h_F|²`. -/
theorem pi_mul_integral_le_of_re_W_le {a ε : ℝ} (hε : 0 ≤ ε) {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hFs : tsupport F ⊆ Icc (-a) a) (hp : paperFT F (I / 2) = 0)
    (hW : (zetaZeroConfig.W F F).re ≤ ε * ∫ u, ‖F u‖ ^ 2) :
    π * ∫ u, ‖F u‖ ^ 2 ≤
      ∫ τ in (-horizonFreqEps a ε)..horizonFreqEps a ε, ‖paperFT F τ‖ ^ 2 := by
  have hFc : HasCompactSupport F :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport F) hFs
  set E := RHTower.horizonExponent (Real.exp (2 * a)) with hEdef
  set T := horizonFreqEps a ε with hTdef
  have hE : 0 < E := RHTower.horizonExponent_pos _
  have hT : 0 ≤ T := horizonFreqEps_nonneg a hε
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
  set cO := (E + 4 * π * ε) / (2 * π) with hcO
  set cI := (2 * E + 4 * π * ε) / (2 * π) with hcI
  set s : ℝ → ℝ := fun τ => cO * N τ - cI * (Icc (-T) T).indicator N τ with hsdef
  have hs_int : Integrable s := (hN.const_mul _).sub (hNi.const_mul _)
  have hpt : ∀ τ, s τ ≤ g τ := by
    intro τ
    have hstep := stepEps_le_mu_add_PX a hε τ
    rw [← hEdef, ← hTdef] at hstep
    have hN0 : 0 ≤ N τ := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hstep hN0
    by_cases hτ : τ ∈ Icc (-T) T
    · rw [indicator_of_mem hτ] at hmul
      simp only [hsdef, hgdef, indicator_of_mem hτ]
      have : N τ * ((E + 4 * π * ε - (2 * E + 4 * π * ε) * 1) / (2 * π)) = cO * N τ - cI * N τ := by
        rw [hcO, hcI]
        ring
      linarith
    · rw [indicator_of_notMem hτ] at hmul
      simp only [hsdef, hgdef, indicator_of_notMem hτ]
      have : N τ * ((E + 4 * π * ε - (2 * E + 4 * π * ε) * 0) / (2 * π)) = cO * N τ - cI * 0 := by
        rw [hcO, hcI]
        ring
      linarith
  have hle : ∫ τ, s τ ≤ ∫ τ, g τ := integral_mono hs_int hg_int hpt
  have hplan : ∫ τ, N τ = 2 * π * ∫ u, ‖F u‖ ^ 2 := RHTower.integral_norm_sq_paperFT_eq hF hFs
  have hind : ∫ τ, (Icc (-T) T).indicator N τ = ∫ τ in (-T)..T, N τ := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      integral_indicator measurableSet_Icc]
  have hs_eq : ∫ τ, s τ = cO * (2 * π * ∫ u, ‖F u‖ ^ 2) - cI * ∫ τ in (-T)..T, N τ := by
    rw [hsdef, integral_sub (hN.const_mul _) (hNi.const_mul _), integral_const_mul,
      integral_const_mul, hplan, hind]
  set A := ∫ u, ‖F u‖ ^ 2 with hA
  set J := ∫ τ in (-T)..T, N τ with hJ
  have hA0 : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hπ : 0 < π := Real.pi_pos
  have hkey : (E + 4 * π * ε) * A - (2 * E + 4 * π * ε) / (2 * π) * J ≤ ε * A := by
    have h1 : cO * (2 * π * A) = (E + 4 * π * ε) * A := by
      rw [hcO]
      field_simp
    rw [← h1, ← hcI, ← hs_eq]
    linarith
  by_contra hlt
  push Not at hlt
  have hcI_pos : 0 < (2 * E + 4 * π * ε) / (2 * π) := by positivity
  have h2 : (2 * E + 4 * π * ε) / (2 * π) * J < (2 * E + 4 * π * ε) / (2 * π) * (π * A) :=
    mul_lt_mul_of_pos_left hlt hcI_pos
  have h3 : (2 * E + 4 * π * ε) / (2 * π) * (π * A) = (E + 2 * π * ε) * A := by
    field_simp
    ring
  have h4 : 0 ≤ (2 * π - 1) * ε * A := by
    have : 0 ≤ 2 * π - 1 := by linarith [Real.pi_gt_three]
    positivity
  nlinarith

/-! ### The near radical -/

/-- **The near radical of `ζ` is finite-dimensional.** A finite-dimensional space of `C²` tests
supported in `[−a, a]`, with transform vanishing at `i/2` and `Re W_ζ(f, f) ≤ ε‖f‖²` for all its
elements, has dimension at most the number of points of the grid of the `ε`-horizon. -/
theorem finrank_le_of_re_W_le {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) (V : Submodule ℂ (ℝ → ℂ))
    [FiniteDimensional ℂ V]
    (hV : ∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0)
    (hW : ∀ f ∈ V, (zetaZeroConfig.W f f).re ≤ ε * ∫ u, ‖f u‖ ^ 2) :
    Module.finrank ℂ V ≤ (lowGridOf (horizonFreqEps a ε) a).card := by
  set T := horizonFreqEps a ε with hT
  set G := lowGridOf T a with hG
  have hcomp : ∀ f ∈ V, Continuous f ∧ HasCompactSupport f := fun f hf =>
    ⟨(hV f hf).1.continuous,
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) (hV f hf).2.1⟩
  let Φ : V →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f j => paperFT (f : ℝ → ℂ) (((j : ℤ) : ℝ) * gridStepOf T a : ℝ)
      map_add' := fun f g => by
        funext j
        simp only [Submodule.coe_add, Pi.add_apply]
        exact paperFT_add (hcomp f f.2).1 (hcomp f f.2).2 (hcomp g g.2).1 (hcomp g g.2).2 _
      map_smul' := fun c f => by
        funext j
        simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        exact paperFT_smul c _ _ }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    obtain ⟨hfd, hfs, hfp⟩ := hV f f.2
    obtain ⟨hfcont, hfc⟩ := hcomp f f.2
    have hgrid : ∀ j ∈ G, paperFT (f : ℝ → ℂ) (((j : ℝ) * gridStepOf T a : ℝ) : ℂ) = 0 :=
      fun j hj => congrFun hf ⟨j, hj⟩
    have hlow := pi_mul_integral_le_of_re_W_le hε hfd hfs hfp (hW f f.2)
    have hband := integral_band_le_of_lowGridOf (horizonFreqEps_nonneg a hε) ha hfcont hfc hfs
      hgrid
    have hA0 : 0 ≤ ∫ u, ‖(f : ℝ → ℂ) u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hA : ∫ u, ‖(f : ℝ → ℂ) u‖ ^ 2 = 0 := by
      have := Real.pi_gt_three
      nlinarith
    have hint : Integrable fun u => ‖(f : ℝ → ℂ) u‖ ^ 2 := by
      have h : Integrable fun u => ‖(f : ℝ → ℂ) u‖ * ‖(f : ℝ → ℂ) u‖ :=
        (hfcont.norm.mul hfcont.norm).integrable_of_hasCompactSupport hfc.norm.mul_right
      simpa only [← pow_two] using h
    have hae := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) hint).mp hA
    have hzero : (fun u => ‖(f : ℝ → ℂ) u‖ ^ 2) = 0 :=
      (Continuous.ae_eq_iff_eq volume (hfcont.norm.pow 2) continuous_const).mp hae
    ext u
    have := congrFun hzero u
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      norm_eq_zero] at this
    simp [this]
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h

/-- The near radical in the normalization of `RHTower.zeta_weil_near_radical_sharp_count`
(`|W(f, f)| ≤ δ‖f‖²`, both poles removed) has dimension at most `#D_{a,δ}`. -/
theorem zeta_near_radical_finrank_le {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (V : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0)
    (hW : ∀ f ∈ V, ‖zetaZeroConfig.W f f‖ ≤ δ * ∫ u, ‖f u‖ ^ 2) :
    Module.finrank ℂ V ≤ (lowGridOf (horizonFreqEps L δ) L).card :=
  finrank_le_of_re_W_le hL hδ V (fun f hf => ⟨(hV f hf).1, (hV f hf).2.1, (hV f hf).2.2.1⟩)
    fun f hf => (Complex.re_le_norm _).trans (hW f hf)

/-! ### Over `𝔽_q`: the radical of a curve is infinite-dimensional -/

/-- **Distinct translates of a nonzero compactly supported function are linearly independent**:
evaluate a vanishing combination just inside the right end of the support of the rightmost
translate with a nonzero coefficient. -/
theorem linearIndependent_translate {N : ℕ} {s : Fin N → ℝ} (hs : Function.Injective s)
    {g : ℝ → ℂ} (hgc : HasCompactSupport g) (hg0 : g ≠ 0) :
    LinearIndependent ℂ fun i => translate (s i) g := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  set S := Finset.univ.filter fun i => c i ≠ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [hS, hi]⟩
  obtain ⟨i₀, hi₀S, hi₀max⟩ := Finset.exists_max_image S s hSne
  have hc₀ : c i₀ ≠ 0 := by simpa [hS] using hi₀S
  -- a positive gap below `s i₀` among the other indices of `S`
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ i ∈ S, i ≠ i₀ → δ ≤ s i₀ - s i := by
    by_cases hE : (S.erase i₀).Nonempty
    · obtain ⟨i₁, hi₁, hi₁min⟩ := Finset.exists_min_image (S.erase i₀) (fun i => s i₀ - s i) hE
      refine ⟨s i₀ - s i₁, ?_, fun i hi hne => hi₁min i (Finset.mem_erase.mpr ⟨hne, hi⟩)⟩
      have hne₁ : i₁ ≠ i₀ := (Finset.mem_erase.mp hi₁).1
      have hle := hi₀max i₁ (Finset.mem_erase.mp hi₁).2
      have hneq : s i₁ ≠ s i₀ := fun h => hne₁ (hs h)
      have : s i₁ < s i₀ := lt_of_le_of_ne hle hneq
      linarith
    · refine ⟨1, one_pos, fun i hi hne => ?_⟩
      exact absurd ⟨i, Finset.mem_erase.mpr ⟨hne, hi⟩⟩ hE
  -- the right end of the support
  have hsupp : (tsupport g).Nonempty := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hg0
    exact ⟨x, subset_tsupport g hx⟩
  obtain ⟨b, hbmem, hbmax⟩ := hgc.isCompact.exists_isGreatest hsupp
  obtain ⟨x, hxsupp, hxb⟩ : ∃ x ∈ Function.support g, b - δ < x := by
    have hcl : b ∈ closure (Function.support g) := hbmem
    obtain ⟨x, hx1, hx2⟩ := Metric.mem_closure_iff.mp hcl δ hδ
    refine ⟨x, hx1, ?_⟩
    rw [Real.dist_eq] at hx2
    have := le_abs_self (b - x)
    linarith
  have hval := congrFun hc (x + s i₀)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, translate] at hval
  rw [Finset.sum_eq_single i₀] at hval
  · rw [add_sub_cancel_right] at hval
    exact hxsupp ((mul_eq_zero.mp hval).resolve_left hc₀)
  · intro i _ hne
    by_cases hci : c i = 0
    · rw [hci, zero_mul]
    · have hiS : i ∈ S := by simp [hS, hci]
      have hgap := hδle i hiS hne
      have hout : b < x + s i₀ - s i := by linarith
      have hnot : x + s i₀ - s i ∉ tsupport g := fun h => by
        have := hbmax h
        linarith
      rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- **The radical of a curve is infinite-dimensional beyond the genus aperture.** For
`a > d log q/2` and every `N` there is an `N`-dimensional space of `C²` tests supported in
`[−a, a]` that are numerically trivial on the scaling surface of the curve. -/
theorem curve_radical_finrank_ge {a : ℝ} (ha : D.spectrum.card * Real.log D.q / 2 < a) (N : ℕ) :
    ∃ V : Submodule ℂ (ℝ → ℂ), N ≤ Module.finrank ℂ V ∧
      ∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ ∀ g, (D.curveConfig hD).W f g = 0 := by
  classical
  set a' := (a + D.spectrum.card * Real.log D.q / 2) / 2 with ha'
  have ha'1 : D.spectrum.card * Real.log D.q / 2 < a' := by rw [ha']; linarith
  have ha'2 : a' < a := by rw [ha']; linarith
  obtain ⟨f₀, hf₀d, hf₀s, hf₀0, hf₀v⟩ := (D.exists_radical_test_iff hD a').mpr ha'1
  have hf₀c : HasCompactSupport f₀ :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f₀) hf₀s
  set s : Fin N → ℝ := fun i => (i : ℝ) * ((a - a') / (N + 1)) with hsdef
  have hstep : 0 < (a - a') / (N + 1) := div_pos (by linarith) (by positivity)
  have hsinj : Function.Injective s := by
    intro i j hij
    simp only [hsdef] at hij
    exact Fin.ext (by exact_mod_cast mul_right_cancel₀ hstep.ne' hij)
  have hs_mem : ∀ i, 0 ≤ s i ∧ s i ≤ a - a' := by
    intro i
    refine ⟨by positivity, ?_⟩
    have hi : (i : ℝ) ≤ N + 1 := by
      have := i.isLt
      have : (i : ℝ) < N := by exact_mod_cast this
      linarith
    calc s i = (i : ℝ) * ((a - a') / (N + 1)) := rfl
      _ ≤ (N + 1) * ((a - a') / (N + 1)) := mul_le_mul_of_nonneg_right hi hstep.le
      _ = a - a' := by field_simp
  set v : Fin N → ℝ → ℂ := fun i => translate (s i) f₀ with hv
  have hvd : ∀ i, ContDiff ℝ 2 (v i) := fun i =>
    hf₀d.comp (contDiff_id.sub contDiff_const)
  have hvs : ∀ i, tsupport (v i) ⊆ Icc (-a) a := by
    intro i
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have hu' : u - s i ∈ tsupport f₀ := subset_tsupport f₀ hu
    have h1 := hf₀s hu'
    obtain ⟨hs0, hs1⟩ := hs_mem i
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hvc : ∀ i, HasCompactSupport (v i) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hvs i)
  have hli : LinearIndependent ℂ v := linearIndependent_translate hsinj hf₀c hf₀0
  refine ⟨Submodule.span ℂ (Set.range v), ?_, fun f hf => ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
    refine ⟨contDiff_sum_smul v hvd c, tsupport_sum_smul_subset v hvs c, fun g => ?_⟩
    have hzero : ∀ ρ : (D.curveConfig hD).carrier,
        paperFT (∑ i, c i • v i) (gammaOf ρ) = 0 := by
      intro ρ
      rw [paperFT_sum_smul v (fun i => (hvd i).continuous) hvc]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hv, paperFT_translate, hf₀v ρ ρ.2, mul_zero, mul_zero]
    rw [ZeroConfig.W]
    refine (tsum_congr fun ρ => ?_).trans tsum_zero
    rw [ZeroConfig.Wsummand, hzero ρ, mul_zero, zero_mul]

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
