import GaloisForLFunctions.BiScaleUncertainty.BandSpectrumZeroWidthLaw
import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization
import GaloisForLFunctions.RHTower.CriticalChebyshevBoostChargeInjection
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszMarkovTransform
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling
import GaloisForLFunctions.RHTower.LiouvilleHyperbolaCutoffWide

/-!
# The band slope bounds the zero energy

Suppose the mean-square band is linear, `∫_0^L Ẽ² ≤ C(1 + L) + K`. Then for every finite set of
critical ordinates `γ_k` with orders `n_k` of `(s − 1)ζ(s)` at `ρ_k = 1/2 + iγ_k`,

`Σ_k n_k² / |ρ_k|² ≤ C`.

So the slope of the band is at least the zero energy `Σ_ρ m_ρ²/|ρ|²`, and every zero has
multiplicity at most `√C |ρ|`. This is the quantitative form of "band ⟹ RH".

Mechanism: Abel means against critical characters.
* A zero width `β` gives `|Ẽ(t)| ≤ C_ε e^{(β+ε)t}`, so the Laplace transform
  `L(z) = ∫_0^∞ e^{-zt} Ẽ(t) dt` is holomorphic on `Re z > β`, where it equals the continuation
  `−((ζ_u'/ζ_u)(z + 1/2) + 1)/(z + 1/2)`, `ζ_u(s) = (s − 1)ζ(s)`.
* The logarithmic residue gives the Abel coefficient `σ L(β + σ + iγ) → −n/ρ` as `σ → 0⁺` at a
  point `ρ = 1/2 + β + iγ` of order `n`.
* Integration by parts against the primitive of `Ẽ²` turns a bound on the band into a bound on
  the Abel energy `σ ∫_0^∞ e^{-σt} Ẽ²`.
* The characters `e^{-iγ_k t}` are Abel-orthonormal: `σ ∫_0^∞ e^{-σt} e^{-iΔt} dt = σ/(σ + iΔ)`
  tends to `1` for `Δ = 0` and to `0` otherwise. The pointwise inequality `2|ab| ≤ a² + |b|²`
  against `φ = Σ_k conj(c_k) e^{-iγ_k t}` then gives Bessel's inequality for Abel coefficients
  (`sum_norm_sq_le_of_abel`).
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar

noncomputable section
set_option autoImplicit false

/-! ## The Laplace transform of `Ẽ` -/

/-- `L(z) = ∫_0^∞ e^{-zt} Ẽ(t) dt` in the field's normalization. -/
theorem criticalNormalizedChebyshevErrorLaplace_eq (z : ℂ) :
    _root_.RHTower.criticalNormalizedChebyshevErrorLaplace z =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * t)) * (normalizedLogError t : ℂ) := by
  rw [_root_.RHTower.criticalNormalizedChebyshevErrorLaplace]
  simp only [criticalMellinNormalizedChebyshevError_eq_normalizedLogError]

/-- Tilting by `e^{-εt}` and shifting the half-line by one exhibit `L` as an Abel tail. -/
theorem laplace_eq_tilted_tail (ε : ℝ) (z : ℂ) :
    _root_.RHTower.criticalNormalizedChebyshevErrorLaplace z =
      Complex.exp (z - ε) * _root_.RHTower.ccmAbelLaplaceTail
        (fun h => Real.exp (-(ε * (h - 1))) * normalizedLogError (h - 1)) 1 (z - ε) := by
  rw [criticalNormalizedChebyshevErrorLaplace_eq, _root_.RHTower.ccmAbelLaplaceTail,
    ← GaloisForLFunctions.RHTower.integral_Ioi_translate 1, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [add_sub_cancel_left]
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  have hexp : Complex.exp (z - ε) * (Complex.exp (-(z - ε) * ((1 + u : ℝ) : ℂ)) *
      Complex.exp ((-(ε * u) : ℝ) : ℂ)) = Complex.exp (-(z * u)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [← hexp]; ring

/-- Exponential bounds `|Ẽ(t)| ≤ B_ε e^{(β+ε)t}` make `L` holomorphic on `Re z > β`. -/
theorem analyticOnNhd_laplace_of_bound {β : ℝ}
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      |normalizedLogError t| ≤ B * Real.exp ((β + ε) * t)) :
    AnalyticOnNhd ℂ _root_.RHTower.criticalNormalizedChebyshevErrorLaplace {z | β < z.re} := by
  intro z₀ hz₀
  change β < z₀.re at hz₀
  set δ := (z₀.re - β) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨B, hB0, hB⟩ := hbound δ hδ0
  set κ := β + δ
  set q : ℝ → ℝ := fun h => Real.exp (-(κ * (h - 1))) * normalizedLogError (h - 1)
  have hq : Measurable q :=
    (Real.measurable_exp.comp ((measurable_id.sub_const 1).const_mul κ).neg).mul
      (measurable_normalizedLogError.comp (measurable_id.sub_const 1))
  have hqB : ∀ h : ℝ, 1 < h → |q h| ≤ B := by
    intro h hh
    simp only [q]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(κ * (h - 1))) * |normalizedLogError (h - 1)|
        ≤ Real.exp (-(κ * (h - 1))) * (B * Real.exp (κ * (h - 1))) :=
          mul_le_mul_of_nonneg_left (hB (h - 1) (by linarith)) (Real.exp_pos _).le
      _ = B := by
          rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hT := _root_.RHTower.analyticOnNhd_ccmAbelLaplaceTail_of_bounded hq one_pos hB0 hqB
  rw [show _root_.RHTower.criticalNormalizedChebyshevErrorLaplace = fun z =>
      Complex.exp (z - κ) * _root_.RHTower.ccmAbelLaplaceTail q 1 (z - κ) from
    funext (laplace_eq_tilted_tail κ)]
  have hshift : AnalyticAt ℂ (fun z : ℂ => z - κ) z₀ := by fun_prop
  have hTz : AnalyticAt ℂ (_root_.RHTower.ccmAbelLaplaceTail q 1) (z₀ - κ) :=
    hT _ (by change 0 < (z₀ - κ).re; simp only [Complex.sub_re, Complex.ofReal_re]; linarith)
  exact hshift.cexp.mul (AnalyticAt.comp (f := fun z : ℂ => z - κ) hTz hshift)

/-- A zero width `β` keeps `(s − 1)ζ(s)` free of zeros on `Re s > 1/2 + β`. -/
theorem zetaResidueUnit_ne_zero_of_halfPlane {β : ℝ} (hβ : 0 ≤ β)
    (hXi : _root_.RHTower.XiZeroHalfPlaneBound β) {s : ℂ} (hs : 1 / 2 + β < s.re) :
    _root_.RHTower.zetaResidueUnit s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1; simp
  · rw [_root_.RHTower.zetaResidueUnit, Function.update_of_ne h1]
    refine mul_ne_zero (sub_ne_zero.mpr h1) fun hz => ?_
    by_cases hre : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re hre hz
    · have := hXi s (_root_.RHTower.LiouvilleHyperbolaCutoffWide.xi_eq_zero_of_riemannZeta_eq_zero hz (by linarith))
      linarith

/-- With zero width `β` the continuation is holomorphic on `Re z > β`. -/
theorem analyticOnNhd_continuation_of_halfPlane {β : ℝ} (hβ : 0 ≤ β)
    (hXi : _root_.RHTower.XiZeroHalfPlaneBound β) :
    AnalyticOnNhd ℂ _root_.RHTower.criticalNormalizedChebyshevErrorContinuation
      {z | β < z.re} := by
  intro z hz
  change β < z.re at hz
  have hs : 1 / 2 + β < (z + 1 / 2).re := by simp; linarith
  have hu := RHTower.Sieve.zetaResidueUnit_analyticOnNhd_univ
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) z := by fun_prop
  have hζ : AnalyticAt ℂ _root_.RHTower.zetaResidueUnit (z + 1 / 2) := hu _ (mem_univ _)
  have hζ' : AnalyticAt ℂ (deriv _root_.RHTower.zetaResidueUnit) (z + 1 / 2) := hζ.deriv
  have hne := zetaResidueUnit_ne_zero_of_halfPlane hβ hXi hs
  have hlog : AnalyticAt ℂ (fun w : ℂ => logDeriv _root_.RHTower.zetaResidueUnit (w + 1 / 2)) z := by
    simp only [logDeriv_apply]
    exact (AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) hζ' hshift).div
      (AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) hζ hshift) hne
  have hz0 : z + 1 / 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  unfold _root_.RHTower.criticalNormalizedChebyshevErrorContinuation
  exact ((hlog.add analyticAt_const).neg).div hshift hz0

/-- **Laplace transform = continuation** on `Re z > β` under zero width `β < 1/2`. -/
theorem laplace_eq_continuation_of_halfPlane {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1 / 2)
    (hXi : _root_.RHTower.XiZeroHalfPlaneBound β) {z : ℂ} (hz : β < z.re) :
    _root_.RHTower.criticalNormalizedChebyshevErrorLaplace z =
      _root_.RHTower.criticalNormalizedChebyshevErrorContinuation z := by
  have hbound : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      |normalizedLogError t| ≤ B * Real.exp ((β + ε) * t) := fun ε hε =>
    exists_abs_normalizedLogError_le_of_xiZeroHalfPlaneBound hβ (by linarith) hXi
  have hU : IsPreconnected {w : ℂ | β < w.re} := (convex_halfSpace_re_gt β).isPreconnected
  have hevent : _root_.RHTower.criticalNormalizedChebyshevErrorLaplace =ᶠ[𝓝 (1 : ℂ)]
      _root_.RHTower.criticalNormalizedChebyshevErrorContinuation := by
    have hopen : IsOpen {w : ℂ | 1 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num)] with w hw
    exact (_root_.RHTower.criticalNormalizedChebyshevErrorContinuation_eq_laplace hw).symm
  exact (analyticOnNhd_laplace_of_bound hbound).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_continuation_of_halfPlane hβ hXi) hU
    (show β < (1 : ℂ).re by simp; linarith) hevent hz

/-- **Abel coefficient on the extremal line.** Under zero width `β < 1/2`, if `(s − 1)ζ(s)` has
order `n` at `ρ = 1/2 + β + iγ`, then `σ L(β + σ + iγ) → −n/ρ` as `σ → 0⁺`. -/
theorem tendsto_abel_laplace_of_halfPlane {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1 / 2)
    (hXi : _root_.RHTower.XiZeroHalfPlaneBound β) {γ : ℝ} {n : ℤ}
    (horder : meromorphicOrderAt _root_.RHTower.zetaResidueUnit
      (((1 / 2 + β : ℝ) : ℂ) + γ * I) = n) :
    Tendsto (fun σ : ℝ => (σ : ℂ) *
        _root_.RHTower.criticalNormalizedChebyshevErrorLaplace (((β + σ : ℝ) : ℂ) + γ * I))
      (𝓝[>] 0) (𝓝 (-(n : ℂ) / (((1 / 2 + β : ℝ) : ℂ) + γ * I))) := by
  set ρ : ℂ := ((1 / 2 + β : ℝ) : ℂ) + γ * I with hρ
  have hρre : ρ.re = 1 / 2 + β := by simp [hρ]
  have hρ0 : ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h; rw [hρre] at this; simp at this; linarith
  have hmero : MeromorphicAt _root_.RHTower.zetaResidueUnit ρ :=
    (RHTower.Sieve.zetaResidueUnit_analyticOnNhd_univ ρ (mem_univ _)).meromorphicAt
  have hres := GaloisForLFunctions.HTGeometry.logDeriv_residue_of_meromorphicOrder hmero horder
  have hpath : Tendsto (fun σ : ℝ => ρ + (σ : ℂ)) (𝓝[>] 0) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun σ : ℝ => ρ + (σ : ℂ)) (𝓝 0) (𝓝 (ρ + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      change ρ + (σ : ℂ) ≠ ρ
      intro h
      have : (σ : ℂ) = 0 := by linear_combination h
      exact (ne_of_gt (show (0 : ℝ) < σ from hσ)) (by exact_mod_cast this)
  have h1 : Tendsto (fun σ : ℝ => (σ : ℂ) * logDeriv _root_.RHTower.zetaResidueUnit (ρ + σ))
      (𝓝[>] 0) (𝓝 (n : ℂ)) := by
    have := hres.comp hpath
    refine this.congr fun σ => ?_
    simp only [Function.comp_apply, add_sub_cancel_left]
  have h2 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have h3 : Tendsto (fun σ : ℝ => ρ + (σ : ℂ)) (𝓝[>] 0) (𝓝 ρ) := hpath.mono_right nhdsWithin_le_nhds
  have hlim := ((h1.add h2).neg).div h3 hρ0
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  change (0 : ℝ) < σ at hσ
  simp only [Pi.div_apply]
  have hz : β < (((β + σ : ℝ) : ℂ) + γ * I).re := by simp; linarith
  rw [laplace_eq_continuation_of_halfPlane hβ hβ1 hXi hz,
    _root_.RHTower.criticalNormalizedChebyshevErrorContinuation,
    show ((β + σ : ℝ) : ℂ) + γ * I + 1 / 2 = ρ + σ by rw [hρ]; push_cast; ring]
  have hne : ρ + (σ : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; linarith
  field_simp

/-! ## Abel energy from the band -/

/-- **Integration by parts against the primitive of `F²`.** If `∫_0^T F² ≤ g(T)` for every
`T ≥ 0` and `e^{-aR} g(R) + a ∫_0^R e^{-aT} g(T) dT ≤ M` for every `R ≥ 0`, then
`∫_0^∞ e^{-at} F² ≤ M`. -/
theorem abel_integral_le_of_primitive {F : ℝ → ℝ} (hFm : Measurable F)
    (hF2 : ∀ T : ℝ, IntegrableOn (fun t => F t ^ 2) (Icc 0 T))
    {a M : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : Continuous g)
    (hB : ∀ T : ℝ, 0 ≤ T → ∫ t in Icc 0 T, F t ^ 2 ≤ g T)
    (hM : ∀ R : ℝ, 0 ≤ R →
      Real.exp (-a * R) * g R + a * ∫ T in (0 : ℝ)..R, Real.exp (-a * T) * g T ≤ M) :
    IntegrableOn (fun t => Real.exp (-a * t) * F t ^ 2) (Ioi 0) ∧
      ∫ t in Ioi 0, Real.exp (-a * t) * F t ^ 2 ≤ M := by
  set B : ℝ → ℝ := fun T => ∫ t in (0 : ℝ)..T, F t ^ 2 with hBdef
  have hsqI : ∀ R : ℝ, 0 ≤ R →
      IntervalIntegrable (fun t => F t ^ 2) volume 0 R := fun R hR => by
    refine IntegrableOn.intervalIntegrable ?_
    rw [uIcc_of_le hR]
    exact hF2 R
  have hBg : ∀ T : ℝ, 0 ≤ T → B T ≤ g T := fun T hT => by
    simp only [B]
    rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
    exact hB T hT
  have hd : ∀ t : ℝ, HasDerivAt (fun T : ℝ => Real.exp (-a * T)) (Real.exp (-a * t) * -a) t :=
    fun t => by simpa using ((hasDerivAt_id t).const_mul (-a)).exp
  have hparts : ∀ R : ℝ, 0 ≤ R →
      ∫ T in (0 : ℝ)..R, Real.exp (-a * T) * F T ^ 2 =
        Real.exp (-a * R) * B R + a * ∫ T in (0 : ℝ)..R, Real.exp (-a * T) * B T := by
    intro R hR
    have hi := hsqI R hR
    have hBac : AbsolutelyContinuousOnInterval B 0 R :=
      hi.absolutelyContinuousOnInterval_intervalIntegral (by simp [hR])
    have hEac : AbsolutelyContinuousOnInterval (fun T : ℝ => Real.exp (-a * T)) 0 R :=
      (by fun_prop : ContDiff ℝ 1 (fun T : ℝ => Real.exp (-a * T))).contDiffOn.absolutelyContinuousOnInterval
    have h := hEac.integral_mul_deriv_eq_deriv_mul hBac
    have hleft : ∫ t in (0 : ℝ)..R, Real.exp (-a * t) * deriv B t =
        ∫ t in (0 : ℝ)..R, Real.exp (-a * t) * F t ^ 2 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
      rw [(ht (uIoc_subset_uIcc hmem) 0 (by simp [hR])).deriv]
    have hright : ∫ t in (0 : ℝ)..R, deriv (fun T : ℝ => Real.exp (-a * T)) t * B t =
        -a * ∫ t in (0 : ℝ)..R, Real.exp (-a * t) * B t := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [(hd t).deriv]; ring
    have hB0 : B 0 = 0 := by simp [B]
    rw [hleft, hright, hB0, mul_zero, sub_zero] at h
    rw [h]; ring
  have hbound : ∀ R : ℝ, 0 ≤ R →
      ∫ T in (0 : ℝ)..R, Real.exp (-a * T) * F T ^ 2 ≤ M := by
    intro R hR
    rw [hparts R hR]
    have hBc : ContinuousOn B (uIcc 0 R) :=
      intervalIntegral.continuousOn_primitive_interval (μ := volume)
        (f := fun t => F t ^ 2) (a := 0) (b := R)
        (by rw [uIcc_of_le hR]; exact hF2 R)
    have hmono : ∫ T in (0 : ℝ)..R, Real.exp (-a * T) * B T ≤
        ∫ T in (0 : ℝ)..R, Real.exp (-a * T) * g T := by
      refine intervalIntegral.integral_mono_on hR
        (((by fun_prop : Continuous fun T : ℝ => Real.exp (-a * T)).continuousOn.mul
          hBc).intervalIntegrable)
        (((by fun_prop : Continuous fun T : ℝ => Real.exp (-a * T)).mul hg).intervalIntegrable
          _ _) fun T hT => ?_
      exact mul_le_mul_of_nonneg_left (hBg T hT.1) (Real.exp_pos _).le
    have hBR := mul_le_mul_of_nonneg_left (hBg R hR) (Real.exp_pos (-a * R)).le
    nlinarith [mul_le_mul_of_nonneg_left hmono ha.le, hM R hR]
  have hnn : ∀ t, 0 ≤ Real.exp (-a * t) * F t ^ 2 :=
    fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hloc : ∀ i : ℝ, IntegrableOn (fun t => Real.exp (-a * t) * F t ^ 2)
      (Ioc 0 i) := by
    intro i
    refine ((hF2 i).mono_set Ioc_subset_Icc_self).mono'
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-a * t)).aestronglyMeasurable.mul
        (hFm.pow_const 2).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]
    have : Real.exp (-a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    nlinarith [sq_nonneg (F t)]
  have hint : IntegrableOn (fun t => Real.exp (-a * t) * F t ^ 2) (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded M 0 hloc tendsto_id ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    simp only [Real.norm_eq_abs, abs_of_nonneg (hnn _)]
    exact hbound R hR
  refine ⟨hint, ?_⟩
  exact le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id) (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact hbound R hR)

/-- **Abel energy of a linear band.** `∫_0^L F² ≤ C(1 + L) + K` with `C ≥ 0` gives
`σ ∫_0^∞ e^{-σt} F² ≤ C(1 + σ) + Kσ`; the offset `K` disappears as `σ → 0`. -/
theorem abel_energy_of_linear_band {F : ℝ → ℝ} (hFm : Measurable F)
    (hF2 : ∀ T : ℝ, IntegrableOn (fun t => F t ^ 2) (Icc 0 T)) {C K : ℝ} (hC : 0 ≤ C)
    (hband : ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, F t ^ 2 ≤ C * (1 + L) + K)
    {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t => Real.exp (-σ * t) * F t ^ 2) (Ioi 0) ∧
      σ * ∫ t in Ioi 0, Real.exp (-σ * t) * F t ^ 2 ≤ C * (1 + σ) + K * σ := by
  have hd : ∀ t : ℝ, HasDerivAt (fun T : ℝ => Real.exp (-σ * T)) (Real.exp (-σ * t) * -σ) t :=
    fun t => by simpa using ((hasDerivAt_id t).const_mul (-σ)).exp
  -- the primitive of `σ e^{-σT}(C(1 + T) + K)`
  have hF : ∀ R : ℝ, σ * ∫ T in (0 : ℝ)..R, Real.exp (-σ * T) * (C * (1 + T) + K) =
      C * (1 + 1 / σ) + K - Real.exp (-σ * R) * (C * (1 + R + 1 / σ) + K) := by
    intro R
    have hderiv : ∀ T : ℝ,
        HasDerivAt (fun T : ℝ => -(Real.exp (-σ * T) * (C * (T + (1 + 1 / σ)) + K)))
          (σ * (Real.exp (-σ * T) * (C * (1 + T) + K))) T := by
      intro T
      have h1 : HasDerivAt (fun y : ℝ => Real.exp (-σ * y) * (C * (y + (1 + 1 / σ)) + K))
          (Real.exp (-σ * T) * -σ * (C * (T + (1 + 1 / σ)) + K) + Real.exp (-σ * T) * (C * 1)) T :=
        (hd T).mul ((((hasDerivAt_id' T).add_const (1 + 1 / σ)).const_mul C).add_const K)
      exact h1.neg.congr_deriv (by field_simp; ring)
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun T _ => hderiv T)
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp only [mul_zero, Real.exp_zero, zero_add, one_mul]; ring
  obtain ⟨hint, hle⟩ := abel_integral_le_of_primitive hFm hF2 (a := σ) (M := C * (1 + 1 / σ) + K) hσ
    (g := fun T => C * (1 + T) + K) (by fun_prop) hband (fun R hR => by
      rw [hF R]
      have hexp := (Real.exp_pos (-σ * R)).le
      have : 0 ≤ C * (Real.exp (-σ * R) * (1 / σ)) := by positivity
      nlinarith)
  refine ⟨hint, ?_⟩
  calc σ * ∫ t in Ioi 0, Real.exp (-σ * t) * F t ^ 2
      ≤ σ * (C * (1 + 1 / σ) + K) := mul_le_mul_of_nonneg_left hle hσ.le
    _ = C * (1 + σ) + K * σ := by field_simp; ring

/-! ## Abel orthonormality of critical characters -/

/-- The critical character `t ↦ e^{-iγt}`. -/
def criticalCharacter (γ t : ℝ) : ℂ := Complex.exp ((-(γ * t) : ℝ) * I)

theorem norm_criticalCharacter (γ t : ℝ) : ‖criticalCharacter γ t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem continuous_criticalCharacter (γ : ℝ) : Continuous (criticalCharacter γ) := by
  unfold criticalCharacter; fun_prop

theorem criticalCharacter_mul_conj (γ γ' t : ℝ) :
    criticalCharacter γ t * (starRingEnd ℂ) (criticalCharacter γ' t) =
      criticalCharacter (γ - γ') t := by
  simp only [criticalCharacter, ← Complex.exp_conj, ← Complex.exp_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  congr 1; push_cast; ring

theorem exp_mul_criticalCharacter (σ Δ t : ℝ) :
    (Real.exp (-σ * t) : ℂ) * criticalCharacter Δ t = Complex.exp ((-(σ : ℂ) - Δ * I) * t) := by
  rw [criticalCharacter, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `∫_0^∞ e^{-σt} e^{-iΔt} dt = 1/(σ + iΔ)`. -/
theorem integral_exp_mul_criticalCharacter {σ : ℝ} (hσ : 0 < σ) (Δ : ℝ) :
    ∫ t in Ioi (0 : ℝ), (Real.exp (-σ * t) : ℂ) * criticalCharacter Δ t =
      1 / ((σ : ℂ) + Δ * I) := by
  have ha : (-(σ : ℂ) - Δ * I).re < 0 := by simp; linarith
  simp_rw [exp_mul_criticalCharacter]
  rw [integral_exp_mul_complex_Ioi ha 0]
  have hne : -(σ : ℂ) - Δ * I ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  have hne' : (σ : ℂ) + Δ * I ≠ 0 := fun h0 => hne (by linear_combination -h0)
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

theorem integrableOn_exp_mul_criticalCharacter {σ : ℝ} (hσ : 0 < σ) (Δ : ℝ) :
    IntegrableOn (fun t : ℝ => (Real.exp (-σ * t) : ℂ) * criticalCharacter Δ t) (Ioi 0) := by
  have ha : (-(σ : ℂ) - Δ * I).re < 0 := by simp; linarith
  exact (integrableOn_exp_mul_complex_Ioi ha 0).congr_fun
    (fun t _ => (exp_mul_criticalCharacter σ Δ t).symm) measurableSet_Ioi

/-! ## Bessel's inequality for Abel coefficients -/

/-- **Abel–Bessel inequality.** Let `F` have Abel energy `σ ∫_0^∞ e^{-σt} F² ≤ a(σ) → A` and
Abel coefficients `σ ∫_0^∞ e^{-σt} F(t) e^{-iγ_k t} dt → c_k` at distinct ordinates `γ_k`.
Then `Σ_k |c_k|² ≤ A`. -/
theorem sum_norm_sq_le_of_abel {F : ℝ → ℝ} (hFm : Measurable F)
    (hint : ∀ σ : ℝ, 0 < σ → IntegrableOn (fun t => Real.exp (-σ * t) * F t ^ 2) (Ioi 0))
    {a : ℝ → ℝ} {A : ℝ}
    (henergy : ∀ σ : ℝ, 0 < σ → σ * ∫ t in Ioi 0, Real.exp (-σ * t) * F t ^ 2 ≤ a σ)
    (ha : Tendsto a (𝓝[>] 0) (𝓝 A))
    {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (hγ : Set.InjOn γ s) (c : ι → ℂ)
    (hcoef : ∀ k ∈ s, Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((Real.exp (-σ * t) * F t : ℝ) : ℂ) * criticalCharacter (γ k) t) (𝓝[>] 0) (𝓝 (c k))) :
    ∑ k ∈ s, ‖c k‖ ^ 2 ≤ A := by
  classical
  set a' : ι → ℂ := fun k => (starRingEnd ℂ) (c k) with ha'
  set S : ℝ := ∑ k ∈ s, ‖c k‖ ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm_a : ∀ k, ‖a' k‖ = ‖c k‖ := fun k => Complex.norm_conj _
  set P : ℝ → ℂ := fun σ => ∑ k ∈ s, a' k * ((σ : ℂ) * ∫ t in Ioi (0 : ℝ),
    ((Real.exp (-σ * t) * F t : ℝ) : ℂ) * criticalCharacter (γ k) t) with hPdef
  set G : ℝ → ℂ := fun σ => ∑ j ∈ s, ∑ k ∈ s,
    a' j * (starRingEnd ℂ) (a' k) * ((σ : ℂ) / ((σ : ℂ) + ((γ j - γ k : ℝ) : ℂ) * I)) with hGdef
  have hP : Tendsto P (𝓝[>] 0) (𝓝 (S : ℂ)) := by
    have h := tendsto_finsetSum s fun k hk => (hcoef k hk).const_mul (a' k)
    convert h using 2
    rw [hSdef]; push_cast
    exact Finset.sum_congr rfl fun k _ => (Complex.conj_mul' (c k)).symm
  have hG : Tendsto G (𝓝[>] 0) (𝓝 (S : ℂ)) := by
    have hterm : ∀ j ∈ s, ∀ k ∈ s, Tendsto
        (fun σ : ℝ => a' j * (starRingEnd ℂ) (a' k) *
          ((σ : ℂ) / ((σ : ℂ) + ((γ j - γ k : ℝ) : ℂ) * I)))
        (𝓝[>] 0) (𝓝 (if j = k then a' j * (starRingEnd ℂ) (a' k) else 0)) := by
      intro j hj k hk
      by_cases hjk : j = k
      · subst hjk
        rw [if_pos rfl]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with σ hσ
        change (0 : ℝ) < σ at hσ
        have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
        simp [hσ0]
      · rw [if_neg hjk]
        have hΔ : ((γ j - γ k : ℝ) : ℂ) * I ≠ 0 := by
          refine mul_ne_zero ?_ I_ne_zero
          exact_mod_cast sub_ne_zero.mpr fun h => hjk (hγ hj hk h)
        have hcont : Tendsto (fun σ : ℝ => (σ : ℂ) / ((σ : ℂ) + ((γ j - γ k : ℝ) : ℂ) * I))
            (𝓝 0) (𝓝 ((0 : ℂ) / (0 + ((γ j - γ k : ℝ) : ℂ) * I))) := by
          have h1 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 0) (𝓝 0) := by
            simpa using Complex.continuous_ofReal.tendsto 0
          exact h1.div (h1.add tendsto_const_nhds) (by simpa using hΔ)
        rw [zero_div] at hcont
        simpa using (hcont.mono_left nhdsWithin_le_nhds).const_mul
          (a' j * (starRingEnd ℂ) (a' k))
    have h := tendsto_finsetSum s fun j hj => tendsto_finsetSum s fun k hk => hterm j hj k hk
    convert h using 2
    simp only [Finset.sum_ite_eq]
    rw [hSdef]; push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_pos hj, Complex.mul_conj', hnorm_a]
  have hbound : ∀ σ : ℝ, 0 < σ → ‖P σ‖ ≤ (a σ + (G σ).re) / 2 := by
    intro σ hσ
    have hint2 := hint σ hσ
    set E : ℝ → ℝ := fun t => Real.exp (-σ * t) * F t with hE
    set φ : ℝ → ℂ := fun t => ∑ k ∈ s, a' k * criticalCharacter (γ k) t with hφ
    have hexpI : IntegrableOn (fun t : ℝ => Real.exp (-σ * t)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 hσ
    have hEm : Measurable E := (by fun_prop : Continuous fun t : ℝ => Real.exp (-σ * t)).measurable.mul hFm
    have hEabs : IntegrableOn (fun t => |E t|) (Ioi 0) := by
      refine ((hexpI.add hint2).div_const 2).mono' hEm.abs.aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      show ‖|E t|‖ ≤ (Real.exp (-σ * t) + Real.exp (-σ * t) * F t ^ 2) / 2
      simp only [hE, Real.norm_eq_abs, abs_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 := mul_nonneg (Real.exp_pos (-σ * t)).le (sq_nonneg (|F t| - 1))
      rw [sub_sq, sq_abs] at h1
      linarith
    have hEchar : ∀ γ' : ℝ, IntegrableOn (fun t => (E t : ℂ) * criticalCharacter γ' t) (Ioi 0) := by
      intro γ'
      refine hEabs.mono' ((Complex.continuous_ofReal.measurable.comp hEm).aestronglyMeasurable.mul
        (continuous_criticalCharacter γ').aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
      rw [norm_mul, norm_criticalCharacter, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hexpand : ∀ t, (E t : ℂ) * φ t =
        ∑ k ∈ s, a' k * ((E t : ℂ) * criticalCharacter (γ k) t) := fun t => by
      simp only [hφ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hsum : ∫ t in Ioi (0 : ℝ), (E t : ℂ) * φ t =
        ∑ k ∈ s, a' k * ∫ t in Ioi (0 : ℝ), (E t : ℂ) * criticalCharacter (γ k) t := by
      simp_rw [hexpand]
      rw [integral_finsetSum s fun k _ => (hEchar (γ k)).const_mul (a' k)]
      exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
    have hPeq : P σ = (σ : ℂ) * ∫ t in Ioi (0 : ℝ), (E t : ℂ) * φ t := by
      rw [hsum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [hE]; ring
    have hφbound : ∀ t, ‖φ t‖ ≤ ∑ k ∈ s, ‖a' k‖ := fun t =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => by
        rw [norm_mul, norm_criticalCharacter, mul_one])
    have hφcont : Continuous φ :=
      continuous_finsetSum s fun k _ => continuous_const.mul (continuous_criticalCharacter _)
    have hI2int : IntegrableOn (fun t => Real.exp (-σ * t) * ‖φ t‖ ^ 2) (Ioi 0) := by
      refine (hexpI.mul_const ((∑ k ∈ s, ‖a' k‖) ^ 2)).mono' ?_ (Eventually.of_forall fun t => ?_)
      · exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (-σ * t)).mul
          (hφcont.norm.pow 2)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hφbound t) 2)
          (Real.exp_pos _).le
    have hI2 : (σ : ℂ) * ((∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * ‖φ t‖ ^ 2 : ℝ) : ℂ) = G σ := by
      rw [← integral_complex_ofReal]
      have hpt : ∀ t, ((Real.exp (-σ * t) * ‖φ t‖ ^ 2 : ℝ) : ℂ) =
          ∑ j ∈ s, ∑ k ∈ s, a' j * (starRingEnd ℂ) (a' k) *
            ((Real.exp (-σ * t) : ℂ) * criticalCharacter (γ j - γ k) t) := by
        intro t
        push_cast
        rw [← Complex.mul_conj', hφ, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_mul, ← criticalCharacter_mul_conj]
        ring
      simp_rw [hpt]
      have hint3 : ∀ j ∈ s, ∀ k ∈ s, IntegrableOn (fun t => a' j * (starRingEnd ℂ) (a' k) *
          ((Real.exp (-σ * t) : ℂ) * criticalCharacter (γ j - γ k) t)) (Ioi 0) :=
        fun j _ k _ => (integrableOn_exp_mul_criticalCharacter hσ _).const_mul _
      rw [integral_finsetSum s fun j hj => integrable_finsetSum s fun k hk => hint3 j hj k hk,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [integral_finsetSum s fun k hk => hint3 j hj k hk, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul, integral_exp_mul_criticalCharacter hσ]
      push_cast
      ring
    have hpt : ∀ t, ‖(E t : ℂ) * φ t‖ ≤
        (Real.exp (-σ * t) * F t ^ 2 + Real.exp (-σ * t) * ‖φ t‖ ^ 2) / 2 := by
      intro t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hE, abs_mul, abs_of_pos (Real.exp_pos _)]
      have he := (Real.exp_pos (-σ * t)).le
      nlinarith [mul_nonneg he (sq_nonneg (|F t| - ‖φ t‖)), sq_abs (F t)]
    have hnormint : ‖∫ t in Ioi (0 : ℝ), (E t : ℂ) * φ t‖ ≤
        ((∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * F t ^ 2) +
          ∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * ‖φ t‖ ^ 2) / 2 := by
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_add hint2 hI2int, ← integral_div]
      exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        ((hint2.add hI2int).div_const 2) (Eventually.of_forall hpt)
    have hGre : (G σ).re = σ * ∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * ‖φ t‖ ^ 2 := by
      rw [← hI2]; simp
    rw [hPeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ, hGre]
    nlinarith [mul_le_mul_of_nonneg_left hnormint hσ.le, henergy σ hσ]
  have hlim1 : Tendsto (fun σ => ‖P σ‖) (𝓝[>] 0) (𝓝 S) := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0] using hP.norm
  have hlim2 : Tendsto (fun σ : ℝ => (a σ + (G σ).re) / 2) (𝓝[>] 0) (𝓝 ((A + (S : ℂ).re) / 2)) :=
    (ha.add ((Complex.continuous_re.tendsto _).comp hG)).div_const 2
  have hle := le_of_tendsto_of_tendsto hlim1 hlim2 (by
    filter_upwards [self_mem_nhdsWithin] with σ hσ using hbound σ hσ)
  simp only [Complex.ofReal_re] at hle
  linarith

/-! ## The band slope bounds the zero energy -/

/-- The weighted Laplace coefficient: `L(σ + iγ) = ∫_0^∞ (e^{-σt} Ẽ(t)) e^{-iγt} dt`. -/
theorem laplace_eq_integral_criticalCharacter (σ γ : ℝ) :
    _root_.RHTower.criticalNormalizedChebyshevErrorLaplace ((σ : ℂ) + γ * I) =
      ∫ t in Ioi (0 : ℝ), ((Real.exp (-σ * t) * normalizedLogError t : ℝ) : ℂ) *
        criticalCharacter γ t := by
  rw [criticalNormalizedChebyshevErrorLaplace_eq]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [criticalCharacter, Complex.ofReal_mul, Complex.ofReal_exp]
  have : Complex.exp (-(((σ : ℂ) + γ * I) * t)) =
      Complex.exp ((-σ * t : ℝ) : ℂ) * Complex.exp ((-(γ * t) : ℝ) * I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [this]; ring

/-- A band of slope `C` has `C ≥ 0`. -/
theorem nonneg_of_linear_band {F : ℝ → ℝ} {C K : ℝ}
    (hband : ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, F t ^ 2 ≤ C * (1 + L) + K) :
    0 ≤ C := by
  by_contra hneg
  rw [not_le] at hneg
  set L := (|K| + 1) / (-C)
  have hL : 0 ≤ L := div_nonneg (by positivity) (by linarith)
  have h := hband L hL
  have hpos : 0 ≤ ∫ t in Icc 0 L, F t ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  have hC0 : C ≠ 0 := hneg.ne
  have hCL : C * L = -(|K| + 1) := by
    simp only [L]; field_simp
  nlinarith [le_abs_self K]

/-- **The band slope bounds the zero energy.** If `∫_0^L Ẽ² ≤ C(1 + L) + K` for every `L ≥ 0`,
then for every finite family of distinct critical ordinates `γ_k`, with `n_k` the order of
`(s − 1)ζ(s)` at `ρ_k = 1/2 + iγ_k`, `Σ_k n_k²/|ρ_k|² ≤ C`. -/
theorem sum_order_sq_div_le_of_band {C K : ℝ}
    (hband : ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L) + K)
    {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (hγ : Set.InjOn γ s) (n : ι → ℤ)
    (horder : ∀ k ∈ s,
      meromorphicOrderAt _root_.RHTower.zetaResidueUnit (1 / 2 + γ k * I) = n k) :
    ∑ k ∈ s, (n k : ℝ) ^ 2 / (1 / 4 + γ k ^ 2) ≤ C := by
  have hC := nonneg_of_linear_band hband
  have hband' : ∀ L : ℝ, 0 ≤ L →
      ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ (C + |K|) * (1 + L) := fun L hL =>
    (hband L hL).trans (by nlinarith [le_abs_self K, abs_nonneg K])
  have hRH : RiemannHypothesis :=
    riemannHypothesis_iff_meanSquare_band.2 ⟨_, by positivity, hband'⟩
  have hXi := _root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.1 hRH
  have hcoef : ∀ k ∈ s, Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Ioi (0 : ℝ),
      ((Real.exp (-σ * t) * normalizedLogError t : ℝ) : ℂ) * criticalCharacter (γ k) t)
      (𝓝[>] 0) (𝓝 (-(n k : ℂ) / (1 / 2 + γ k * I))) := by
    intro k hk
    have horder' : meromorphicOrderAt _root_.RHTower.zetaResidueUnit
        (((1 / 2 + 0 : ℝ) : ℂ) + γ k * I) = n k := by
      rw [show (((1 / 2 + 0 : ℝ) : ℂ) + γ k * I) = 1 / 2 + γ k * I by push_cast; ring]
      exact horder k hk
    have h := tendsto_abel_laplace_of_halfPlane le_rfl (by norm_num) hXi horder'
    simp only [zero_add, add_zero, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] at h
    refine h.congr fun σ => ?_
    rw [laplace_eq_integral_criticalCharacter]
  have h := sum_norm_sq_le_of_abel measurable_normalizedLogError
    (fun σ hσ => (abel_energy_of_linear_band measurable_normalizedLogError
      integrableOn_normalizedLogError_sq hC hband hσ).1)
    (fun σ hσ => (abel_energy_of_linear_band measurable_normalizedLogError
      integrableOn_normalizedLogError_sq hC hband hσ).2)
    (a := fun σ => C * (1 + σ) + K * σ) (A := C)
    (by
      have hσ : Tendsto (fun σ : ℝ => σ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using ((tendsto_const_nhds (x := (1 : ℝ)).add hσ).const_mul C).add
        (hσ.const_mul K))
    s γ hγ _ hcoef
  refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_) h
  have hnormρ : ‖(1 / 2 + γ k * I : ℂ)‖ ^ 2 = 1 / 4 + γ k ^ 2 := by
    rw [Complex.sq_norm, show (1 / 2 + γ k * I : ℂ) = ((1 / 2 : ℝ) : ℂ) + (γ k : ℂ) * I by simp,
      Complex.normSq_add_mul_I]; ring
  rw [norm_div, norm_neg, div_pow, hnormρ, Complex.norm_intCast, sq_abs]

/-- Each critical zero has multiplicity at most `√C |ρ|` under a band of slope `C`. -/
theorem order_sq_le_of_band {C K : ℝ}
    (hband : ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L) + K)
    {γ : ℝ} {n : ℤ}
    (horder : meromorphicOrderAt _root_.RHTower.zetaResidueUnit (1 / 2 + γ * I) = n) :
    (n : ℝ) ^ 2 ≤ C * (1 / 4 + γ ^ 2) := by
  have h := sum_order_sq_div_le_of_band hband ({()} : Finset Unit) (fun _ => γ)
    (Set.injOn_of_subsingleton _ _) (fun _ => n) (fun _ _ => horder)
  simp only [Finset.sum_singleton] at h
  have hpos : (0 : ℝ) < 1 / 4 + γ ^ 2 := by positivity
  rwa [div_le_iff₀ hpos] at h

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
