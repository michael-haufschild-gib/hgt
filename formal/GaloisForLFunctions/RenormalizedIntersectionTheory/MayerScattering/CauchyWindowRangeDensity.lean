import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.CauchyCompatibleReflection
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspComplexStrip
import GaloisForLFunctions.RHTower.ExpDecayFourierAnalytic
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma41

/-!
# Local source windows determine Cauchy reflection

Exponential decay of the literal Cauchy symbol makes every averaged field analytic in a strip.
Analytic uniqueness propagates source compatibility from any nonempty interval to the whole line.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate FourierTransform ENNReal
open GaloisForLFunctions RenormalizedIntersectionTheory
open MayerScatteringCore MayerCauchyMellinSymbol

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- A single critical-line Gamma factor already gives exponential Cauchy smoothing.
The other Gamma factor is bounded by its positive-real-axis value. -/
theorem mayerCoreMellinFactor_exponential_bound (s : ℂ) (hs : 0 < s.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖mayerCoreMellinFactor s t‖ ≤ C * Real.exp (-(Real.pi * |t| / 4)) := by
  have hα : 0 < s.re + 1 / 2 := by linarith only [hs]
  have hΓ : 0 < Real.Gamma (s.re + 1 / 2) := Real.Gamma_pos_of_pos hα
  let C := (Real.sqrt (2 * Real.pi) * Real.Gamma (s.re + 1 / 2)) /
    (‖(Real.pi : ℂ) ^ (1 / 2 : ℂ)‖ * ‖Gamma ((2 * s + 1) / 2)‖ * ‖Gammaℝ (2 * s)‖)
  refine ⟨C, by dsimp only [C]; positivity, fun t => ?_⟩
  have hfirst : ‖Gamma (((t : ℂ) * I + 1) / 2)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 4)) := by
    have h := (HTGeometry.norm_Gamma_half_add_I_bounds (t / 2)).2
    rw [show (((t : ℂ) * I + 1) / 2) = 1 / 2 + ((t / 2 : ℝ) : ℂ) * I by push_cast; ring]
    convert h using 1
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 2
    ring
  have hre : ((2 * s + 1 - (t : ℂ) * I) / 2).re = s.re + 1 / 2 := by simp; ring
  have hsecond : ‖Gamma ((2 * s + 1 - (t : ℂ) * I) / 2)‖ ≤ Real.Gamma (s.re + 1 / 2) := by
    have h := HTGeometry.norm_Gamma_le_Gamma_re (show 0 < ((2 * s + 1 - (t : ℂ) * I) / 2).re by
      rw [hre]; exact hα)
    rwa [hre] at h
  rw [mayerCoreMellinFactor, MayerCauchyMellinSymbol.symbol, norm_div, norm_div, norm_mul, norm_mul]
  calc
    _ ≤ ((Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 4))) *
        Real.Gamma (s.re + 1 / 2) /
        (‖(Real.pi : ℂ) ^ (1 / 2 : ℂ)‖ * ‖Gamma ((2 * s + 1) / 2)‖)) / ‖Gammaℝ (2 * s)‖ :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
        (mul_le_mul hfirst hsecond (norm_nonneg _) (by positivity)) (by positivity)) (norm_nonneg _)
    _ = _ := by dsimp only [C]; ring


private theorem cauchy_frequency_exponential_bound (s : ℂ) (hs : 0 < s.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ,
      ‖mayerCoreMellinFactor s (2 * Real.pi * ξ)‖ ≤ C * Real.exp (-((Real.pi ^ 2 / 2) * |ξ|)) := by
  obtain ⟨C, hC, hb⟩ := mayerCoreMellinFactor_exponential_bound s hs
  refine ⟨C, hC, fun ξ => ?_⟩
  have he : Real.pi * |2 * Real.pi * ξ| / 4 = (Real.pi ^ 2 / 2) * |ξ| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    ring
  simpa only [he] using hb (2 * Real.pi * ξ)

private theorem expWeightIntegrable_multiplier
    (u v : Lp ℂ 2 (volume : Measure ℝ)) (φ : ℝ → ℂ)
    (hv : (v : ℝ → ℂ) =ᵐ[volume] fun ξ => φ ξ * u ξ)
    {C δ : ℝ} (hφ : ∀ ξ, ‖φ ξ‖ ≤ C * Real.exp (-(δ * |ξ|))) :
    _root_.RHTower.ExpWeightIntegrable (v : ℝ → ℂ) δ := by
  intro a ha
  have hbase := _root_.RHTower.integrable_memLp_mul_XiC_mul_expWeight ha (Lp.memLp u)
  refine (hbase.const_mul C).mono' ?_ ?_
  · exact (Lp.memLp v).aestronglyMeasurable.norm.mul (by fun_prop)
  · filter_upwards [hv] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hξ, norm_mul]
    calc
      ‖φ ξ‖ * ‖u ξ‖ * Real.exp (a * |ξ|) ≤
          (C * Real.exp (-(δ * |ξ|))) * ‖u ξ‖ * Real.exp (a * |ξ|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hφ ξ) (norm_nonneg _))
          (Real.exp_nonneg _)
      _ = C * (‖u ξ‖ * (Real.exp (-(δ * |ξ|)) * Real.exp (a * |ξ|))) := by ring

private theorem expFourier_eq_fourierInv (v : ℝ → ℂ) (x : ℝ) :
    _root_.RHTower.expFourier v (-(2 * Real.pi : ℂ) * (x : ℂ)) = 𝓕⁻ v x := by
  rw [_root_.RHTower.expFourier, Real.fourierInv_eq_fourier_neg,
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smul_eq_mul]
  have he : -(I * (-(2 * Real.pi : ℂ) * (x : ℂ)) * (ξ : ℂ)) =
      (((-2 * Real.pi * ξ * (-x) : ℝ) : ℂ) * I) := by push_cast; ring
  rw [he, mul_comm]

private theorem analytic_representative_of_frequency_weight
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : _root_.RHTower.ExpWeightIntegrable (HTGeometry.fourierL2 ℝ f : ℝ → ℂ) (Real.pi ^ 2 / 2)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {z : ℂ | |z.im| < Real.pi / 4} ∧
      (f : ℝ → ℂ) =ᵐ[volume] fun x => F (x : ℂ) := by
  let v := HTGeometry.fourierL2 ℝ f
  let F : ℂ → ℂ := fun z => _root_.RHTower.expFourier (v : ℝ → ℂ) (-(2 * Real.pi : ℂ) * z)
  have hv : Integrable (v : ℝ → ℂ) := by
    have h0 := hf 0 (by norm_num; positivity)
    refine h0.mono' (Lp.memLp v).aestronglyMeasurable ?_
    filter_upwards with x
    simp [v]
  refine ⟨F, ?_, ?_⟩
  · intro z hz
    have him : |(-(2 * Real.pi : ℂ) * z).im| < Real.pi ^ 2 / 2 := by
      have he : |(-(2 * Real.pi : ℂ) * z).im| = (2 * Real.pi) * |z.im| := by
        simp only [Complex.mul_im, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
          Complex.re_ofNat, Complex.ofReal_im, Complex.im_ofNat, mul_zero, zero_mul,
          sub_zero, add_zero, Complex.neg_im, neg_zero, abs_mul, abs_neg]
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
      rw [he]
      have h := mul_lt_mul_of_pos_left hz (show 0 < 2 * Real.pi by positivity)
      nlinarith only [h]
    exact (_root_.RHTower.analyticOnNhd_expFourier' (Lp.memLp v).aestronglyMeasurable hf
      (-(2 * Real.pi : ℂ) * z) him).comp
        (analyticAt_const.mul analyticAt_id)
  · have hi := _root_.RHTower.suzuki_l2_fourierInv_coeFn_eq_l1_fourierInv_of_integrable v hv
    change (HTGeometry.fourierL2inv ℝ (HTGeometry.fourierL2 ℝ f) : ℝ → ℂ) =ᵐ[volume]
      fun x => 𝓕⁻ (v : ℝ → ℂ) x at hi
    rw [HTGeometry.fourierL2inv_fourierL2] at hi
    refine hi.trans (Filter.Eventually.of_forall fun x => ?_)
    exact (expFourier_eq_fourierInv (v : ℝ → ℂ) x).symm

/-- Every actual Cauchy average of an arbitrary Haar `L²` input has a holomorphic strip representative. -/
theorem mayerCauchyHaarOperator_analytic_representative (s : ℂ) (hs : 0 < s.re)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {z : ℂ | |z.im| < Real.pi / 4} ∧
      (mayerCauchyHaarOperator s hs f : ℝ → ℂ) =ᵐ[volume] fun x => F (x : ℂ) := by
  obtain ⟨C, _, hb⟩ := cauchy_frequency_exponential_bound s hs
  apply analytic_representative_of_frequency_weight
  exact expWeightIntegrable_multiplier (HTGeometry.fourierL2 ℝ f) _ _
    (fourier_mayerCauchyHaarOperator_coeFn s hs f) hb

/-- The adjoint has the same analytic smoothing on every Haar `L²` input. -/
theorem adjoint_mayerCauchyHaarOperator_analytic_representative (s : ℂ) (hs : 0 < s.re)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {z : ℂ | |z.im| < Real.pi / 4} ∧
      (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) f : ℝ → ℂ) =ᵐ[volume]
        fun x => F (x : ℂ) := by
  obtain ⟨C, _, hb⟩ := cauchy_frequency_exponential_bound s hs
  apply analytic_representative_of_frequency_weight
  exact expWeightIntegrable_multiplier (HTGeometry.fourierL2 ℝ f) _ _
    (fourier_adjoint_mayerCauchyHaarOperator_coeFn s hs f)
      (fun ξ => (Complex.norm_conj _).trans_le (hb ξ))


private theorem supported_orthogonality_zero_on_interval
    (v : Lp ℂ 2 (volume : Measure ℝ)) (a b : ℝ)
    (horth : ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      (∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0) → inner ℂ f v = 0) :
    ∀ᵐ x ∂volume, x ∈ Ioo a b → v x = 0 := by
  let φ : ℝ → ℂ := (Ioo a b).indicator (fun _ => 1)
  have hm : Measurable φ := measurable_const.indicator measurableSet_Ioo
  have hb : ∀ x, ‖φ x‖ ≤ (1 : ℝ) := by
    intro x
    by_cases hx : x ∈ Ioo a b <;> simp [φ, hx]
  let f := lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hm zero_le_one hb v
  have hf : (f : ℝ → ℂ) =ᵐ[volume] fun x => φ x * v x := lpBoundedMulCLM_coeFn _ _ _ _
  have hsupport : ∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0 := by
    filter_upwards [hf] with x hx hnot
    rw [hx]
    simp [φ, hnot]
  have hi : inner ℂ f v = inner ℂ f f := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf] with x hfx
    by_cases hx : x ∈ Ioo a b
    · have he : f x = v x := by simpa [φ, hx] using hfx
      rw [he]
    · have he : f x = 0 := by simpa [φ, hx] using hfx
      rw [he]
      simp
  have hzero : f = 0 := inner_self_eq_zero.mp (hi.symm.trans (horth f hsupport))
  have hz : (f : ℝ → ℂ) =ᵐ[volume] 0 := by
    rw [hzero]
    exact Lp.coeFn_zero ℂ 2 volume
  filter_upwards [hf, hz] with x hfx hzx hx
  have he : f x = v x := by simpa [φ, hx] using hfx
  exact he.symm.trans hzx

private theorem continuous_zero_on_interval_of_ae
    {F : ℝ → ℂ} (hF : Continuous F) {a b : ℝ}
    (hae : ∀ᵐ x ∂volume, x ∈ Ioo a b → F x = 0) : ∀ x ∈ Ioo a b, F x = 0 := by
  intro x hx
  by_contra hn
  have ho : IsOpen (Ioo a b ∩ {y : ℝ | F y ≠ 0}) :=
    isOpen_Ioo.inter (isOpen_ne.preimage hF)
  have hnull : volume (Ioo a b ∩ {y : ℝ | F y ≠ 0}) = 0 := by
    refine measure_mono_null ?_ (mem_ae_iff.mp hae)
    intro y hy hgood
    exact hy.2 (hgood hy.1)
  have hp := ho.measure_pos volume (show (Ioo a b ∩ {y : ℝ | F y ≠ 0}).Nonempty from ⟨x, hx, hn⟩)
  rw [hnull] at hp
  exact lt_irrefl 0 hp

private theorem strip_zero_of_real_interval {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < Real.pi / 4})
    {a b : ℝ} (hab : a < b) (hz : ∀ x ∈ Ioo a b, F (x : ℂ) = 0) :
    ∀ x : ℝ, F (x : ℂ) = 0 := by
  let m := (a + b) / 2
  let q := fun n : ℕ => m + ((b - m) / 2) * (1 / ((n : ℝ) + 1))
  have ham : a < m := by dsimp only [m]; linarith only [hab]
  have hmb : m < b := by dsimp only [m]; linarith only [hab]
  have hmq (n : ℕ) : m < q n := by
    have hp : 0 < ((b - m) / 2) * (1 / ((n : ℝ) + 1)) := by positivity
    exact lt_add_of_pos_right m hp
  have hqb (n : ℕ) : q n < b := by
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith only [hn]
    have h := mul_le_mul_of_nonneg_left hle (by linarith only [hmb] : 0 ≤ (b - m) / 2)
    dsimp only [q]
    linarith only [h, hmb]
  have hlim : Tendsto q atTop (𝓝 m) := by
    have h := (tendsto_const_nhds (x := m)).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((b - m) / 2))
    simpa only [mul_zero, add_zero] using h
  have hc : (m : ℂ) ∈ closure ({z : ℂ | F z = 0} \ {(m : ℂ)}) := by
    apply mem_closure_of_tendsto ((Complex.continuous_ofReal.tendsto m).comp hlim)
    apply Eventually.of_forall
    intro n
    refine ⟨hz (q n) ⟨ham.trans (hmq n), hqb n⟩, ?_⟩
    change (q n : ℂ) ≠ (m : ℂ)
    exact fun h => (hmq n).ne' (Complex.ofReal_injective h)
  have hconn : IsPreconnected {z : ℂ | |z.im| < Real.pi / 4} := by
    have he : {z : ℂ | |z.im| < Real.pi / 4} =
        Complex.im ⁻¹' Ioo (-(Real.pi / 4)) (Real.pi / 4) := by
      ext z
      simp only [mem_setOf_eq, mem_preimage, mem_Ioo, abs_lt]
    rw [he]
    exact ((convex_Ioo (-(Real.pi / 4)) (Real.pi / 4)).linear_preimage Complex.imLm).isPreconnected
  have hm : (m : ℂ) ∈ {z : ℂ | |z.im| < Real.pi / 4} := by simp; positivity
  have he := hF.eqOn_zero_of_preconnected_of_mem_closure hconn hm hc
  intro x
  exact he (by simp; positivity)

/-- A strip-analytic Haar `L²` vector is determined by its pairings with one source interval. -/
theorem cauchyStripAnalytic_zero_of_local_orthogonality
    (v : Lp ℂ 2 (volume : Measure ℝ))
    (hv : ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {z : ℂ | |z.im| < Real.pi / 4} ∧
      (v : ℝ → ℂ) =ᵐ[volume] fun x => F (x : ℂ))
    {a b : ℝ} (hab : a < b)
    (horth : ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      (∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0) → inner ℂ f v = 0) : v = 0 := by
  obtain ⟨F, hF, hcoe⟩ := hv
  have hc : Continuous (fun x : ℝ => F (x : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hF (x : ℂ) (by simp; positivity)).continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hloc : ∀ᵐ x ∂volume, x ∈ Ioo a b → F (x : ℂ) = 0 := by
    filter_upwards [hcoe, supported_orthogonality_zero_on_interval v a b horth] with x he hx hmem
    rw [← he]
    exact hx hmem
  have hall := strip_zero_of_real_interval hF hab (continuous_zero_on_interval_of_ae hc hloc)
  apply Lp.ext
  filter_upwards [hcoe, Lp.coeFn_zero ℂ 2 volume] with x hx hz
  exact hx.trans ((hall x).trans hz.symm)

private def windowCutoff (a b : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (φ := (Ioo a b).indicator (fun _ : ℝ => (1 : ℂ)))
    (measurable_const.indicator measurableSet_Ioo) zero_le_one
    (fun x => by by_cases hx : x ∈ Ioo a b <;> simp [hx])

private theorem windowCutoff_coeFn (a b : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (windowCutoff a b f : ℝ → ℂ) =ᵐ[volume]
      fun x => (Ioo a b).indicator (fun _ => (1 : ℂ)) x * f x :=
  lpBoundedMulCLM_coeFn _ _ _ _

private theorem windowCutoff_supported (a b : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ x ∂volume, x ∉ Ioo a b → windowCutoff a b f x = 0 := by
  filter_upwards [windowCutoff_coeFn a b f] with x hx hnot
  rw [hx]
  simp [hnot]

private theorem windowCutoff_fix (a b : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : ∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0) : windowCutoff a b f = f := by
  apply Lp.ext
  filter_upwards [windowCutoff_coeFn a b f, hf] with x hx hs
  rw [hx]
  by_cases hmem : x ∈ Ioo a b
  · simp [hmem]
  · simp [hmem, hs hmem]

/-- Actual Cauchy averaging of the input restricted to one logarithmic source window. -/
def mayerCauchyWindowOperator (s : ℂ) (hs : 0 < s.re) (a b : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (mayerCauchyHaarOperator s hs).comp (windowCutoff a b)

/-- The window operator retains the literal integral over the specified source interval. -/
theorem mayerCauchyWindowOperator_coeFn (s : ℂ) (hs : 0 < s.re) (a b : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (mayerCauchyWindowOperator s hs a b f : ℝ → ℂ) =ᵐ[volume]
      fun y => ∫ z in Ioo a b, mayerCauchyHaarKernel s (y - z) * f z := by
  filter_upwards [mayerCauchyHaarOperator_coeFn s hs (windowCutoff a b f)] with y hy
  change mayerCauchyHaarOperator s hs (windowCutoff a b f) y = _
  rw [hy, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [windowCutoff_coeFn a b f] with z hz
  rw [hz]
  by_cases hmem : z ∈ Ioo a b <;> simp [hmem]

/-- Every positive-length source window has dense physical range under actual Cauchy averaging. -/
theorem denseRange_mayerCauchyWindowOperator (s : ℂ) (hs : 0 < s.re)
    (a b : ℝ) (hab : a < b) : DenseRange (mayerCauchyWindowOperator s hs a b) := by
  refine HTGeometry.denseRange_of_orthogonal_trivial fun g hg => ?_
  have hz : ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) g = 0 := by
    apply cauchyStripAnalytic_zero_of_local_orthogonality _
      (adjoint_mayerCauchyHaarOperator_analytic_representative s hs g) hab
    intro f hf
    rw [ContinuousLinearMap.adjoint_inner_right]
    have h := hg f
    change inner ℂ (mayerCauchyHaarOperator s hs (windowCutoff a b f)) g = 0 at h
    rwa [windowCutoff_fix a b f hf] at h
  have he : (fun v : Lp ℂ 2 (volume : Measure ℝ) => inner ℂ v g) = fun _ => (0 : ℂ) := by
    apply (denseRange_mayerCauchyHaarOperator s hs).equalizer
      (continuous_id.inner continuous_const) continuous_const
    funext f
    change inner ℂ (mayerCauchyHaarOperator s hs f) g = 0
    rw [← ContinuousLinearMap.adjoint_inner_right, hz, inner_zero_right]
  exact inner_self_eq_zero.mp (congrFun he g)

private theorem local_cauchy_linear_factorization_global
    (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re) (a b : ℝ) (hab : a < b)
    (S : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hlocal : ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      (∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0) →
      S (mayerCauchyHaarOperator s hs f) = ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) f) :
    ∀ f, S (mayerCauchyHaarOperator s hs f) = ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) f := by
  have hrow (g : Lp ℂ 2 (volume : Measure ℝ)) :
      ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) (ContinuousLinearMap.adjoint S g) -
        mayerCauchyHaarOperator r hr g = 0 := by
    obtain ⟨F₁, hF₁, he₁⟩ := adjoint_mayerCauchyHaarOperator_analytic_representative s hs
      (ContinuousLinearMap.adjoint S g)
    obtain ⟨F₂, hF₂, he₂⟩ := mayerCauchyHaarOperator_analytic_representative r hr g
    refine cauchyStripAnalytic_zero_of_local_orthogonality _ ?_ hab ?_
    · refine ⟨F₁ - F₂, hF₁.sub hF₂, ?_⟩
      filter_upwards [he₁, he₂, Lp.coeFn_sub
        (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) (ContinuousLinearMap.adjoint S g))
        (mayerCauchyHaarOperator r hr g)] with x h1 h2 hsub
      simp only [hsub, Pi.sub_apply, h1, h2]
    · intro f hf
      rw [inner_sub_right]
      apply sub_eq_zero.mpr
      calc
        _ = inner ℂ (mayerCauchyHaarOperator s hs f) (ContinuousLinearMap.adjoint S g) :=
          ContinuousLinearMap.adjoint_inner_right _ _ _
        _ = inner ℂ (S (mayerCauchyHaarOperator s hs f)) g :=
          ContinuousLinearMap.adjoint_inner_right _ _ _
        _ = inner ℂ (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) f) g :=
          congrArg (fun v => inner ℂ v g) (hlocal f hf)
        _ = _ := ContinuousLinearMap.adjoint_inner_left _ _ _
  intro f
  let d := S (mayerCauchyHaarOperator s hs f) - ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) f
  have hc := congrArg (fun v => inner ℂ f v) (sub_eq_zero.mp (hrow d))
  have h1 := ContinuousLinearMap.adjoint_inner_right S (mayerCauchyHaarOperator s hs f) d
  have h2 := ContinuousLinearMap.adjoint_inner_right (mayerCauchyHaarOperator s hs) f
    (ContinuousLinearMap.adjoint S d)
  have h3 := ContinuousLinearMap.adjoint_inner_left (mayerCauchyHaarOperator r hr) d f
  have heq := h1.symm.trans (h2.symm.trans (hc.trans h3.symm))
  have hd : inner ℂ d d = 0 := by
    change inner ℂ (S (mayerCauchyHaarOperator s hs f) -
      ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) f) d = 0
    rw [inner_sub_left, heq, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hd)


private def leftLinearizedReflection
    (R : Lp ℂ 2 (volume : Measure ℝ) → Lp ℂ 2 (volume : Measure ℝ))
    (hadd : ∀ f g, R (f + g) = R f + R g)
    (hsmul : ∀ (c : ℂ) f, R (c • f) = conj c • R f)
    (C : ℝ) (hbound : ∀ f, ‖R f‖ ≤ C * ‖f‖) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  ({ toFun := fun f => mayerFieldReflection (R f)
     map_add' := fun f g => by rw [hadd, mayerFieldReflection_add]
     map_smul' := fun c f => by
       simp only [hsmul, mayerFieldReflection_smul, starRingEnd_self_apply, RingHom.id_apply] }
    : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ)).mkContinuous C
    (fun f => by
      change ‖mayerFieldReflection (R f)‖ ≤ C * ‖f‖
      simpa only [norm_mayerFieldReflection] using hbound f)

/-- Compatibility on one positive-length source interval forces compatibility on every input.
The field reflection need not preserve the interval: applying it to the output gives the
linear adjoint factorization whose rows are analytic. -/
theorem mayerCauchy_compatible_on_window_iff_global
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) (a b : ℝ) (hab : a < b)
    (R : Lp ℂ 2 (volume : Measure ℝ) → Lp ℂ 2 (volume : Measure ℝ))
    (hadd : ∀ f g, R (f + g) = R f + R g)
    (hsmul : ∀ (c : ℂ) f, R (c • f) = conj c • R f)
    (C : ℝ) (hbound : ∀ f, ‖R f‖ ≤ C * ‖f‖) :
    (∀ f : Lp ℂ 2 (volume : Measure ℝ),
      (∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0) →
      R (mayerCauchyHaarOperator s hs0 f) =
        mayerCauchyHaarOperator (riemannMayerReflect s)
          (by simp [riemannMayerReflect]; linarith only [hs1]) (mayerFieldReflection f)) ↔
    (∀ f, R (mayerCauchyHaarOperator s hs0 f) =
      mayerCauchyHaarOperator (riemannMayerReflect s)
        (by simp [riemannMayerReflect]; linarith only [hs1]) (mayerFieldReflection f)) := by
  constructor
  · intro hlocal
    have hr : 0 < (riemannMayerReflect s).re := by
      simp [riemannMayerReflect]; linarith only [hs1]
    let S := leftLinearizedReflection R hadd hsmul C hbound
    have hS := local_cauchy_linear_factorization_global s (riemannMayerReflect s) hs0 hr a b hab S
      (fun f hf => by
        have h := congrArg mayerFieldReflection (hlocal f hf)
        change mayerFieldReflection (R (mayerCauchyHaarOperator s hs0 f)) =
          mayerFieldReflection (mayerCauchyHaarOperator (riemannMayerReflect s) hr (mayerFieldReflection f)) at h
        rw [mayerFieldReflection_cauchy_adjoint] at h
        exact h)
    intro f
    have h := congrArg mayerFieldReflection (hS f)
    change mayerFieldReflection (mayerFieldReflection (R (mayerCauchyHaarOperator s hs0 f))) =
      mayerFieldReflection (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator (riemannMayerReflect s) hr) f) at h
    rw [mayerFieldReflection_involutive] at h
    refine h.trans ?_
    rw [← mayerFieldReflection_cauchy_adjoint (riemannMayerReflect s) hr f,
      mayerFieldReflection_involutive]
  · exact fun h f _ => h f

/-- Even one arbitrarily short source window imposes the sharp half-strip boundary on every
bounded conjugate-linear compatible reflection. -/
theorem mayerCauchy_bounded_window_reflection_iff
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) (a b : ℝ) (hab : a < b) :
    (∃ R : Lp ℂ 2 (volume : Measure ℝ) → Lp ℂ 2 (volume : Measure ℝ),
      (∀ f g, R (f + g) = R f + R g) ∧
      (∀ (c : ℂ) f, R (c • f) = conj c • R f) ∧
      (∃ C : ℝ, ∀ f, ‖R f‖ ≤ C * ‖f‖) ∧
      (∀ f : Lp ℂ 2 (volume : Measure ℝ),
        (∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0) →
        R (mayerCauchyHaarOperator s hs0 f) =
          mayerCauchyHaarOperator (riemannMayerReflect s)
            (by simp [riemannMayerReflect]; linarith only [hs1]) (mayerFieldReflection f))) ↔
      1 / 4 ≤ s.re := by
  constructor
  · rintro ⟨R, hadd, hsmul, ⟨C, hbound⟩, hlocal⟩
    apply (mayerCauchy_bounded_compatible_reflection_iff s hs0 hs1).mp
    exact ⟨R, hadd, hsmul, ⟨C, hbound⟩,
      (mayerCauchy_compatible_on_window_iff_global s hs0 hs1 a b hab R hadd hsmul C hbound).mp hlocal⟩
  · intro hs
    obtain ⟨R, hadd, hsmul, hb, hcomp⟩ := (mayerCauchy_bounded_compatible_reflection_iff s hs0 hs1).mpr hs
    exact ⟨R, hadd, hsmul, hb, fun f _ => hcomp f⟩

/-- A bounded reflection specified on one source window is the unique global Cauchy correction. -/
theorem mayerCauchy_window_reflection_unique
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) (hs : 1 / 4 ≤ s.re)
    (a b : ℝ) (hab : a < b)
    (R : Lp ℂ 2 (volume : Measure ℝ) → Lp ℂ 2 (volume : Measure ℝ))
    (hadd : ∀ f g, R (f + g) = R f + R g)
    (hsmul : ∀ (c : ℂ) f, R (c • f) = conj c • R f)
    (C : ℝ) (hbound : ∀ f, ‖R f‖ ≤ C * ‖f‖)
    (hlocal : ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      (∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0) →
      R (mayerCauchyHaarOperator s hs0 f) =
        mayerCauchyHaarOperator (riemannMayerReflect s)
          (by simp [riemannMayerReflect]; linarith only [hs1]) (mayerFieldReflection f)) :
    R = mayerCauchyReflection s hs0 hs1 hs :=
  mayerCauchy_compatible_reflection_unique s hs0 hs1 hs R hadd hsmul C hbound
    ((mayerCauchy_compatible_on_window_iff_global s hs0 hs1 a b hab R hadd hsmul C hbound).mp hlocal)


#print axioms mayerCoreMellinFactor_exponential_bound
#print axioms mayerCauchyHaarOperator_analytic_representative
#print axioms adjoint_mayerCauchyHaarOperator_analytic_representative
#print axioms mayerCauchyWindowOperator_coeFn
#print axioms denseRange_mayerCauchyWindowOperator
#print axioms mayerCauchy_compatible_on_window_iff_global
#print axioms mayerCauchy_bounded_window_reflection_iff
#print axioms mayerCauchy_window_reflection_unique
#print axioms cauchyStripAnalytic_zero_of_local_orthogonality

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
