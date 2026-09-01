import Mathlib

/-!
# The boundary Cauchy kernel as a probability density

The real-boundary divisor measure of a logarithmic derivative is built from the distributional
boundary value `-(1/π) Im (F'/F)(t + iε)`.  Near a real zero of multiplicity `m` the singular part
of `F'/F` is `m/(z - γ)`, so the kernel that appears is

`-(1/π) Im (1/(t - γ + iε)) = m ↦ π⁻¹ ε / ((t-γ)² + ε²)`,

which is exactly mathlib's **Cauchy probability density** `ProbabilityTheory.cauchyPDFReal` with
location `γ` and scale `ε` (`neg_im_inv_eq_cauchyPDFReal`).  Making that identification rather than
introducing a bespoke Poisson kernel means the total mass and integrability come for free from
`integral_cauchyPDFReal_eq_one` and `integrable_cauchyPDFReal`.

`cauchyPDFReal_le_of_dist` is the uniform decay away from the centre — the hypothesis an
approximate-identity argument needs — and `im_inv_add_inv_conj_eq_zero` is the observation that a
conjugate pair of nonreal poles has *real* boundary value on the real axis, so it contributes no
atom.
-/

noncomputable section

open Complex Filter Topology MeasureTheory Set ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry


/-- **The boundary Cauchy kernel is the Cauchy density.**  The negative imaginary part of the
boundary value `1/(t - γ + iε)` of the Cauchy kernel is exactly `π` times mathlib's Cauchy
probability density with location `γ` and scale `ε`.  This identification turns the distributional
boundary value of a logarithmic derivative into an approximate identity with a *known* total
mass (`ProbabilityTheory.integral_cauchyPDFReal_eq_one`). -/
theorem neg_im_inv_eq_cauchyPDFReal {ε : ℝ} {s : NNReal} (hs : (s : ℝ) = ε) (hε : 0 < ε)
    (γ t : ℝ) :
    -(((t : ℂ) - (γ : ℂ) + (ε : ℂ) * I)⁻¹).im
      = Real.pi * cauchyPDFReal γ s t := by
  have hnormSq : Complex.normSq ((t : ℂ) - (γ : ℂ) + (ε : ℂ) * I)
      = (t - γ) ^ 2 + ε ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  have him : ((t : ℂ) - (γ : ℂ) + (ε : ℂ) * I).im = ε := by simp
  rw [Complex.inv_im, hnormSq, him, cauchyPDFReal_def, hs]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : (t - γ) ^ 2 + ε ^ 2 ≠ 0 := by positivity
  field_simp

/-- Away from the centre the kernel is uniformly small, with an explicit bound. -/
theorem cauchyPDFReal_le_of_dist {ε : ℝ} {s : NNReal} (hs : (s : ℝ) = ε) (hε : 0 < ε)
    (γ t d : ℝ) (hd : 0 < d) (ht : d ≤ |t - γ|) :
    cauchyPDFReal γ s t ≤ Real.pi⁻¹ * ε / d ^ 2 := by
  rw [cauchyPDFReal_def, hs]
  have hsq : d ^ 2 ≤ (t - γ) ^ 2 := by
    have h1 : |t - γ| ^ 2 = (t - γ) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (t - γ)]
  have hd2 : (0 : ℝ) < d ^ 2 := by positivity
  have hcoef : (0 : ℝ) ≤ Real.pi⁻¹ * ε := by positivity
  have hinv : ((t - γ) ^ 2 + ε ^ 2)⁻¹ ≤ (d ^ 2)⁻¹ := by
    have hpos : (0 : ℝ) < (t - γ) ^ 2 + ε ^ 2 := by positivity
    gcongr
    nlinarith
  calc Real.pi⁻¹ * ε * ((t - γ) ^ 2 + ε ^ 2)⁻¹
      ≤ Real.pi⁻¹ * ε * (d ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hinv hcoef
    _ = Real.pi⁻¹ * ε / d ^ 2 := by rw [div_eq_mul_inv]

/-- The conjugate-symmetric pair of nonreal poles has real boundary value, so it contributes
nothing to the imaginary part in the limit. -/
theorem im_inv_add_inv_conj_eq_zero (ρ : ℂ) (t : ℝ) (h1 : (t : ℂ) - ρ ≠ 0) :
    (((t : ℂ) - ρ)⁻¹ + ((t : ℂ) - (starRingEnd ℂ) ρ)⁻¹).im = 0 := by
  have hconj : (t : ℂ) - (starRingEnd ℂ) ρ = (starRingEnd ℂ) ((t : ℂ) - ρ) := by
    rw [map_sub, Complex.conj_ofReal]
  rw [hconj, ← map_inv₀]
  have hsum : ((t : ℂ) - ρ)⁻¹ + (starRingEnd ℂ) (((t : ℂ) - ρ)⁻¹)
      = ((2 : ℝ) : ℂ) * (((t : ℂ) - ρ)⁻¹).re := by
    rw [Complex.add_conj]
    push_cast
    ring
  rw [hsum]
  simp


/-! ## The Cauchy kernel as an approximate identity

mathlib's peak-function machinery already contains the scaling form of the approximate-identity
theorem (`tendsto_integral_comp_smul_smul_of_integrable`): a nonnegative density of integral one
whose `‖x‖^d`-weighted tail vanishes gives peak functions under rescaling.  The Cauchy density
satisfies both hypotheses, and its rescalings are again Cauchy densities of the reciprocal scale,
so the boundary limit of the card is an instance of that theorem rather than a fresh construction.
-/


/-- The standard Cauchy density rescales to the Cauchy density of the reciprocal scale. -/
theorem smul_cauchyPDFReal_zero_one {c : ℝ} (hc : 0 < c) (x : ℝ) :
    c ^ (Module.finrank ℝ ℝ) * cauchyPDFReal 0 1 (c • x)
      = cauchyPDFReal 0 (Real.toNNReal c⁻¹) x := by
  have hfr : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  have hinv : ((Real.toNNReal c⁻¹ : NNReal) : ℝ) = c⁻¹ := Real.coe_toNNReal _ (by positivity)
  rw [hfr, cauchyPDFReal_def, cauchyPDFReal_def, hinv]
  have hcne : c ≠ 0 := ne_of_gt hc
  simp only [NNReal.coe_one, smul_eq_mul, sub_zero]
  field_simp

/-- The tail decay hypothesis of the peak-function theorem for the Cauchy density. -/
theorem tendsto_norm_mul_cauchyPDFReal :
    Tendsto (fun x : ℝ => ‖x‖ ^ (Module.finrank ℝ ℝ) * cauchyPDFReal 0 1 x)
      (Bornology.cobounded ℝ) (𝓝 0) := by
  have hfr : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  have hform : ∀ x : ℝ, ‖x‖ ^ (Module.finrank ℝ ℝ) * cauchyPDFReal 0 1 x
      = Real.pi⁻¹ * (|x| / (x ^ 2 + 1)) := by
    intro x
    rw [hfr, cauchyPDFReal_def]
    simp only [pow_one, Real.norm_eq_abs, NNReal.coe_one, sub_zero, one_pow, mul_one]
    field_simp
  rw [funext hform]
  have hy : Tendsto (fun y : ℝ => y / (y ^ 2 + 1)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      rw [div_le_iff₀ (by positivity)]
      have hy0 : (0 : ℝ) < y := by linarith
      rw [inv_mul_eq_div, le_div_iff₀ hy0]
      nlinarith
  have hnorm : Tendsto (fun x : ℝ => ‖x‖) (Bornology.cobounded ℝ) atTop :=
    tendsto_norm_cobounded_atTop
  have hcomp : Tendsto (fun x : ℝ => |x| / (x ^ 2 + 1)) (Bornology.cobounded ℝ) (𝓝 0) := by
    have h := hy.comp hnorm
    refine h.congr (fun x => ?_)
    simp only [Function.comp_apply, Real.norm_eq_abs, sq_abs]
  simpa using hcomp.const_mul Real.pi⁻¹


theorem cauchyPDFReal_translate (γ : ℝ) (s : NNReal) (u : ℝ) :
    cauchyPDFReal γ s (u + γ) = cauchyPDFReal 0 s u := by
  rw [cauchyPDFReal_def, cauchyPDFReal_def]
  congr 2
  ring

/-- **The Cauchy kernel is an approximate identity on the line.**  For an integrable `g`
continuous at `γ`, pairing against the Cauchy density of shrinking scale recovers `g γ`. -/
theorem tendsto_integral_cauchyPDFReal_mul {g : ℝ → ℝ} (hg : Integrable g) {γ : ℝ}
    (hcont : ContinuousAt g γ) :
    Tendsto (fun c : ℝ => ∫ t, cauchyPDFReal γ (Real.toNNReal c⁻¹) t * g t)
      atTop (𝓝 (g γ)) := by
  have hfr : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  set g' : ℝ → ℝ := fun u => g (u + γ) with hg'def
  have hg'int : Integrable g' := by
    have := hg.comp_add_right γ
    exact this
  have hg'cont : ContinuousAt g' 0 := by
    have htend : Filter.Tendsto (fun u : ℝ => u + γ) (𝓝 0) (𝓝 γ) := by
      have h : Filter.Tendsto (fun u : ℝ => u + γ) (𝓝 0) (𝓝 (0 + γ)) :=
        (tendsto_id.add tendsto_const_nhds)
      rwa [zero_add] at h
    have hcomp : Filter.Tendsto (fun u : ℝ => g (u + γ)) (𝓝 0) (𝓝 (g γ)) :=
      Filter.Tendsto.comp hcont htend
    have hzero : g' 0 = g γ := by simp [hg'def]
    rw [ContinuousAt, hzero]
    exact hcomp
  have hmain := tendsto_integral_comp_smul_smul_of_integrable
    (μ := (volume : Measure ℝ))
    (φ := cauchyPDFReal 0 1)
    (fun x => (cauchyPDF_pos 0 (by norm_num) x).le)
    (integral_cauchyPDFReal_eq_one 0 (by norm_num))
    tendsto_norm_mul_cauchyPDFReal hg'int hg'cont
  have hzero : g' 0 = g γ := by simp [hg'def]
  rw [hzero] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hstep : ∀ x : ℝ, (c ^ (Module.finrank ℝ ℝ) * cauchyPDFReal 0 1 (c • x)) • g' x
      = cauchyPDFReal γ (Real.toNNReal c⁻¹) (x + γ) * g (x + γ) := by
    intro x
    rw [smul_eq_mul, smul_cauchyPDFReal_zero_one hc x, cauchyPDFReal_translate]
  rw [funext hstep]
  exact integral_add_right_eq_self
    (fun t => cauchyPDFReal γ (Real.toNNReal c⁻¹) t * g t) γ


/-! ## Nonreal conjugate pairs carry no boundary atom

`im_inv_add_inv_conj_eq_zero` says the pair kernel vanishes *at* `ε = 0`.  What the boundary
theorem needs is that its pairing against a test function vanishes *in the limit*, which is
dominated convergence: near `ε = 0` the two denominators stay a fixed distance `|Im ρ|/2` from the
real axis, so the kernel is bounded by `4/|Im ρ|` uniformly, and it converges pointwise to `0`.
-/


/-- The boundary pair kernel of a nonreal pole and its conjugate. -/
def conjPairKernel (ρ : ℂ) (ε t : ℝ) : ℝ :=
  (((t : ℂ) + (ε : ℂ) * I - ρ)⁻¹ + ((t : ℂ) + (ε : ℂ) * I - (starRingEnd ℂ) ρ)⁻¹).im

theorem im_shift (ρ : ℂ) (ε t : ℝ) : ((t : ℂ) + (ε : ℂ) * I - ρ).im = ε - ρ.im := by
  simp

theorem norm_inv_le {ρ : ℂ} {ε t : ℝ} (h : ε - ρ.im ≠ 0) :
    ‖((t : ℂ) + (ε : ℂ) * I - ρ)⁻¹‖ ≤ |ε - ρ.im|⁻¹ := by
  have hne : ((t : ℂ) + (ε : ℂ) * I - ρ) ≠ 0 := by
    intro hzero
    apply h
    have := congrArg Complex.im hzero
    rw [im_shift] at this
    simpa using this
  rw [norm_inv]
  have habs : |((t : ℂ) + (ε : ℂ) * I - ρ).im| ≤ ‖((t : ℂ) + (ε : ℂ) * I - ρ)‖ :=
    Complex.abs_im_le_norm _
  rw [im_shift] at habs
  have hpos : (0 : ℝ) < |ε - ρ.im| := abs_pos.mpr h
  gcongr

theorem norm_conjPairKernel_le {ρ : ℂ} {ε t : ℝ} (h1 : ε - ρ.im ≠ 0) (h2 : ε + ρ.im ≠ 0) :
    |conjPairKernel ρ ε t| ≤ |ε - ρ.im|⁻¹ + |ε + ρ.im|⁻¹ := by
  have hconj : ((starRingEnd ℂ) ρ).im = -ρ.im := by simp
  have hb1 := norm_inv_le (ρ := ρ) (ε := ε) (t := t) h1
  have hb2 : ‖((t : ℂ) + (ε : ℂ) * I - (starRingEnd ℂ) ρ)⁻¹‖ ≤ |ε + ρ.im|⁻¹ := by
    have h2' : ε - ((starRingEnd ℂ) ρ).im ≠ 0 := by rw [hconj]; simpa using h2
    have hb := norm_inv_le (ρ := (starRingEnd ℂ) ρ) (ε := ε) (t := t) h2'
    rw [hconj] at hb
    simpa using hb
  refine le_trans (Complex.abs_im_le_norm _) ?_
  refine le_trans (norm_add_le _ _) ?_
  exact add_le_add hb1 hb2


theorem conjPairKernel_zero {ρ : ℂ} (hρ : ρ.im ≠ 0) (t : ℝ) : conjPairKernel ρ 0 t = 0 := by
  have hne : (t : ℂ) - ρ ≠ 0 := by
    intro hzero
    apply hρ
    have := congrArg Complex.im hzero
    simpa using this.symm
  have hcoord : ((t : ℂ) + ((0 : ℝ) : ℂ) * I - ρ) = (t : ℂ) - ρ := by push_cast; ring
  have hcoord' : ((t : ℂ) + ((0 : ℝ) : ℂ) * I - (starRingEnd ℂ) ρ)
      = (t : ℂ) - (starRingEnd ℂ) ρ := by push_cast; ring
  rw [conjPairKernel, hcoord, hcoord']
  exact im_inv_add_inv_conj_eq_zero ρ t hne

theorem continuousAt_conjPairKernel {ρ : ℂ} (hρ : ρ.im ≠ 0) (t : ℝ) :
    ContinuousAt (fun ε : ℝ => conjPairKernel ρ ε t) 0 := by
  have hne : ((t : ℂ) + ((0 : ℝ) : ℂ) * I - ρ) ≠ 0 := by
    intro hzero
    apply hρ
    have him := congrArg Complex.im hzero
    rw [im_shift] at him
    simpa using him.symm
  have hne' : ((t : ℂ) + ((0 : ℝ) : ℂ) * I - (starRingEnd ℂ) ρ) ≠ 0 := by
    intro hzero
    apply hρ
    have him := congrArg Complex.im hzero
    rw [im_shift] at him
    simp at him
    linarith
  have h1 : ContinuousAt (fun ε : ℝ => ((t : ℂ) + (ε : ℂ) * I - ρ)⁻¹) 0 :=
    ContinuousAt.inv₀ (by fun_prop) hne
  have h2 : ContinuousAt (fun ε : ℝ => ((t : ℂ) + (ε : ℂ) * I - (starRingEnd ℂ) ρ)⁻¹) 0 :=
    ContinuousAt.inv₀ (by fun_prop) hne'
  exact Complex.continuous_im.continuousAt.comp (h1.add h2)

theorem tendsto_conjPairKernel {ρ : ℂ} (hρ : ρ.im ≠ 0) (t : ℝ) :
    Tendsto (fun ε : ℝ => conjPairKernel ρ ε t) (𝓝 0) (𝓝 0) := by
  have h := continuousAt_conjPairKernel hρ t
  rw [ContinuousAt, conjPairKernel_zero hρ t] at h
  exact h


theorem continuous_conjPairKernel_of_ne {ρ : ℂ} {ε : ℝ} (h1 : ε - ρ.im ≠ 0)
    (h2 : ε + ρ.im ≠ 0) : Continuous (fun t : ℝ => conjPairKernel ρ ε t) := by
  have hne : ∀ t : ℝ, ((t : ℂ) + (ε : ℂ) * I - ρ) ≠ 0 := by
    intro t hzero
    apply h1
    have him := congrArg Complex.im hzero
    rw [im_shift] at him
    simpa using him
  have hne' : ∀ t : ℝ, ((t : ℂ) + (ε : ℂ) * I - (starRingEnd ℂ) ρ) ≠ 0 := by
    intro t hzero
    apply h2
    have him := congrArg Complex.im hzero
    rw [im_shift] at him
    simp at him
    linarith
  refine Complex.continuous_im.comp (Continuous.add ?_ ?_)
  · exact Continuous.inv₀ (by fun_prop) hne
  · exact Continuous.inv₀ (by fun_prop) hne'

/-- **A conjugate pair of nonreal poles contributes no boundary atom.** -/
theorem tendsto_integral_conjPairKernel {ρ : ℂ} (hρ : ρ.im ≠ 0) {φ : ℝ → ℝ}
    (hφ : Integrable φ) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ, φ t * conjPairKernel ρ ε t) (𝓝 0) (𝓝 0) := by
  have habs : (0 : ℝ) < |ρ.im| := abs_pos.mpr hρ
  have hbound : Integrable (fun t : ℝ => (4 / |ρ.im|) * |φ t|) := (hφ.abs).const_mul _
  have hsmall : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), |ε| < |ρ.im| / 2 := by
    have := Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0:ℝ) < |ρ.im| / 2)
    filter_upwards [this] with ε hε
    simpa [Real.dist_eq] using hε
  have hkey : ∀ ε : ℝ, |ε| < |ρ.im| / 2 → (ε - ρ.im ≠ 0 ∧ ε + ρ.im ≠ 0 ∧
      |ε - ρ.im|⁻¹ + |ε + ρ.im|⁻¹ ≤ 4 / |ρ.im|) := by
    intro ε hε
    have hεb : |ε| < |ρ.im| / 2 := hε
    have h1 : |ρ.im| / 2 ≤ |ε - ρ.im| := by
      have hrev : |ρ.im| - |ε| ≤ |ρ.im - ε| := abs_sub_abs_le_abs_sub ρ.im ε
      rw [abs_sub_comm ρ.im ε] at hrev
      linarith
    have h2 : |ρ.im| / 2 ≤ |ε + ρ.im| := by
      have hrev : |ρ.im| - |(-ε)| ≤ |ρ.im - (-ε)| := abs_sub_abs_le_abs_sub ρ.im (-ε)
      rw [abs_neg] at hrev
      have heq : |ρ.im - (-ε)| = |ε + ρ.im| := by
        congr 1
        ring
      rw [heq] at hrev
      linarith
    have hp1 : (0 : ℝ) < |ε - ρ.im| := lt_of_lt_of_le (by positivity) h1
    have hp2 : (0 : ℝ) < |ε + ρ.im| := lt_of_lt_of_le (by positivity) h2
    refine ⟨abs_pos.mp hp1, abs_pos.mp hp2, ?_⟩
    have hi1 : |ε - ρ.im|⁻¹ ≤ (|ρ.im| / 2)⁻¹ := by gcongr
    have hi2 : |ε + ρ.im|⁻¹ ≤ (|ρ.im| / 2)⁻¹ := by gcongr
    have : (|ρ.im| / 2)⁻¹ + (|ρ.im| / 2)⁻¹ = 4 / |ρ.im| := by field_simp; ring
    linarith
  have hlim : Tendsto (fun ε : ℝ => ∫ t : ℝ, φ t * conjPairKernel ρ ε t) (𝓝 0)
      (𝓝 (∫ t : ℝ, φ t * (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => (4 / |ρ.im|) * |φ t|) ?_ ?_ hbound ?_
    · filter_upwards [hsmall] with ε hε
      obtain ⟨h1, h2, _⟩ := hkey ε hε
      exact hφ.aestronglyMeasurable.mul
        (continuous_conjPairKernel_of_ne h1 h2).aestronglyMeasurable
    · filter_upwards [hsmall] with ε hε
      filter_upwards with t
      obtain ⟨h1, h2, h3⟩ := hkey ε hε
      have hk := norm_conjPairKernel_le (ρ := ρ) (ε := ε) (t := t) h1 h2
      rw [Real.norm_eq_abs, abs_mul]
      calc |φ t| * |conjPairKernel ρ ε t| ≤ |φ t| * (4 / |ρ.im|) :=
            mul_le_mul_of_nonneg_left (le_trans hk h3) (abs_nonneg _)
        _ = 4 / |ρ.im| * |φ t| := by ring
    · filter_upwards with t
      have := (tendsto_conjPairKernel hρ t).const_mul (φ t)
      simpa using this
  simpa using hlim


/-! ## Exact positive-shift strip census

At a fixed positive boundary displacement, a conjugate pair does not merely admit a limiting
description. Its full-line mass is classified exactly. A pair below the displaced line contributes
`-2π`; a pair above it contributes zero because the two Cauchy orientations cancel. Thus a fixed
positive shift is an exact transverse-strip census, not a new upper-bound statistic.
-/

private theorem integral_inv_im_shift_pos (gamma d : ℝ) (hd : 0 < d) :
    (∫ t : ℝ, (((t : ℂ) - (gamma : ℂ) + (d : ℂ) * I)⁻¹).im) = -Real.pi := by
  let s : NNReal := ⟨d, hd.le⟩
  have hs : (s : ℝ) = d := rfl
  have hpoint : (fun t : ℝ =>
      (((t : ℂ) - (gamma : ℂ) + (d : ℂ) * I)⁻¹).im) =
      fun t : ℝ => -(Real.pi * cauchyPDFReal gamma s t) := by
    funext t
    linarith [neg_im_inv_eq_cauchyPDFReal hs hd gamma t]
  rw [hpoint, integral_neg, integral_const_mul,
    integral_cauchyPDFReal_eq_one gamma (by
      intro hs0
      have hval := congrArg (fun x : NNReal => (x : ℝ)) hs0
      simp [s] at hval
      linarith)]
  ring

private theorem integral_inv_im_shift_neg (gamma d : ℝ) (hd : d < 0) :
    (∫ t : ℝ, (((t : ℂ) - (gamma : ℂ) + (d : ℂ) * I)⁻¹).im) = Real.pi := by
  have hpoint : (fun t : ℝ =>
      (((t : ℂ) - (gamma : ℂ) + (d : ℂ) * I)⁻¹).im) =
      fun t : ℝ => -((((t : ℂ) - (gamma : ℂ) + ((-d : ℝ) : ℂ) * I)⁻¹).im) := by
    funext t
    have hcoord :
        (t : ℂ) - (gamma : ℂ) + (d : ℂ) * I =
          (starRingEnd ℂ)
            ((t : ℂ) - (gamma : ℂ) + ((-d : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hcoord, ← map_inv₀]
    exact Complex.conj_im _
  rw [hpoint, integral_neg, integral_inv_im_shift_pos gamma (-d) (neg_pos.mpr hd)]
  ring

private theorem conjPairKernel_eq_shifted_inv_im_add
    (rho : ℂ) (eps t : ℝ) :
    conjPairKernel rho eps t =
      (((t : ℂ) - (rho.re : ℂ) + ((eps - rho.im : ℝ) : ℂ) * I)⁻¹).im +
      (((t : ℂ) - (rho.re : ℂ) + ((eps + rho.im : ℝ) : ℂ) * I)⁻¹).im := by
  have hfirst :
      (t : ℂ) + (eps : ℂ) * I - rho =
        (t : ℂ) - (rho.re : ℂ) + ((eps - rho.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hsecond :
      (t : ℂ) + (eps : ℂ) * I - (starRingEnd ℂ) rho =
        (t : ℂ) - (rho.re : ℂ) + ((eps + rho.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [conjPairKernel, hfirst, hsecond, Complex.add_im]

private theorem integrable_inv_im_shift_pos (gamma d : ℝ) (hd : 0 < d) :
    Integrable (fun t : ℝ =>
      (((t : ℂ) - (gamma : ℂ) + (d : ℂ) * I)⁻¹).im) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_inv_im_shift_pos gamma d hd]
  exact neg_ne_zero.mpr Real.pi_ne_zero

private theorem integrable_inv_im_shift_neg (gamma d : ℝ) (hd : d < 0) :
    Integrable (fun t : ℝ =>
      (((t : ℂ) - (gamma : ℂ) + (d : ℂ) * I)⁻¹).im) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_inv_im_shift_neg gamma d hd]
  exact Real.pi_ne_zero

/-- A conjugate pair strictly inside a positive displaced line has exact full-line mass `-2π`. -/
theorem integral_conjPairKernel_eq_neg_two_pi_of_abs_im_lt
    (rho : ℂ) {eps : ℝ} (hdepth : |rho.im| < eps) :
    (∫ t : ℝ, conjPairKernel rho eps t) = -2 * Real.pi := by
  have hminus : 0 < eps - rho.im := by
    have hle : rho.im ≤ |rho.im| := le_abs_self _
    linarith
  have hplus : 0 < eps + rho.im := by
    have hle : -rho.im ≤ |rho.im| := neg_le_abs _
    linarith
  rw [show (fun t : ℝ => conjPairKernel rho eps t) =
      (fun t : ℝ =>
        (((t : ℂ) - (rho.re : ℂ) + ((eps - rho.im : ℝ) : ℂ) * I)⁻¹).im) +
      (fun t : ℝ =>
        (((t : ℂ) - (rho.re : ℂ) + ((eps + rho.im : ℝ) : ℂ) * I)⁻¹).im) by
    funext t
    exact conjPairKernel_eq_shifted_inv_im_add rho eps t]
  change (∫ t : ℝ,
      (((t : ℂ) - (rho.re : ℂ) + ((eps - rho.im : ℝ) : ℂ) * I)⁻¹).im +
      (((t : ℂ) - (rho.re : ℂ) + ((eps + rho.im : ℝ) : ℂ) * I)⁻¹).im) = _
  rw [integral_add
    (integrable_inv_im_shift_pos rho.re (eps - rho.im) hminus)
    (integrable_inv_im_shift_pos rho.re (eps + rho.im) hplus),
    integral_inv_im_shift_pos rho.re (eps - rho.im) hminus,
    integral_inv_im_shift_pos rho.re (eps + rho.im) hplus]
  ring

/-- A conjugate pair strictly outside a positive displaced line has zero full-line mass. -/
theorem integral_conjPairKernel_eq_zero_of_lt_abs_im
    (rho : ℂ) {eps : ℝ} (heps : 0 < eps) (hdepth : eps < |rho.im|) :
    (∫ t : ℝ, conjPairKernel rho eps t) = 0 := by
  rw [show (fun t : ℝ => conjPairKernel rho eps t) =
      (fun t : ℝ =>
        (((t : ℂ) - (rho.re : ℂ) + ((eps - rho.im : ℝ) : ℂ) * I)⁻¹).im) +
      (fun t : ℝ =>
        (((t : ℂ) - (rho.re : ℂ) + ((eps + rho.im : ℝ) : ℂ) * I)⁻¹).im) by
    funext t
    exact conjPairKernel_eq_shifted_inv_im_add rho eps t]
  change (∫ t : ℝ,
      (((t : ℂ) - (rho.re : ℂ) + ((eps - rho.im : ℝ) : ℂ) * I)⁻¹).im +
      (((t : ℂ) - (rho.re : ℂ) + ((eps + rho.im : ℝ) : ℂ) * I)⁻¹).im) = _
  by_cases hb : 0 ≤ rho.im
  · have habs : |rho.im| = rho.im := abs_of_nonneg hb
    have hminus : eps - rho.im < 0 := by linarith
    have hplus : 0 < eps + rho.im := by linarith
    rw [integral_add
      (integrable_inv_im_shift_neg rho.re (eps - rho.im) hminus)
      (integrable_inv_im_shift_pos rho.re (eps + rho.im) hplus),
      integral_inv_im_shift_neg rho.re (eps - rho.im) hminus,
      integral_inv_im_shift_pos rho.re (eps + rho.im) hplus]
    ring
  · have hbneg : rho.im < 0 := lt_of_not_ge hb
    have habs : |rho.im| = -rho.im := abs_of_neg hbneg
    have hminus : 0 < eps - rho.im := by linarith
    have hplus : eps + rho.im < 0 := by linarith
    rw [integral_add
      (integrable_inv_im_shift_pos rho.re (eps - rho.im) hminus)
      (integrable_inv_im_shift_neg rho.re (eps + rho.im) hplus),
      integral_inv_im_shift_pos rho.re (eps - rho.im) hminus,
      integral_inv_im_shift_neg rho.re (eps + rho.im) hplus]
    ring


end GaloisForLFunctions.HTGeometry

end
