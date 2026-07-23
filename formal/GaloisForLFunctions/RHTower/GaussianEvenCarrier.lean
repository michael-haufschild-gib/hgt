import GaloisForLFunctions.RHTower.ConstrainedProlateOperator
import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import GaloisForLFunctions.HTGeometry.TruncatedFixedVector
import GaloisForLFunctions.RHTower.ConstrainedProlateTrueLeakage
import GaloisForLFunctions.HTGeometry.GaussianTailBound

/-!
# The Gaussian inside the even prolate carrier

The prolate trial functions live in the project's even `L²` carrier, cut down to the aperture.
This module places the Gaussian there: its `L²` class is even, hence a member of
`evenSubspace`, and the even Fourier transform fixes it, because that transform is the
restriction of the `L²` Fourier transform which fixes the Gaussian.

The Gaussian is even pointwise since it depends on `x` only through `x²`, and evenness of an
`L²` class is evenness of any representative almost everywhere; the Schwartz representative is
continuous, so its own evenness transports.
-/

open MeasureTheory
open scoped Real

noncomputable section

namespace RHTower

/-- The `L²` class of the Gaussian. -/
def gaussL2 : SoninL2 := GaloisForLFunctions.gaussianSchwartz.toLp 2

theorem gaussL2_coeFn :
    (gaussL2 : ℝ → ℂ) =ᵐ[volume] fun x => (GaloisForLFunctions.gaussReal x : ℂ) := by
  have h := SchwartzMap.coeFn_toLp GaloisForLFunctions.gaussianSchwartz 2 (μ := volume)
  refine h.trans ?_
  filter_upwards with x
  exact GaloisForLFunctions.gaussianSchwartz_apply x

/-- The Gaussian is even. -/
theorem gaussReal_neg (x : ℝ) : GaloisForLFunctions.gaussReal (-x)
    = GaloisForLFunctions.gaussReal x := by
  unfold GaloisForLFunctions.gaussReal
  congr 1
  ring

/-- **The Gaussian lies in the even carrier.** -/
theorem gaussL2_mem_evenSubspace : gaussL2 ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hneg := gaussL2_coeFn.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae gaussL2, hneg, gaussL2_coeFn] with x href hleft hright
  have hleft' : (gaussL2 : ℝ → ℂ) (-x) = (GaloisForLFunctions.gaussReal (-x) : ℂ) := by
    simpa [Function.comp_apply] using hleft
  rw [href, hleft', hright, gaussReal_neg]

/-- The Gaussian as an element of the even carrier. -/
def gaussEven : evenSubspace := ⟨gaussL2, gaussL2_mem_evenSubspace⟩

@[simp] theorem coe_gaussEven : (gaussEven : SoninL2) = gaussL2 := rfl

/-- **The even Fourier transform fixes the Gaussian.**  The even transform is the restriction of
the `L²` Fourier transform, which fixes the Gaussian's class. -/
theorem evenFourierTransform_gaussEven : evenFourierTransform gaussEven = gaussEven := by
  apply Subtype.ext
  rw [coe_evenFourierTransform_apply, coe_gaussEven]
  exact GaloisForLFunctions.fourier_gaussianSchwartz_toLp

/-- The Gaussian is nonzero in `L²`: its value at the origin is one, and it is continuous. -/
theorem gaussEven_ne_zero : gaussEven ≠ 0 := by
  intro hzero
  have hcoe : gaussL2 = 0 := by
    have := congrArg (fun v : evenSubspace => (v : SoninL2)) hzero
    simpa using this
  have hae : (fun x : ℝ => (GaloisForLFunctions.gaussReal x : ℂ)) =ᵐ[volume] 0 := by
    refine gaussL2_coeFn.symm.trans ?_
    rw [hcoe]
    exact Lp.coeFn_zero _ _ _
  have hpos : ∀ x : ℝ, (GaloisForLFunctions.gaussReal x : ℂ) ≠ 0 := by
    intro x
    simpa using (GaloisForLFunctions.gaussReal_pos x).ne'
  have hvol : (volume : Measure ℝ) = 0 := by
    simpa using hae.mono fun x hx => hpos x hx
  have hIcc : (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1) = 0 := by rw [hvol]; rfl
  rw [Real.volume_Icc] at hIcc
  norm_num at hIcc

/-! ## The aperture cutoff as a star projection on the even carrier -/

/-- The even aperture cutoff is symmetric: it inherits symmetry from the underlying
multiplication by an indicator. -/
theorem evenIndicatorCutoff_symmetric (a : ℝ) (f g : evenSubspace) :
    inner ℂ (evenIndicatorCutoff a f) g = inner ℂ f (evenIndicatorCutoff a g) := by
  have h := indicatorCutoff_symmetric (centralInterval a) (measurableSet_centralInterval a)
    (f : SoninL2) (g : SoninL2)
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_evenIndicatorCutoff_apply,
    coe_evenIndicatorCutoff_apply]
  exact h

theorem evenIndicatorCutoff_apply_apply (a : ℝ) (f : evenSubspace) :
    evenIndicatorCutoff a (evenIndicatorCutoff a f) = evenIndicatorCutoff a f := by
  have h := evenIndicatorCutoff_idempotent a
  rw [IsIdempotentElem] at h
  calc evenIndicatorCutoff a (evenIndicatorCutoff a f)
      = (evenIndicatorCutoff a * evenIndicatorCutoff a) f := rfl
    _ = evenIndicatorCutoff a f := by rw [h]

/-- **The Gaussian trial estimate at the aperture.**  The truncated Gaussian retains at least
`1 − 4θ²` of its squared norm under the compressed Fourier block, where `θ` bounds the relative
truncation error.  This is `evenProlateLeakageValue_le_of_form_trial`'s hypothesis for the
one-dimensional trial space spanned by the truncated Gaussian. -/
theorem gaussEven_concentration (a : ℝ) {θ : ℝ}
    (hθ : ‖gaussEven - evenIndicatorCutoff a gaussEven‖
      ≤ θ * ‖evenIndicatorCutoff a gaussEven‖) :
    (1 - 4 * θ ^ 2) * ‖evenIndicatorCutoff a gaussEven‖ ^ 2
      ≤ ‖evenIndicatorCutoff a (evenFourierTransform (evenIndicatorCutoff a gaussEven))‖ ^ 2 :=
  ContinuousLinearMap.norm_sq_proj_unitary_proj_ge_of_rel
    (fun x => evenFourierTransform_isometry x)
    (evenIndicatorCutoff_apply_apply a)
    (evenIndicatorCutoff_symmetric a)
    evenFourierTransform_gaussEven hθ

/-- The compressed Fourier block applied to the truncated Gaussian is the doubly-cut
transform, by idempotency of the cutoff. -/
theorem evenTimeBandFourier_gaussEven_cut (a : ℝ) :
    evenTimeBandFourier a (evenIndicatorCutoff a gaussEven)
      = evenIndicatorCutoff a (evenFourierTransform (evenIndicatorCutoff a gaussEven)) := by
  rw [evenTimeBandFourier_eq_mul]
  change evenIndicatorCutoff a (evenFourierTransform
    (evenIndicatorCutoff a (evenIndicatorCutoff a gaussEven))) = _
  rw [evenIndicatorCutoff_apply_apply]

/-- **The truncated Gaussian is a concentrated trial vector for the compressed Fourier block.**
Relative truncation error `θ` gives concentration deficit `4θ²` — the exact hypothesis shape of
`evenProlateLeakageValue_le_of_form_trial`. -/
theorem gaussEven_timeBand_concentration (a : ℝ) {θ : ℝ}
    (hθ : ‖gaussEven - evenIndicatorCutoff a gaussEven‖
      ≤ θ * ‖evenIndicatorCutoff a gaussEven‖) :
    (1 - 4 * θ ^ 2) * ‖evenIndicatorCutoff a gaussEven‖ ^ 2
      ≤ ‖evenTimeBandFourier a (evenIndicatorCutoff a gaussEven)‖ ^ 2 := by
  rw [evenTimeBandFourier_gaussEven_cut]
  exact gaussEven_concentration a hθ

/-- The concentration estimate is homogeneous, so it holds on the whole line spanned by the
truncated Gaussian — the one-dimensional trial space. -/
theorem gaussEven_span_concentration (a : ℝ) {θ : ℝ}
    (hθ : ‖gaussEven - evenIndicatorCutoff a gaussEven‖
      ≤ θ * ‖evenIndicatorCutoff a gaussEven‖)
    (f : evenSubspace)
    (hf : f ∈ Submodule.span ℂ {evenIndicatorCutoff a gaussEven}) :
    (1 - 4 * θ ^ 2) * ‖f‖ ^ 2 ≤ ‖evenTimeBandFourier a f‖ ^ 2 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf
  have hbase := gaussEven_timeBand_concentration a hθ
  rw [← hc, map_smul, norm_smul, norm_smul]
  have hcn : (0 : ℝ) ≤ ‖c‖ ^ 2 := sq_nonneg _
  calc (1 - 4 * θ ^ 2) * (‖c‖ * ‖evenIndicatorCutoff a gaussEven‖) ^ 2
      = ‖c‖ ^ 2 * ((1 - 4 * θ ^ 2) * ‖evenIndicatorCutoff a gaussEven‖ ^ 2) := by ring
    _ ≤ ‖c‖ ^ 2 * ‖evenTimeBandFourier a (evenIndicatorCutoff a gaussEven)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hbase hcn
    _ = (‖c‖ * ‖evenTimeBandFourier a (evenIndicatorCutoff a gaussEven)‖) ^ 2 := by ring

/-! ## Norms as integrals -/

/-- The `L²` norm squared is the integral of the pointwise squared norm. -/
theorem norm_sq_eq_integral (f : SoninL2) :
    ‖f‖ ^ 2 = ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 := by
  have h2 := MeasureTheory.L2.inner_def (𝕜 := ℂ) f f
  rw [inner_self_eq_norm_sq_to_K] at h2
  have h3 : ∀ a : ℝ, inner ℂ ((f : ℝ → ℂ) a) ((f : ℝ → ℂ) a)
      = ((‖(f : ℝ → ℂ) a‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [h3] at h2
  rw [integral_complex_ofReal] at h2
  have h4 : ((‖f‖ ^ 2 : ℝ) : ℂ) = ((∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact h2
  exact_mod_cast h4

/-- The truncation error of the Gaussian is exactly its `L²` mass outside the aperture. -/
theorem norm_sq_gaussEven_sub_cut (a : ℝ) :
    ‖gaussEven - evenIndicatorCutoff a gaussEven‖ ^ 2
      = ∫ x in (centralInterval a)ᶜ, Real.exp (-(2 * π * x ^ 2)) := by
  have hcoe : ((gaussEven - evenIndicatorCutoff a gaussEven : evenSubspace) : SoninL2)
      = gaussL2 - indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) gaussL2 := rfl
  have hnorm : ‖gaussEven - evenIndicatorCutoff a gaussEven‖
      = ‖gaussL2 - indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) gaussL2‖ := rfl
  rw [hnorm, norm_sq_eq_integral]
  have hae : ((gaussL2 - indicatorCutoff (centralInterval a)
      (measurableSet_centralInterval a) gaussL2 : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] fun x => (centralInterval a)ᶜ.indicator
        (fun y => (GaloisForLFunctions.gaussReal y : ℂ)) x := by
    filter_upwards [Lp.coeFn_sub gaussL2 (indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) gaussL2),
      indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) gaussL2,
      gaussL2_coeFn] with x hsub hcut hg
    rw [hsub, Pi.sub_apply, hcut]
    by_cases hx : x ∈ centralInterval a
    · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx), sub_self]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx), sub_zero, hg]
  rw [integral_congr_ae (hae.mono fun x hx => by rw [hx])]
  rw [← integral_indicator (measurableSet_centralInterval a).compl]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ (centralInterval a)ᶜ
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    unfold GaloisForLFunctions.gaussReal
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      sq, ← Real.exp_add]
    congr 1
    ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-! ## The explicit truncation error -/

/-- **The truncation error of the Gaussian is explicitly exponentially small.**  Splitting the
complement of the aperture into two rays and reflecting the left one onto the right, the tail is
twice the ray bound. -/
theorem norm_sq_gaussEven_sub_cut_le {a : ℝ} (ha : 0 < a) :
    ‖gaussEven - evenIndicatorCutoff a gaussEven‖ ^ 2
      ≤ 2 * (Real.exp (-(2 * π * a ^ 2)) / (4 * π * a)) := by
  have hgi : Integrable (fun x : ℝ => Real.exp (-(2 * π * x ^ 2))) volume := by
    have hb : (0 : ℝ) < 2 * π := by positivity
    refine (integrable_exp_neg_mul_sq hb).congr ?_
    filter_upwards with x
    ring_nf
  have hsplit : (centralInterval a)ᶜ = Set.Iio (-a) ∪ Set.Ioi a := by
    ext x
    simp only [centralInterval, Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio,
      Set.mem_Ioi, not_and_or, not_le]
  have hdisj : Disjoint (Set.Iio (-a)) (Set.Ioi a) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_Iio] at hx
    simp only [Set.mem_Ioi] at hx'
    linarith
  rw [norm_sq_gaussEven_sub_cut, hsplit,
    setIntegral_union hdisj measurableSet_Ioi hgi.integrableOn hgi.integrableOn]
  have hIioIic : ∫ x in Set.Iio (-a), Real.exp (-(2 * π * x ^ 2))
      = ∫ x in Set.Iic (-a), Real.exp (-(2 * π * x ^ 2)) :=
    setIntegral_congr_set Iio_ae_eq_Iic
  have hrefl : ∫ x in Set.Iic (-a), Real.exp (-(2 * π * x ^ 2))
      = ∫ x in Set.Ioi a, Real.exp (-(2 * π * x ^ 2)) := by
    rw [← integral_comp_neg_Ioi a (fun x : ℝ => Real.exp (-(2 * π * x ^ 2)))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp
  rw [hIioIic, hrefl]
  have hray := GaloisForLFunctions.integral_Ioi_gauss_sq_le ha
  linarith

/-! ## The ground leakage bound for the true operator -/

/-- Every positive aperture retains a nonzero Gaussian trial vector. This discharges the
nonvanishing premise of the one-dimensional Courant--Fischer bound on the complete physical
aperture ray. -/
theorem evenIndicatorCutoff_gaussEven_ne_zero {a : ℝ} (ha : 0 < a) :
    evenIndicatorCutoff a gaussEven ≠ 0 := by
  intro hzero
  have hcutzero : indicatorCutoff (centralInterval a)
      (measurableSet_centralInterval a) gaussL2 = 0 := by
    have h := congrArg (fun v : evenSubspace => (v : SoninL2)) hzero
    simpa using h
  have hzeroae :
      ((indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        gaussL2 : SoninL2) : ℝ → ℂ) =ᵐ[volume] 0 := by
    rw [hcutzero]
    exact Lp.coeFn_zero _ _ _
  have hnotmem : ∀ᵐ x : ℝ ∂volume, x ∉ centralInterval a := by
    filter_upwards [indicatorCutoff_ae (centralInterval a)
        (measurableSet_centralInterval a) gaussL2,
      gaussL2_coeFn, hzeroae] with x hcut hgauss hzeroPoint
    intro hx
    have hz : (GaloisForLFunctions.gaussReal x : ℂ) = 0 := by
      rw [hcut, Set.indicator_of_mem hx, hgauss] at hzeroPoint
      exact hzeroPoint
    exact (Complex.ofReal_ne_zero.mpr
      (GaloisForLFunctions.gaussReal_pos x).ne') hz
  have hpositive : (volume : Measure ℝ) (centralInterval a) ≠ 0 := by
    rw [centralInterval, Real.volume_Icc, ENNReal.ofReal_ne_zero_iff]
    linarith
  exact hpositive (measure_eq_zero_iff_ae_notMem.mpr hnotmem)

/-- **The true ground leakage is bounded by the Gaussian truncation deficit.**  The truncated
Gaussian spans a one-dimensional trial space, so Courant–Fischer caps the zeroth leakage of the
actual compressed Fourier block by `4θ²`, where `θ` is the relative truncation error of the
Gaussian at the aperture. -/
theorem evenProlateLeakageValue_zero_le (a : ℝ) {θ : ℝ}
    (hne : evenIndicatorCutoff a gaussEven ≠ 0)
    (hθ : ‖gaussEven - evenIndicatorCutoff a gaussEven‖
      ≤ θ * ‖evenIndicatorCutoff a gaussEven‖) :
    evenProlateLeakageValue a 0 ≤ 4 * θ ^ 2 := by
  have hdim : 0 < Module.finrank ℂ
      (Submodule.span ℂ ({evenIndicatorCutoff a gaussEven} : Set evenSubspace)) := by
    rw [finrank_span_singleton hne]
    norm_num
  have h := evenProlateLeakageValue_le_of_form_trial a 0
    (Submodule.span ℂ ({evenIndicatorCutoff a gaussEven} : Set evenSubspace)) hdim
    (ε := 4 * θ ^ 2) ?_
  · exact h
  · intro f hf
    have := gaussEven_span_concentration a hθ f hf
    have hrw : (1 : ℝ) - 4 * θ ^ 2 = 1 - 4 * θ ^ 2 := rfl
    linarith [this]

/-- Positive aperture alone discharges the nonzero-trial hypothesis in the Gaussian leakage
bound. -/
theorem evenProlateLeakageValue_zero_le_of_pos
    {a : ℝ} (ha : 0 < a) {θ : ℝ}
    (hθ : ‖gaussEven - evenIndicatorCutoff a gaussEven‖
      ≤ θ * ‖evenIndicatorCutoff a gaussEven‖) :
    evenProlateLeakageValue a 0 ≤ 4 * θ ^ 2 := by
  exact evenProlateLeakageValue_zero_le a
    (evenIndicatorCutoff_gaussEven_ne_zero ha) hθ

/-- **Unconditional Gaussian relative-tail bound.** At every positive aperture, true ground
leakage is at most four times the squared relative Gaussian truncation error. No separate
nonvanishing or calibration witness is required. -/
theorem evenProlateLeakageValue_zero_le_gaussianRelativeTail
    {a : ℝ} (ha : 0 < a) :
    evenProlateLeakageValue a 0 ≤
      4 * (‖gaussEven - evenIndicatorCutoff a gaussEven‖ /
        ‖evenIndicatorCutoff a gaussEven‖) ^ 2 := by
  have hne := evenIndicatorCutoff_gaussEven_ne_zero ha
  have hnorm : ‖evenIndicatorCutoff a gaussEven‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hne
  apply evenProlateLeakageValue_zero_le_of_pos ha
  rw [div_mul_cancel₀ _ hnorm]

/-! ## The true ground leakage vanishes as the aperture grows -/

/-- The truncated Gaussian's mass is the total mass minus the tail. -/
theorem norm_sq_cut_gaussEven (a : ℝ) :
    ‖evenIndicatorCutoff a gaussEven‖ ^ 2
      = ‖gaussEven‖ ^ 2 - ‖gaussEven - evenIndicatorCutoff a gaussEven‖ ^ 2 := by
  have h := ContinuousLinearMap.norm_sq_eq_of_isIdempotent_symmetric
    (evenIndicatorCutoff_apply_apply a) (evenIndicatorCutoff_symmetric a) gaussEven
  linarith

/-- The truncation error vanishes as the aperture grows. -/
theorem norm_sq_gaussEven_sub_cut_tendsto_zero :
    Filter.Tendsto (fun a : ℝ => ‖gaussEven - evenIndicatorCutoff a gaussEven‖ ^ 2)
      Filter.atTop (nhds 0) := by
  have hbound : Filter.Tendsto
      (fun a : ℝ => 2 * (Real.exp (-(2 * π * a ^ 2)) / (4 * π * a)))
      Filter.atTop (nhds 0) := by
    have hexp := GaloisForLFunctions.tendsto_gaussExp_atTop
    have hinv : Filter.Tendsto (fun a : ℝ => (4 * π * a)⁻¹) Filter.atTop (nhds 0) := by
      have hup : Filter.Tendsto (fun a : ℝ => 4 * π * a) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id
      exact hup.inv_tendsto_atTop
    have hmul := (hexp.mul hinv).const_mul 2
    simp only [mul_zero] at hmul
    refine hmul.congr fun a => ?_
    rw [div_eq_mul_inv]
  refine squeeze_zero' (Filter.Eventually.of_forall fun a => sq_nonneg _) ?_ hbound
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a ha
  exact norm_sq_gaussEven_sub_cut_le ha

/-- **The true ground leakage of the compressed Fourier block vanishes as the aperture grows.**
The truncated Gaussian is an admissible one-dimensional trial space whose concentration deficit
tends to zero, so Courant–Fischer forces `d_0(a) → 0`. -/
theorem evenProlateLeakageValue_zero_tendsto_zero :
    Filter.Tendsto (fun a : ℝ => evenProlateLeakageValue a 0) Filter.atTop (nhds 0) := by
  have hgpos : (0 : ℝ) < ‖gaussEven‖ ^ 2 := by
    have := gaussEven_ne_zero
    positivity
  set K := ‖gaussEven‖ ^ 2 with hK
  have htail := norm_sq_gaussEven_sub_cut_tendsto_zero
  -- eventually the tail is below half the total mass
  have hhalf : ∀ᶠ a : ℝ in Filter.atTop,
      ‖gaussEven - evenIndicatorCutoff a gaussEven‖ ^ 2 < K / 2 :=
    htail.eventually (eventually_lt_nhds (by linarith))
  have hbound : Filter.Tendsto
      (fun a : ℝ => 4 * (‖gaussEven - evenIndicatorCutoff a gaussEven‖ ^ 2 / (K / 2)))
      Filter.atTop (nhds 0) := by
    have := (htail.div_const (K / 2)).const_mul 4
    simpa using this
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a ha
    exact evenProlateLeakageValue_nonneg a 0
  · filter_upwards [hhalf, Filter.eventually_gt_atTop (0 : ℝ)] with a hlt ha
    set τ := ‖gaussEven - evenIndicatorCutoff a gaussEven‖ ^ 2 with hτ
    have hcut : ‖evenIndicatorCutoff a gaussEven‖ ^ 2 = K - τ := norm_sq_cut_gaussEven a
    have hmain := evenProlateLeakageValue_zero_le_gaussianRelativeTail ha
    rw [div_pow, ← hτ, hcut] at hmain
    have hmono : τ / (K - τ) ≤ τ / (K / 2) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
    linarith

/-- **Explicit exponential upper bound on the true ground leakage.**  Eventually
`d_0(a) ≤ (8/‖g‖²)·e^{−2πa²}/(4πa)`: the leakage of the actual compressed Fourier block is
exponentially small in `a²`. -/
theorem evenProlateLeakageValue_zero_le_exp :
    ∀ᶠ a : ℝ in Filter.atTop,
      evenProlateLeakageValue a 0
        ≤ (16 / ‖gaussEven‖ ^ 2) * (Real.exp (-(2 * π * a ^ 2)) / (4 * π * a)) := by
  have hgpos : (0 : ℝ) < ‖gaussEven‖ ^ 2 := by
    have := gaussEven_ne_zero
    positivity
  set K := ‖gaussEven‖ ^ 2 with hK
  have hhalf : ∀ᶠ a : ℝ in Filter.atTop,
      ‖gaussEven - evenIndicatorCutoff a gaussEven‖ ^ 2 < K / 2 :=
    norm_sq_gaussEven_sub_cut_tendsto_zero.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hhalf, Filter.eventually_gt_atTop (0 : ℝ)] with a hlt ha
  set τ := ‖gaussEven - evenIndicatorCutoff a gaussEven‖ ^ 2 with hτ
  have hcut : ‖evenIndicatorCutoff a gaussEven‖ ^ 2 = K - τ := norm_sq_cut_gaussEven a
  have hmain := evenProlateLeakageValue_zero_le_gaussianRelativeTail ha
  rw [div_pow, ← hτ, hcut] at hmain
  have hstep : τ / (K - τ) ≤ τ / (K / 2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
  have htail := norm_sq_gaussEven_sub_cut_le ha
  have hfinal : 4 * (τ / (K / 2)) ≤ (16 / K) * (Real.exp (-(2 * π * a ^ 2)) / (4 * π * a)) := by
    rw [div_div_eq_mul_div, show (4 : ℝ) * (τ * 2 / K) = (8 / K) * τ by ring]
    calc (8 / K) * τ
        ≤ (8 / K) * (2 * (Real.exp (-(2 * π * a ^ 2)) / (4 * π * a))) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = (16 / K) * (Real.exp (-(2 * π * a ^ 2)) / (4 * π * a)) := by ring
  linarith [hmain, hstep, hfinal]

end RHTower
