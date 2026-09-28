import GaloisForLFunctions.HTGeometry.FirstOrderRepeatedRegularValue
import GaloisForLFunctions.HTGeometry.CasoratiWeierstrassAtInfinity
import GaloisForLFunctions.HTGeometry.FirstOrderAlgebraicStripPeriodicity

/-!
# A transcendental entire solution of an autonomous first-order equation is periodic

Let `f` be transcendental entire with `P(f, f') = 0` for a nonzero `P ∈ ℂ[X][Y]`.

* A relation `Q` of least degree in `Y` has `∂_Y Q (f, f') ≢ 0`; together with `f' ≢ 0` the
  "bad" points, where `f' = 0` or `∂_Y Q (f, f') = 0`, do not accumulate.
* By Casorati–Weierstrass `f` has dense image near infinity, so there are two distinct good points
  with the same value and the same derivative.  Local uniqueness for `Q(u, u') = 0` makes the
  difference of the two points a period of `f`.
* An entire function with two `ℝ`-linearly independent periods is bounded on a compact period
  parallelogram, hence constant.
-/

open Filter Topology Metric Set Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

variable {f : ℂ → ℂ}

theorem TranscendentalEntire.exists_ne {f : ℂ → ℂ} (hf : TranscendentalEntire f) :
    ∃ z₁ z₂ : ℂ, f z₁ ≠ f z₂ := by
  by_contra h
  push Not at h
  exact hf.2 ⟨Polynomial.C (f 0), fun z => by simp [h z 0]⟩

theorem TranscendentalEntire.analyticOnNhd (hf : TranscendentalEntire f) :
    AnalyticOnNhd ℂ f univ :=
  hf.1.differentiableOn.analyticOnNhd isOpen_univ

theorem TranscendentalEntire.analyticOnNhd_deriv (hf : TranscendentalEntire f) :
    AnalyticOnNhd ℂ (deriv f) univ :=
  (hf.1.differentiableOn.deriv isOpen_univ).analyticOnNhd isOpen_univ

/-- **A relation of least degree for a transcendental entire function.** -/
theorem exists_entire_relation_derivative_ne_zero (hf : TranscendentalEntire f)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0)
    (hrel : ∀ z, relEval P (f z) (deriv f z) = 0) :
    ∃ Q : Polynomial (Polynomial ℂ), Q ≠ 0 ∧ (∀ z, relEval Q (f z) (deriv f z) = 0) ∧
      ∃ z, relEval (derivative Q) (f z) (deriv f z) ≠ 0 := by
  have hnc : ∃ z₁ ∈ imStrip 1, ∃ z₂ ∈ imStrip 1, f z₁ ≠ f z₂ := by
    by_contra hall
    push Not at hall
    obtain ⟨w₁, w₂, hw⟩ := hf.exists_ne
    have h0 : (0 : ℂ) ∈ imStrip 1 := by simp [mem_imStrip]
    have hconst : EqOn (fun z => f z - f 0) 0 univ := by
      refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun z _ => (hf.analyticOnNhd z (mem_univ z)).sub analyticAt_const) isPreconnected_univ
        (mem_univ 0) ?_
      filter_upwards [(isOpen_imStrip 1).mem_nhds h0] with z hz
      simp [hall z hz 0 h0]
    have h1 := hconst (mem_univ w₁)
    have h2 := hconst (mem_univ w₂)
    simp only [Pi.zero_apply, sub_eq_zero] at h1 h2
    exact hw (h1.trans h2.symm)
  obtain ⟨Q, hQrel, z₀, -, hz₀⟩ := exists_relation_derivative_ne_zero (η := 1)
    hf.1.differentiableOn hnc hP fun z _ => hrel z
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp [relEval] at hz₀
  refine ⟨Q, hQ0, fun z => ?_, z₀, hz₀⟩
  have hana : AnalyticOnNhd ℂ (fun z => relEval Q (f z) (deriv f z)) univ :=
    fun z _ => analyticAt_relEval Q (hf.analyticOnNhd z (mem_univ z))
      (hf.analyticOnNhd_deriv z (mem_univ z))
  have h0 : (0 : ℂ) ∈ imStrip 1 := by simp [mem_imStrip]
  have := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 0)
    (by filter_upwards [(isOpen_imStrip 1).mem_nhds h0] with z hz using hQrel z hz)
  simpa using this (mem_univ z)

/-- The product `f' · ∂_Y Q (f, f')` is analytic and does not vanish identically. -/
theorem exists_badness_ne_zero (hf : TranscendentalEntire f) {Q : Polynomial (Polynomial ℂ)}
    (hQ : ∃ z, relEval (derivative Q) (f z) (deriv f z) ≠ 0) :
    ∃ z, deriv f z * relEval (derivative Q) (f z) (deriv f z) ≠ 0 := by
  have hA := hf.analyticOnNhd_deriv
  have hB : AnalyticOnNhd ℂ (fun z => relEval (derivative Q) (f z) (deriv f z)) univ :=
    fun z _ => analyticAt_relEval _ (hf.analyticOnNhd z (mem_univ z)) (hA z (mem_univ z))
  obtain ⟨z₁, hz₁⟩ : ∃ z, deriv f z ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨w₁, w₂, hw⟩ := hf.exists_ne
    exact hw (is_const_of_deriv_eq_zero hf.1 h w₁ w₂)
  by_contra hall
  push Not at hall
  obtain ⟨z₂, hz₂⟩ := hQ
  have hnear : ∀ᶠ z in 𝓝 z₁, deriv f z ≠ 0 := (hA z₁ (mem_univ _)).continuousAt.eventually_ne hz₁
  have hBz : ∀ᶠ z in 𝓝 z₁, relEval (derivative Q) (f z) (deriv f z) = 0 := by
    filter_upwards [hnear] with z hz
    exact (mul_eq_zero.mp (hall z)).resolve_left hz
  exact hz₂ (hB.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z₁)
    hBz (mem_univ z₂))

/-- **Bad points do not accumulate.** -/
theorem eventually_relGood_of_entire (hf : TranscendentalEntire f) {Q : Polynomial (Polynomial ℂ)}
    (hQ : ∃ z, relEval (derivative Q) (f z) (deriv f z) ≠ 0) (z₀ : ℂ) :
    ∀ᶠ y in 𝓝[≠] z₀, RelGood f (deriv f) Q y := by
  set B := fun z => deriv f z * relEval (derivative Q) (f z) (deriv f z) with hBdef
  have hBa : AnalyticOnNhd ℂ B univ := fun z _ =>
    (hf.analyticOnNhd_deriv z (mem_univ z)).mul
      (analyticAt_relEval _ (hf.analyticOnNhd z (mem_univ z))
        (hf.analyticOnNhd_deriv z (mem_univ z)))
  obtain ⟨z₁, hz₁⟩ := exists_badness_ne_zero hf hQ
  rcases (hBa z₀ (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exfalso
    exact hz₁ (hBa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ z₀) h0 (mem_univ z₁))
  · filter_upwards [hne] with y hy
    exact ⟨left_ne_zero_of_mul hy, right_ne_zero_of_mul hy⟩

/-- **Two equal good jets give a period.**  If `f(z₁) = f(z₂)`, `f'(z₁) = f'(z₂)` and
`∂_Y Q (f(z₁), f'(z₁)) ≠ 0`, then `z₂ - z₁` is a period of `f`. -/
theorem periodic_of_equal_jets (hfd : Differentiable ℂ f) {Q : Polynomial (Polynomial ℂ)}
    (hrel : ∀ z, relEval Q (f z) (deriv f z) = 0) {z₁ z₂ : ℂ} (hval : f z₁ = f z₂)
    (hder : deriv f z₁ = deriv f z₂) (hQ : relEval (derivative Q) (f z₁) (deriv f z₁) ≠ 0) :
    ∀ z, f (z + (z₂ - z₁)) = f z := by
  obtain ⟨δ, hδ, huniq⟩ := eqOn_of_relEval_eq_zero hQ
  have hw : Differentiable ℂ fun z => f (z + (z₂ - z₁)) := hfd.comp (differentiable_id.add_const _)
  have heq := huniq isOpen_univ isPreconnected_univ (mem_univ z₁) hfd.differentiableOn
    hw.differentiableOn (fun z _ => hrel z)
    (fun z _ => by rw [deriv_comp_add_const]; exact hrel _)
    (by simp [hval]) (by simpa using hδ) (by simpa using hδ)
    (by rw [deriv_comp_add_const]; simpa [← hder] using hδ)
  intro z
  exact (heq (mem_univ z)).symm

/-- **A transcendental entire solution of an autonomous first-order equation is periodic.** -/
theorem exists_period_of_autonomous_firstOrder (hf : TranscendentalEntire f)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0) (hrel : ∀ z, relEval P (f z) (deriv f z) = 0) :
    ∃ ω : ℂ, ω ≠ 0 ∧ ∀ z, f (z + ω) = f z := by
  obtain ⟨Q, hQ0, hQrel, hQ⟩ := exists_entire_relation_derivative_ne_zero hf hP hrel
  obtain ⟨z₁, z₂, -, hsep, -, hval, hder, hgood⟩ :=
    exists_repeated_relGood_value (φ := f) (D := deriv f) (R₀ := -1)
      hf.1.differentiableOn hQ0 (fun z _ => hQrel z)
      (fun z _ => eventually_relGood_of_entire hf hQ z)
      (dense_image_of_transcendentalEntire hf) 0
  refine ⟨z₂ - z₁, fun h => ?_, periodic_of_equal_jets hf.1 hQrel hval hder hgood.2⟩
  rw [sub_eq_zero] at h
  rw [h] at hsep
  linarith

/-! ## Two independent periods -/

/-- **An entire function with two `ℝ`-independent periods is constant.** -/
theorem eq_const_of_two_periods (hfd : Differentiable ℂ f) {ω₁ ω₂ : ℂ} (hω₁ : ω₁ ≠ 0)
    (hind : (ω₂ / ω₁).im ≠ 0) (h₁ : ∀ z, f (z + ω₁) = f z) (h₂ : ∀ z, f (z + ω₂) = f z) :
    ∀ z w, f z = f w := by
  set τ := ω₂ / ω₁ with hτ
  have hp₁ : Function.Periodic f ω₁ := h₁
  have hp₂ : Function.Periodic f ω₂ := h₂
  set K : Set ℂ := (fun p : ℝ × ℝ => ω₁ * ((p.1 : ℂ) + (p.2 : ℂ) * τ)) '' (Icc 0 1 ×ˢ Icc 0 1)
    with hK
  have hKc : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hred : ∀ z, ∃ y ∈ K, f z = f y := by
    intro z
    set u := z / ω₁
    set b : ℝ := u.im / τ.im
    set a : ℝ := u.re - b * τ.re
    have hu : u = (a : ℂ) + (b : ℂ) * τ := by
      apply Complex.ext
      · simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero, a, b]
        ring
      · simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add, b]
        field_simp
    refine ⟨ω₁ * (((a - ⌊a⌋ : ℝ) : ℂ) + ((b - ⌊b⌋ : ℝ) : ℂ) * τ),
      ⟨(a - ⌊a⌋, b - ⌊b⌋), ⟨⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩,
        ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩⟩, rfl⟩, ?_⟩
    have hz : z = ω₁ * (((a - ⌊a⌋ : ℝ) : ℂ) + ((b - ⌊b⌋ : ℝ) : ℂ) * τ)
        + ((⌊a⌋ : ℤ) : ℂ) * ω₁ + ((⌊b⌋ : ℤ) : ℂ) * ω₂ := by
      have hz' : z = ω₁ * u := by rw [mul_div_cancel₀ _ hω₁]
      rw [hz', hu, hτ]
      push_cast
      field_simp
      ring
    rw [hz, hp₂.int_mul, hp₁.int_mul]
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hfd.continuous.continuousOn
  have hbdd : Bornology.IsBounded (range f) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨B, ?_⟩
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hyK, hy⟩ := hred z
    rw [hy]
    exact hB y hyK
  exact hfd.apply_eq_apply_of_bounded hbdd

end GaloisForLFunctions.HTGeometry
