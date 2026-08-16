import Mathlib

/-!
# The second moment controls the tail of the integral

A function with a finite second moment has uniformly small integral tails:

```text
∫_{ξ > K} |f|  ≤  sqrt( (∫_{ξ > K} ξ² f²) / K ) .
```

This is the Cauchy–Schwarz bound `∫ |f| = ∫ (1/ξ)(ξ|f|) ≤ ‖1/ξ‖₂ ‖ξ f‖₂`, but it is obtained here
without any Hölder machinery: the pointwise arithmetic–geometric inequality

```text
|f ξ|  ≤  (t/2)(1/ξ²) + (1/(2t)) ξ² f(ξ)²          (t > 0, ξ > 0)
```

is integrated term by term against `∫_{ξ > K} ξ^(−2) = 1/K`, and the free parameter is then set to
`t = sqrt(N K)`, at which the two halves of the bound coincide.

For a family of profiles with a uniform second-moment bound this makes the tails of `∫ f` uniformly
small, which is exactly what turns locally uniform convergence of the family into convergence of the
integrals — the coordinate half of a prolate-to-Hermite limit.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-- The tail integral of `ξ^(−2)`. -/
theorem integral_Ioi_one_div_sq {K : ℝ} (hK : 0 < K) :
    ∫ ξ in Ioi K, 1 / ξ ^ 2 = 1 / K := by
  have hcongr : ∀ ξ ∈ Ioi K, (1 : ℝ) / ξ ^ 2 = ξ ^ (-2 : ℝ) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := lt_trans hK hξ
    rw [Real.rpow_neg hξ0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_Ioi_rpow_of_lt (by norm_num) hK]
  norm_num
  rw [Real.rpow_neg_one]

/-- The tail of `ξ^(−2)` is integrable. -/
theorem integrableOn_Ioi_one_div_sq {K : ℝ} (hK : 0 < K) :
    IntegrableOn (fun ξ : ℝ => 1 / ξ ^ 2) (Ioi K) := by
  have hcongr : ∀ ξ ∈ Ioi K, (1 : ℝ) / ξ ^ 2 = ξ ^ (-2 : ℝ) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := lt_trans hK hξ
    rw [Real.rpow_neg hξ0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div]
  refine (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hK).congr_fun ?_
    measurableSet_Ioi
  intro ξ hξ
  exact (hcongr ξ hξ).symm

/-- **The pointwise arithmetic–geometric split.** -/
theorem abs_le_secondMoment_split {f : ℝ → ℝ} {ξ t : ℝ} (ht : 0 < t) (hξ : 0 < ξ) :
    |f ξ| ≤ t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2) := by
  have habs : |f ξ| ^ 2 = f ξ ^ 2 := sq_abs _
  have key : 2 * t * ξ ^ 2 * |f ξ| ≤ t ^ 2 + ξ ^ 4 * f ξ ^ 2 := by
    have hsq2 : (ξ ^ 2 * |f ξ|) ^ 2 = ξ ^ 4 * f ξ ^ 2 := by
      rw [mul_pow, habs]
      ring
    nlinarith [sq_nonneg (t - ξ ^ 2 * |f ξ|), hsq2]
  rw [← sub_nonneg]
  have hval : t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2) - |f ξ|
      = (t ^ 2 + ξ ^ 4 * f ξ ^ 2 - 2 * t * ξ ^ 2 * |f ξ|) / (2 * t * ξ ^ 2) := by
    field_simp
  rw [hval]
  refine div_nonneg ?_ (by positivity)
  linarith [key]

/-- **The tail bound with a free parameter.** -/
theorem integral_Ioi_abs_le_param {f : ℝ → ℝ} {K t : ℝ} (hK : 0 < K) (ht : 0 < t)
    (h1 : IntegrableOn (fun ξ => |f ξ|) (Ioi K))
    (h2 : IntegrableOn (fun ξ => ξ ^ 2 * f ξ ^ 2) (Ioi K)) :
    (∫ ξ in Ioi K, |f ξ|)
      ≤ t / (2 * K) + 1 / (2 * t) * ∫ ξ in Ioi K, ξ ^ 2 * f ξ ^ 2 := by
  have hmaj : IntegrableOn
      (fun ξ : ℝ => t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2)) (Ioi K) :=
    ((integrableOn_Ioi_one_div_sq hK).const_mul (t / 2)).add (h2.const_mul (1 / (2 * t)))
  have hmono : (∫ ξ in Ioi K, |f ξ|)
      ≤ ∫ ξ in Ioi K, (t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2)) := by
    refine setIntegral_mono_on h1 hmaj measurableSet_Ioi fun ξ hξ => ?_
    exact abs_le_secondMoment_split ht (lt_trans hK hξ)
  have hval : (∫ ξ in Ioi K, (t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2)))
      = t / (2 * K) + 1 / (2 * t) * ∫ ξ in Ioi K, ξ ^ 2 * f ξ ^ 2 := by
    rw [integral_add ((integrableOn_Ioi_one_div_sq hK).const_mul (t / 2))
      (h2.const_mul (1 / (2 * t))), integral_const_mul, integral_const_mul,
      integral_Ioi_one_div_sq hK]
    ring
  linarith [hmono, hval.le, hval.ge]

/-- **The sharp tail bound.**  Choosing `t = sqrt(N K)` balances the two halves. -/
theorem integral_Ioi_abs_le_sqrt {f : ℝ → ℝ} {K N : ℝ} (hK : 0 < K) (hN : 0 < N)
    (h1 : IntegrableOn (fun ξ => |f ξ|) (Ioi K))
    (h2 : IntegrableOn (fun ξ => ξ ^ 2 * f ξ ^ 2) (Ioi K))
    (hbd : (∫ ξ in Ioi K, ξ ^ 2 * f ξ ^ 2) ≤ N) :
    (∫ ξ in Ioi K, |f ξ|) ≤ Real.sqrt (N / K) := by
  have hNK : 0 < N * K := by positivity
  have ht : 0 < Real.sqrt (N * K) := Real.sqrt_pos.2 hNK
  have hmain := integral_Ioi_abs_le_param (f := f) hK ht h1 h2
  have hstep : Real.sqrt (N * K) / (2 * K)
      + 1 / (2 * Real.sqrt (N * K)) * ∫ ξ in Ioi K, ξ ^ 2 * f ξ ^ 2
      ≤ Real.sqrt (N * K) / (2 * K) + 1 / (2 * Real.sqrt (N * K)) * N := by
    have hpos : (0 : ℝ) < 1 / (2 * Real.sqrt (N * K)) := by positivity
    nlinarith [hbd, hpos]
  refine le_trans hmain (le_trans hstep (le_of_eq ?_))
  have hsq : Real.sqrt (N * K) * Real.sqrt (N * K) = N * K := Real.mul_self_sqrt hNK.le
  have hval : Real.sqrt (N / K) * Real.sqrt (N * K) = N := by
    rw [← Real.sqrt_mul (by positivity)]
    have hprod : N / K * (N * K) = N ^ 2 := by
      field_simp
    rw [hprod, Real.sqrt_sq hN.le]
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hK
  field_simp
  nlinarith [hsq, hval, ht, hK]

/-! ## From compact convergence and uniform tails to convergence of the integrals -/

open Filter Topology

/-- **Compact convergence plus uniformly small tails gives convergence of the integrals.**  This is
the standard three-epsilon argument, and it is what turns locally uniform convergence of a family of
profiles into convergence of their integrals once the second moment controls the tails. -/
theorem tendsto_integral_of_compact_of_tail {ι : Type*} {l : Filter ι}
    {F : ι → ℝ → ℝ} {f : ℝ → ℝ}
    (hint : ∀ i, Integrable (F i)) (hf : Integrable f)
    (hcompact : ∀ K : ℝ, 0 < K →
      Tendsto (fun i => ∫ ξ in Icc (-K) K, F i ξ) l (𝓝 (∫ ξ in Icc (-K) K, f ξ)))
    (htail : ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 < K ∧
      (∀ i, |∫ ξ in (Icc (-K) K)ᶜ, F i ξ| ≤ δ) ∧ |∫ ξ in (Icc (-K) K)ᶜ, f ξ| ≤ δ) :
    Tendsto (fun i => ∫ ξ, F i ξ) l (𝓝 (∫ ξ, f ξ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK, hFtail, hftail⟩ := htail (ε / 4) (by linarith)
  have hmid := (Metric.tendsto_nhds.1 (hcompact K hK)) (ε / 4) (by linarith)
  filter_upwards [hmid] with i hi
  have hsplitF : (∫ ξ in Icc (-K) K, F i ξ) + (∫ ξ in (Icc (-K) K)ᶜ, F i ξ) = ∫ ξ, F i ξ :=
    integral_add_compl measurableSet_Icc (hint i)
  have hsplitf : (∫ ξ in Icc (-K) K, f ξ) + (∫ ξ in (Icc (-K) K)ᶜ, f ξ) = ∫ ξ, f ξ :=
    integral_add_compl measurableSet_Icc hf
  rw [Real.dist_eq] at hi ⊢
  have hbound : |(∫ ξ, F i ξ) - ∫ ξ, f ξ|
      ≤ |(∫ ξ in Icc (-K) K, F i ξ) - ∫ ξ in Icc (-K) K, f ξ|
        + |∫ ξ in (Icc (-K) K)ᶜ, F i ξ| + |∫ ξ in (Icc (-K) K)ᶜ, f ξ| := by
    have hid : (∫ ξ, F i ξ) - ∫ ξ, f ξ
        = ((∫ ξ in Icc (-K) K, F i ξ) - ∫ ξ in Icc (-K) K, f ξ)
          + ((∫ ξ in (Icc (-K) K)ᶜ, F i ξ) - ∫ ξ in (Icc (-K) K)ᶜ, f ξ) := by
      rw [← hsplitF, ← hsplitf]
      ring
    rw [hid]
    have h1 := abs_add_le ((∫ ξ in Icc (-K) K, F i ξ) - ∫ ξ in Icc (-K) K, f ξ)
      ((∫ ξ in (Icc (-K) K)ᶜ, F i ξ) - ∫ ξ in (Icc (-K) K)ᶜ, f ξ)
    have h2 := abs_sub ((∫ ξ in (Icc (-K) K)ᶜ, F i ξ)) ((∫ ξ in (Icc (-K) K)ᶜ, f ξ))
    linarith
  have hF := hFtail i
  linarith [hbound, hi, hF, hftail]

/-! ## The interval form, matching the window convention -/

/-- `∫_K^R ξ^(−2) = 1/K − 1/R`. -/
theorem intervalIntegral_one_div_sq {K R : ℝ} (hK : 0 < K) (hKR : K ≤ R) :
    (∫ ξ in K..R, 1 / ξ ^ 2) = 1 / K - 1 / R := by
  have hne : ∀ ξ ∈ Set.uIcc K R, ξ ≠ 0 := by
    intro ξ hξ
    rw [Set.uIcc_of_le hKR] at hξ
    have : 0 < ξ := lt_of_lt_of_le hK hξ.1
    exact ne_of_gt this
  have hderiv : ∀ ξ ∈ Set.uIcc K R, HasDerivAt (fun z : ℝ => -(1 / z)) (1 / ξ ^ 2) ξ := by
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := hne ξ hξ
    have h0 : HasDerivAt (fun z : ℝ => z⁻¹) (-(ξ ^ 2)⁻¹) ξ := hasDerivAt_inv hξ0
    have h1 : HasDerivAt (fun z : ℝ => -z⁻¹) ((ξ ^ 2)⁻¹) ξ := by
      have hneg := h0.neg
      rwa [neg_neg] at hneg
    have hfun : (fun z : ℝ => -(1 / z)) = fun z : ℝ => -z⁻¹ := by
      funext z
      rw [one_div]
    rw [hfun, one_div]
    exact h1
  have hint : IntervalIntegrable (fun ξ : ℝ => 1 / ξ ^ 2) MeasureTheory.volume K R := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun ξ hξ => ?_
    exact pow_ne_zero 2 (hne ξ hξ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  field_simp
  ring

/-- **The interval tail bound.**  On any window past `K`, the integral is controlled by the second
moment there. -/
theorem intervalIntegral_abs_le_sqrt {f : ℝ → ℝ} {K R N : ℝ} (hK : 0 < K) (hKR : K ≤ R)
    (hN : 0 < N) (hcont : Continuous f)
    (hbd : (∫ ξ in K..R, ξ ^ 2 * f ξ ^ 2) ≤ N) :
    |∫ ξ in K..R, f ξ| ≤ Real.sqrt (N / K) := by
  have hNK : 0 < N * K := by positivity
  have ht : 0 < Real.sqrt (N * K) := Real.sqrt_pos.2 hNK
  set t := Real.sqrt (N * K) with htdef
  have hne : ∀ ξ ∈ Set.uIcc K R, ξ ≠ 0 := by
    intro ξ hξ
    rw [Set.uIcc_of_le hKR] at hξ
    exact ne_of_gt (lt_of_lt_of_le hK hξ.1)
  have hintf : IntervalIntegrable (fun ξ : ℝ => |f ξ|) MeasureTheory.volume K R :=
    (hcont.abs).intervalIntegrable K R
  have hint2 : IntervalIntegrable (fun ξ : ℝ => ξ ^ 2 * f ξ ^ 2) MeasureTheory.volume K R :=
    (by fun_prop : Continuous fun ξ : ℝ => ξ ^ 2 * f ξ ^ 2).intervalIntegrable K R
  have hintinv : IntervalIntegrable (fun ξ : ℝ => 1 / ξ ^ 2) MeasureTheory.volume K R := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun ξ hξ => ?_
    exact pow_ne_zero 2 (hne ξ hξ)
  -- the pointwise split, integrated
  have hmono : (∫ ξ in K..R, |f ξ|)
      ≤ ∫ ξ in K..R, (t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2)) := by
    refine intervalIntegral.integral_mono_on hKR hintf
      ((hintinv.const_mul (t / 2)).add (hint2.const_mul (1 / (2 * t)))) fun ξ hξ => ?_
    exact abs_le_secondMoment_split ht (lt_of_lt_of_le hK hξ.1)
  have hval : (∫ ξ in K..R, (t / 2 * (1 / ξ ^ 2) + 1 / (2 * t) * (ξ ^ 2 * f ξ ^ 2)))
      = t / 2 * (1 / K - 1 / R) + 1 / (2 * t) * ∫ ξ in K..R, ξ ^ 2 * f ξ ^ 2 := by
    rw [intervalIntegral.integral_add (hintinv.const_mul (t / 2))
      (hint2.const_mul (1 / (2 * t))), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral_one_div_sq hK hKR]
  have habs : |∫ ξ in K..R, f ξ| ≤ ∫ ξ in K..R, |f ξ| :=
    intervalIntegral.abs_integral_le_integral_abs hKR
  have hR : 0 < R := lt_of_lt_of_le hK hKR
  have hinvR : 0 < 1 / R := by positivity
  have hstep : (∫ ξ in K..R, |f ξ|) ≤ t / 2 * (1 / K) + 1 / (2 * t) * N := by
    have hpos : (0 : ℝ) < 1 / (2 * t) := by positivity
    have htpos : (0 : ℝ) < t / 2 := by positivity
    nlinarith [hmono, hval.le, hval.ge, hbd, hinvR, hpos, htpos]
  have hfinal : t / 2 * (1 / K) + 1 / (2 * t) * N = Real.sqrt (N / K) := by
    have hsq : t * t = N * K := Real.mul_self_sqrt hNK.le
    have hval2 : Real.sqrt (N / K) * t = N := by
      rw [htdef, ← Real.sqrt_mul (by positivity)]
      have hprod : N / K * (N * K) = N ^ 2 := by
        field_simp
      rw [hprod, Real.sqrt_sq hN.le]
    have hKne : (K : ℝ) ≠ 0 := ne_of_gt hK
    field_simp
    nlinarith [hsq, hval2, ht, hK]
  linarith [habs, hstep, hfinal.le, hfinal.ge]

/-! ## The compact half: pointwise convergence with a uniform bound -/

/-- **Dominated convergence on a compact window.**  Pointwise convergence of a uniformly bounded
family of continuous functions gives convergence of the integrals over the window.  This is the
compact half of the transfer above. -/
theorem tendsto_setIntegral_Icc_of_tendsto_of_bounded {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated]
    {u : ι → ℝ → ℝ} {v : ℝ → ℝ} {a b B : ℝ}
    (hcont : ∀ i, Continuous (u i))
    (hB : ∀ i, ∀ x ∈ Icc a b, |u i x| ≤ B)
    (hlim : ∀ x ∈ Icc a b, Tendsto (fun i => u i x) L (𝓝 (v x))) :
    Tendsto (fun i => ∫ x in Icc a b, u i x) L (𝓝 (∫ x in Icc a b, v x)) := by
  have hmeasIcc : MeasurableSet (Icc a b) := measurableSet_Icc
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => B) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun i => (hcont i).aestronglyMeasurable
  · refine Eventually.of_forall fun i => ?_
    rw [ae_restrict_iff' hmeasIcc]
    refine Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs]
    exact hB i x hx
  · refine integrableOn_const (C := B) (μ := MeasureTheory.volume) (s := Icc a b) ?_ ?_
    · exact (measure_Icc_lt_top).ne
    · simp
  · rw [ae_restrict_iff' hmeasIcc]
    exact Eventually.of_forall fun x hx => hlim x hx

/-! ## The growing-window transfer -/

/-- **Convergence of integrals over a growing window.**  If the integrals over every fixed window
converge, the window values converge to the target, and the tails past any large enough cut are
uniformly small, then the integrals over the growing window converge to the target.  This is the
shape the prolate family has: the window is `[−sqrt c, sqrt c]` and grows with the bandwidth. -/
theorem tendsto_intervalIntegral_growing_window {ι : Type*} {L : Filter ι}
    {F : ι → ℝ → ℝ} {R : ι → ℝ} {g : ℝ → ℝ} {A : ℝ}
    (hint : ∀ i, ∀ u v : ℝ, IntervalIntegrable (F i) MeasureTheory.volume u v)
    (hcompact : ∀ K : ℝ, 0 < K → Tendsto (fun i => ∫ x in (-K)..K, F i x) L (𝓝 (g K)))
    (hg : Tendsto g atTop (𝓝 A))
    (hKR : ∀ K : ℝ, 0 < K → ∀ᶠ i in L, K ≤ R i)
    (htail : ∀ δ : ℝ, 0 < δ → ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      ∀ᶠ i in L, |∫ x in K..(R i), F i x| ≤ δ ∧ |∫ x in (-(R i))..(-K), F i x| ≤ δ) :
    Tendsto (fun i => ∫ x in (-(R i))..(R i), F i x) L (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K₀, hK₀, htailK⟩ := htail (ε / 5) (by linarith)
  have hgev := (Metric.tendsto_nhds.1 hg) (ε / 5) (by linarith)
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.1 hgev
  set K : ℝ := max K₀ (max K₁ 1) with hKdef
  have hK1le : (1 : ℝ) ≤ K := le_trans (le_max_right K₁ 1) (le_max_right K₀ _)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1le
  have hKK₀ : K₀ ≤ K := le_max_left _ _
  have hKK₁ : K₁ ≤ K := le_trans (le_max_left K₁ 1) (le_max_right K₀ _)
  have hgK : dist (g K) A < ε / 5 := hK₁ K hKK₁
  have hmid := (Metric.tendsto_nhds.1 (hcompact K hK0)) (ε / 5) (by linarith)
  filter_upwards [hmid, htailK K hKK₀, hKR K hK0] with i hi ⟨htail1, htail2⟩ _hRi
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals
    (f := F i) (μ := MeasureTheory.volume) (a := -(R i)) (b := -K) (c := K)
    (hint i _ _) (hint i _ _)
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals
    (f := F i) (μ := MeasureTheory.volume) (a := -(R i)) (b := K) (c := R i)
    (hint i _ _) (hint i _ _)
  rw [Real.dist_eq] at hi hgK ⊢
  have hid : (∫ x in (-(R i))..(R i), F i x) - A
      = ((∫ x in (-K)..K, F i x) - g K) + (g K - A)
        + (∫ x in (-(R i))..(-K), F i x) + (∫ x in K..(R i), F i x) := by
    have h1 : (∫ x in (-(R i))..(-K), F i x) + (∫ x in (-K)..K, F i x)
        = ∫ x in (-(R i))..K, F i x := hadd1
    have h2 : (∫ x in (-(R i))..K, F i x) + (∫ x in K..(R i), F i x)
        = ∫ x in (-(R i))..(R i), F i x := hadd2
    linarith [h1, h2]
  rw [hid]
  have hb1 := abs_add_le ((∫ x in (-K)..K, F i x) - g K + (g K - A)
      + (∫ x in (-(R i))..(-K), F i x)) (∫ x in K..(R i), F i x)
  have hb2 := abs_add_le ((∫ x in (-K)..K, F i x) - g K + (g K - A))
      (∫ x in (-(R i))..(-K), F i x)
  have hb3 := abs_add_le ((∫ x in (-K)..K, F i x) - g K) (g K - A)
  linarith [hb1, hb2, hb3, hi, hgK, htail1, htail2]

end GaloisForLFunctions.RHTower

end
