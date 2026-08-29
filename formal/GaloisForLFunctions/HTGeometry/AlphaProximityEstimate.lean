import GaloisForLFunctions.HTGeometry.NegPowerCircleAverage
import GaloisForLFunctions.HTGeometry.PosLogRpowAverage

/-!
# The `α`-power estimate for a circle average of `log⁺`

Transporting the measure-average form of the `α`-power Jensen estimate to the interval-integral form
used by circle averages, and combining it with the uniform divisor-kernel bound.

The result is the shape of Nevanlinna's estimate for the proximity of a logarithmic derivative: if
on the circle of radius `r` a function is bounded by a divisor-kernel sum plus a constant `B`, then
its `log⁺` circle average is at most

```text
(1/α) · log (1 + (2π)⁻¹ · (∑_u m_u^α) · (C_α r^{-α} + 2π (R−r)^{-α}) + B^α),
```

so that `n(R)` divisor points cost only `log n(R)` and the boundary term only `log B`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real

/-- The normalised arc measure of the circle. -/
noncomputable def arcMeasure : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * π))

instance : IsFiniteMeasure arcMeasure := by
  rw [arcMeasure]
  exact ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩

theorem arcMeasure_univ : arcMeasure Set.univ = ENNReal.ofReal (2 * π) := by
  rw [arcMeasure, Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

instance : NeZero arcMeasure := by
  refine ⟨fun h => ?_⟩
  have huniv : arcMeasure Set.univ = ENNReal.ofReal (2 * π) := arcMeasure_univ
  rw [h] at huniv
  have hpos : (0 : ℝ) < 2 * π := by positivity
  simp only [Measure.coe_zero, Pi.zero_apply] at huniv
  rw [eq_comm, ENNReal.ofReal_eq_zero] at huniv
  linarith

theorem arcMeasure_real_univ : arcMeasure.real Set.univ = 2 * π := by
  show (arcMeasure Set.univ).toReal = 2 * π
  rw [arcMeasure_univ, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * π)]

/-- The average against the arc measure is the normalised interval integral. -/
theorem average_arcMeasure (h : ℝ → ℝ) :
    ⨍ θ, h θ ∂arcMeasure = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), h θ := by
  rw [MeasureTheory.average_eq, arcMeasure_real_univ, smul_eq_mul, arcMeasure,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]

/-- Interval-integral form of the `α`-power `log⁺` estimate. -/
theorem intervalIntegral_posLog_le_log_one_add_rpow {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ}
    (hF0 : ∀ θ, 0 ≤ F θ) (hFmeas : Measurable F)
    (hint : IntervalIntegrable (fun θ => (F θ) ^ α) volume 0 (2 * π)) :
    (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), Real.posLog (F θ)
      ≤ (1 / α) * Real.log (1 + (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), (F θ) ^ α) := by
  have hintμ : Integrable (fun θ => (F θ) ^ α) arcMeasure := by
    rw [arcMeasure]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp hint
  have h := average_posLog_le_log_one_add_average_rpow hα hF0 hFmeas hintμ
  rw [average_arcMeasure, average_arcMeasure] at h
  exact h

/-- **The `α`-power proximity estimate.**  A function bounded on the circle of radius `r` by a
divisor-kernel sum plus a constant has a controlled `log⁺` circle average. -/
theorem circleAverage_posLog_le_of_kernel_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r Rr B : ℝ} (hr : 0 < r) (hRr : 0 < Rr) (hB : 0 ≤ B)
    (S : Finset ℂ) (m : ℂ → ℝ) (hm : ∀ u ∈ S, 0 ≤ m u)
    {F : ℝ → ℝ} (hF0 : ∀ θ, 0 ≤ F θ) (hFmeas : Measurable F)
    (hbound : ∀ᵐ θ : ℝ,
      F θ ≤ (∑ u ∈ S, m u * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ + Rr⁻¹)) + B) :
    (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), Real.posLog (F θ)
      ≤ (1 / α) * Real.log (1 + ((2 * π)⁻¹ * ((∑ u ∈ S, (m u) ^ α)
          * (r ^ (-α) * sinNegPowerConst α + 2 * π * Rr ^ (-α))) + B ^ α)) := by
  classical
  set K : ℝ → ℝ := fun θ =>
    ∑ u ∈ S, m u * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ + Rr⁻¹) with hK
  have hK0 : ∀ θ, 0 ≤ K θ := by
    intro θ
    refine Finset.sum_nonneg fun u hu => ?_
    have h1 : (0 : ℝ) ≤ ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ Rr⁻¹ := by positivity
    exact mul_nonneg (hm u hu) (by linarith)
  -- the `α`-th power of `F` is dominated by that of the kernel sum plus `B^α`
  have hFα : ∀ᵐ θ : ℝ, (F θ) ^ α ≤ (K θ) ^ α + B ^ α := by
    filter_upwards [hbound] with θ hθ
    calc (F θ) ^ α ≤ (K θ + B) ^ α := Real.rpow_le_rpow (hF0 θ) hθ hα0.le
      _ ≤ (K θ) ^ α + B ^ α := Real.rpow_add_le_add_rpow (hK0 θ) hB hα0.le hα1.le
  have hKint : IntervalIntegrable (fun θ => (K θ) ^ α) volume 0 (2 * π) := by
    have hGterm : ∀ u ∈ S, IntervalIntegrable
        (fun θ : ℝ => (m u) ^ α * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α)
          + Rr ^ (-α))) volume 0 (2 * π) := fun u _ =>
      ((intervalIntegrable_norm_circle_sub_rpow_neg hα0 hα1 hr u).add
        intervalIntegrable_const).const_mul _
    have hsum := IntervalIntegrable.sum S hGterm
    have hmeas : Measurable fun θ : ℝ => (K θ) ^ α := by
      refine Measurable.pow_const ?_ _
      rw [hK]
      refine Finset.measurable_sum _ fun u _ => ?_
      refine Measurable.const_mul ?_ _
      refine Measurable.add ?_ measurable_const
      exact ((Continuous.norm (by fun_prop)).measurable).inv
    refine IntervalIntegrable.mono_fun' (g := fun θ : ℝ =>
      ∑ u ∈ S, (m u) ^ α * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α) + Rr ^ (-α)))
      ?_ hmeas.aestronglyMeasurable.restrict ?_
    · have heq : (∑ i ∈ S, fun θ : ℝ => (m i) ^ α
          * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - i‖ ^ (-α) + Rr ^ (-α)))
          = fun θ : ℝ => ∑ u ∈ S, (m u) ^ α
            * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α) + Rr ^ (-α)) := by
        funext θ
        simp [Finset.sum_apply]
      rwa [heq] at hsum
    · refine MeasureTheory.ae_restrict_of_ae (Filter.Eventually.of_forall fun θ => ?_)
      show ‖(K θ) ^ α‖ ≤ ∑ u ∈ S, (m u) ^ α
        * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α) + Rr ^ (-α))
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hK0 θ) α)]
      have hterm0 : ∀ u ∈ S, 0 ≤ m u * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ + Rr⁻¹) := by
        intro u hu
        have h1 : (0 : ℝ) ≤ ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ := by positivity
        have h2 : (0 : ℝ) ≤ Rr⁻¹ := by positivity
        exact mul_nonneg (hm u hu) (by linarith)
      refine le_trans (rpow_sum_le_sum_rpow S _ hterm0 hα0 hα1.le) ?_
      refine Finset.sum_le_sum fun u hu => ?_
      have hnn : (0 : ℝ) ≤ ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ := by positivity
      have hRinv : (0 : ℝ) ≤ Rr⁻¹ := by positivity
      rw [Real.mul_rpow (hm u hu) (by linarith)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hm u hu) α)
      refine le_trans (Real.rpow_add_le_add_rpow hnn hRinv hα0.le hα1.le) ?_
      rw [inv_rpow_eq_rpow_neg (norm_nonneg _), inv_rpow_eq_rpow_neg hRr.le]
  have hFαint : IntervalIntegrable (fun θ => (F θ) ^ α) volume 0 (2 * π) := by
    refine IntervalIntegrable.mono_fun' (g := fun θ : ℝ => (K θ) ^ α + B ^ α)
      (hKint.add intervalIntegrable_const)
      ((hFmeas.pow_const α).aestronglyMeasurable.restrict) ?_
    refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hFα] with θ hθ
    show ‖(F θ) ^ α‖ ≤ (K θ) ^ α + B ^ α
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hF0 θ) α)]
    exact hθ
  have hstep := intervalIntegral_posLog_le_log_one_add_rpow hα0 hF0 hFmeas hFαint
  refine le_trans hstep ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.log_le_log (by
    have : (0 : ℝ) ≤ ∫ θ in (0 : ℝ)..(2 * π), (F θ) ^ α :=
      intervalIntegral.integral_nonneg (by positivity) fun θ _ => Real.rpow_nonneg (hF0 θ) α
    have h2 : (0 : ℝ) ≤ (2 * π)⁻¹ := by positivity
    nlinarith) ?_
  have hle : ∫ θ in (0 : ℝ)..(2 * π), (F θ) ^ α
      ≤ ∫ θ in (0 : ℝ)..(2 * π), ((K θ) ^ α + B ^ α) :=
    intervalIntegral.integral_mono_ae (by positivity) hFαint
      (hKint.add intervalIntegrable_const) hFα
  have hsplit : ∫ θ in (0 : ℝ)..(2 * π), ((K θ) ^ α + B ^ α)
      = (∫ θ in (0 : ℝ)..(2 * π), (K θ) ^ α) + 2 * π * B ^ α := by
    rw [intervalIntegral.integral_add hKint intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hker := intervalIntegral_kernelSum_rpow_le hα0 hα1 hr hRr S m hm
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hfinal : (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), (F θ) ^ α
      ≤ (2 * π)⁻¹ * ((∑ u ∈ S, (m u) ^ α)
          * (r ^ (-α) * sinNegPowerConst α + 2 * π * Rr ^ (-α))) + B ^ α := by
    have hchain : ∫ θ in (0 : ℝ)..(2 * π), (F θ) ^ α
        ≤ (∑ u ∈ S, (m u) ^ α) * (r ^ (-α) * sinNegPowerConst α + 2 * π * Rr ^ (-α))
          + 2 * π * B ^ α := by
      rw [hsplit] at hle
      linarith [hle, hker]
    have hinv : (0 : ℝ) < (2 * π)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left hchain hinv.le
    have hcancel : (2 * π)⁻¹ * (2 * π * B ^ α) = B ^ α := by
      field_simp
    nlinarith [this, hcancel]
  linarith [hfinal]


/-! ## Assembling with the Poisson–Jensen kernel -/

/-- **The Blaschke reflection factor is bounded by `1/(R − r)`** on the circle of radius `r`. -/
theorem norm_blaschke_reflection_le {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    {u w : ℂ} (hu : ‖u‖ ≤ R) (hw : ‖w‖ = r) :
    ‖(starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * w)‖ ≤ (R - r)⁻¹ := by
  have hRr : 0 < R - r := by linarith
  have h2 : ‖((R : ℂ)) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have h3 : ‖(starRingEnd ℂ) u * w‖ = ‖u‖ * r := by
    rw [norm_mul, RCLike.norm_conj, hw]
  have hden : R * (R - r) ≤ ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * w‖ := by
    have h1 := norm_sub_norm_le ((R : ℂ) ^ 2) ((starRingEnd ℂ) u * w)
    rw [h2, h3] at h1
    nlinarith [h1, hu, hr, hR]
  have hdenpos : (0 : ℝ) < ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * w‖ := by
    have : (0 : ℝ) < R * (R - r) := by positivity
    linarith
  rw [norm_div, RCLike.norm_conj, div_le_iff₀ hdenpos]
  have hstep : (R - r)⁻¹ * (R * (R - r)) ≤ (R - r)⁻¹ * ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) u * w‖ := by
    refine mul_le_mul_of_nonneg_left hden (by positivity)
  have hcancel : (R - r)⁻¹ * (R * (R - r)) = R := by
    field_simp
  rw [hcancel] at hstep
  linarith [hu, hstep]

/-- **The `α`-power proximity estimate for a Poisson–Jensen bound.**  If on the circle of radius `r`
a function is bounded by the Poisson–Jensen divisor kernel plus a constant `B`, then its `log⁺`
circle average costs only the logarithm of the total divisor weight, of `1/(R − r)` and of `B`. -/
theorem circleAverage_posLog_le_of_poissonJensen {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r R B : ℝ} (hr : 0 < r) (hrR : r < R)
    (D : ℂ → ℤ) (S : Finset ℂ) (hDsupp : ∀ u, D u ≠ 0 → u ∈ S) (hDball : ∀ u ∈ S, ‖u‖ ≤ R)
    (hB : 0 ≤ B) (g : ℂ → ℂ)
    (hgmeas : Measurable fun θ : ℝ => ‖g ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
    (hbound : ∀ᵐ θ : ℝ, ‖g ((r : ℂ) * Complex.exp (θ * Complex.I))‖
      ≤ ‖∑ᶠ u : ℂ, (D u : ℂ) * (1 / ((r : ℂ) * Complex.exp (θ * Complex.I) - u)
        + (starRingEnd ℂ) u
          / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * ((r : ℂ) * Complex.exp (θ * Complex.I))))‖ + B) :
    (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
        Real.posLog ‖g ((r : ℂ) * Complex.exp (θ * Complex.I))‖
      ≤ (1 / α) * Real.log (1 + ((2 * π)⁻¹ * ((∑ u ∈ S, (|D u| : ℝ) ^ α)
          * (r ^ (-α) * sinNegPowerConst α + 2 * π * (R - r) ^ (-α))) + B ^ α)) := by
  classical
  have hR : 0 < R := lt_trans hr hrR
  have hRr : 0 < R - r := by linarith
  have hcirc : ∀ θ : ℝ, ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = r := by
    intro θ
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    simp
  refine circleAverage_posLog_le_of_kernel_bound hα0 hα1 hr hRr hB S (fun u => (|D u| : ℝ))
    (fun u _ => by positivity) (fun θ => norm_nonneg _) hgmeas ?_
  filter_upwards [hbound] with θ hθ
  set w : ℂ := (r : ℂ) * Complex.exp (θ * Complex.I) with hwdef
  have hwn : ‖w‖ = r := hcirc θ
  refine le_trans hθ ?_
  refine add_le_add ?_ (le_refl B)
  -- replace the finsum by a Finset sum and bound each term
  set G : ℂ → ℂ := fun u => (D u : ℂ) * (1 / (w - u)
    + (starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * w)) with hG
  have hsupp : Function.support G ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hD : (D u : ℂ) ≠ 0 := by
      intro h
      apply hu
      show (D u : ℂ) * (1 / (w - u)
        + (starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * w)) = 0
      rw [h, zero_mul]
    exact hDsupp u (by exact_mod_cast hD)
  rw [finsum_eq_sum_of_support_subset G hsupp]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun u hu => ?_
  rw [hG, norm_mul]
  have hDn : ‖(D u : ℂ)‖ = |((D u : ℤ) : ℝ)| := by
    simp
  rw [hDn]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖1 / (w - u)‖ = ‖w - u‖⁻¹ := by
    rw [norm_div, norm_one, one_div]
  have h2 : ‖(starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * w)‖ ≤ (R - r)⁻¹ :=
    norm_blaschke_reflection_le hR hr.le hrR (hDball u hu) hwn
  rw [h1]
  linarith [h2]

end GaloisForLFunctions.HTGeometry
