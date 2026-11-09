import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ConfigurationTailIsolation
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.FiniteSpectrumOscillation
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SquareRootWindowLeakage

/-!
# Square-root logarithmic windows detect every zero depth

A lower bound of exponential order `α` on arbitrarily late windows of
radius `r√T` excludes every zero deeper than `α`. Infinite positive
annihilation preserves a chosen deeper zero and leaves a finite spectrum.
Its bounded-gap negative excursions contradict the exponentially small
leakage from the observation windows. Temperedness suffices; no maximal
real part is assumed.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Arbitrarily late square-root windows detect every depth above their lower-bound exponent. -/
theorem configuration_re_le_of_squareRoot_windows {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {α r K : ℝ} (hα : 0 ≤ α) (hr : 0 < r)
    (hwindow : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ, |u - T| ≤ r * Real.sqrt T →
      -(K * Real.exp (α * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + α := by
  classical
  intro ρ hρ
  by_contra hρle
  have hρdeep : 1 / 2 + α < ρ.re := lt_of_not_ge hρle
  let z₀ : ℂ := ρ - 1 / 2
  let c : ℂ → ℂ := evenCoeff Z (boxSpline 1 3)
  let D : ℝ := 1 / 2 + |α|
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hc : Summable fun z => ‖c z‖ := summable_norm_evenCoeff_spline hZ
  have hw : ∀ z, c z ≠ 0 → |(z - (α : ℂ)).re| ≤ D :=
    fun z hz => configuration_shifted_exponent_bound α hz
  have hc₀ : c z₀ ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z (contDiff_boxSpline one_pos 2).continuous
      (hasCompactSupport_of_support_subset_abs (boxSpline_support one_pos 3))
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ
      (paperFT_boxSpline_ne_zero one_pos 3
        (im_gammaOf_ne_zero (by linarith only [hρdeep, hα])))
  -- Delete a cofinite tail while retaining this deeper exponent.
  obtain ⟨a, h, S, hsq, hcost, hkeep, hdelete⟩ :=
    exists_configuration_tail_deletion Z hZ hnoreal α (z₀ - (α : ℂ))
      (windowSquareBudget_pos hD hr)
  let d : ℂ → ℂ := fun z => c z * ∏' n, quartetFactor (a n) (h n) (z - (α : ℂ))
  have hdout : ∀ z ∉ S, d z = 0 := by
    intro z hz
    by_cases hcz : c z = 0
    · simp only [d, hcz, zero_mul]
    simp only [d, hdelete z hz hcz, mul_zero]
  let R : Finset ℂ := S.filter fun z => d z ≠ 0
  have hmem (z : ℂ) : z ∈ R ↔ d z ≠ 0 := by
    simp only [R, Finset.mem_filter]
    exact ⟨fun hz => hz.2, fun hz => ⟨by_contra fun hn => hz (hdout z hn), hz⟩⟩
  have hdconj (z : ℂ) : d (conj z) = conj (d z) := by
    have he : conj z - (α : ℂ) = conj (z - (α : ℂ)) := by simp
    simp only [d, c, evenCoeff_conj, he, tprod_quartetFactor_conj a h hsq, map_mul]
  have hRconj : ∀ z ∈ R, conj z ∈ R := by
    intro z hz
    apply (hmem _).mpr
    rw [hdconj]
    intro hn
    apply (hmem z).mp hz
    simpa only [Complex.conj_conj, map_zero] using congrArg conj hn
  have hRreal : ∀ z ∈ R, z.im ≠ 0 := by
    intro z hz
    have hcz : c z ≠ 0 := fun hn => (hmem z).mp hz (by simp [d, hn])
    intro him
    rcases mem_of_evenCoeff_ne_zero hcz with h | h
    · exact hnoreal _ h (by simp [him])
    · exact hnoreal _ h (by simp [him])
  have hz₀R : z₀ ∈ R := (hmem z₀).mpr (mul_ne_zero hc₀ hkeep)
  -- Only the retained finite spectrum needs a greatest real part.
  obtain ⟨z₁, hz₁, hmax⟩ := R.exists_max_image Complex.re ⟨z₀, hz₀R⟩
  have hβα : 0 < z₁.re - α := by
    have hmax₀ := hmax z₀ hz₀R
    dsimp only [z₀] at hmax₀
    simp only [Complex.sub_re] at hmax₀
    norm_num at hmax₀
    linarith only [hρdeep, hmax₀]
  obtain ⟨B, η, U₀, hB, hη, hnegative⟩ := finite_spectrum_dense_negative R d
    hRconj (fun z _ => hdconj z) hRreal hz₁ ((hmem z₁).mp hz₁) hmax
  let A : ℝ := ∑' z, ‖c z‖
  have hleak : Tendsto (fun T : ℝ =>
      2 * A * Real.exp (D * B + D ^ 2 * windowSquareBudget D r - T)) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
      (2 * A * Real.exp (D * B + D ^ 2 * windowSquareBudget D r))
    simpa only [mul_zero, sub_eq_add_neg, Real.exp_add, mul_assoc] using ht
  have hgrowth : Tendsto (fun T : ℝ => η * Real.exp ((z₁.re - α) * T)) atTop atTop := by
    simpa only [Function.comp_def, id_eq] using
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hβα)).const_mul_atTop hη
  have hlate : ∀ᶠ T : ℝ in atTop, 0 ≤ T ∧ U₀ ≤ T ∧
      2 * A * Real.exp (D * B + D ^ 2 * windowSquareBudget D r - T) ≤ 1 ∧
      |K| + 1 < η * Real.exp ((z₁.re - α) * T) ∧ B ≤ r * Real.sqrt T / 2 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_ge_atTop U₀,
      hleak.eventually_le_const (by norm_num : (0 : ℝ) < 1),
      hgrowth.eventually_gt_atTop (|K| + 1),
      Real.tendsto_sqrt_atTop.eventually_ge_atTop (2 * B / r)] with T hT hU hE hG hR
    refine ⟨hT, hU, hE, hG, ?_⟩
    have hh := (div_le_iff₀ hr).mp hR
    nlinarith only [hh]
  obtain ⟨U, hU⟩ := eventually_atTop.mp hlate
  obtain ⟨T, hTU, hbound⟩ := hwindow U
  obtain ⟨hT, hTU₀, herror, hgrow, hspan⟩ := hU T hTU
  obtain ⟨t, ht, hneg⟩ := hnegative T hTU₀
  have ht0 : 0 ≤ t := hT.trans ht.1
  have htB : |t| ≤ T + B := by rw [abs_of_nonneg ht0]; exact ht.2
  -- The negative excursion lies inside an observation window with half its radius to spare.
  have hlocal : ∀ u, |u - t| ≤ r * Real.sqrt T / 2 →
      -|K| ≤ ∑' z : ℂ, (c z * Complex.exp ((z - (α : ℂ)) * u)).re := by
    intro u hu
    have htT : |t - T| ≤ B := abs_le.mpr ⟨by linarith only [ht.1, hB], by linarith only [ht.2]⟩
    have huT : |u - T| ≤ r * Real.sqrt T := by
      have htri : |u - T| ≤ |u - t| + |t - T| := by
        calc |u - T| = |(u - t) + (t - T)| := by congr 1; ring
          _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_add_le (u - t) (t - T)
      linarith only [htri, htT, hu, hspan]
    have hh := mul_le_mul_of_nonneg_left (hbound u huT) (Real.exp_pos (-α * u)).le
    have he : Real.exp (-α * u) * (-(K * Real.exp (α * u))) = -K := by
      have hp : Real.exp (-α * u) * Real.exp (α * u) = 1 := by
        rw [← Real.exp_add]
        simp only [neg_mul, neg_add_cancel, Real.exp_zero]
      calc _ = -K * (Real.exp (-α * u) * Real.exp (α * u)) := by ring
        _ = _ := by rw [hp, mul_one]
    rw [he, configuration_shifted_trace_series hZ] at hh
    exact (neg_le_neg (le_abs_self K)).trans hh
  have hfloor := infinite_tail_squareRoot_floor a h hsq c (fun z => z - (α : ℂ))
    hD hr hc hw hcost.le (abs_nonneg K) hT htB hlocal
  have hsum : (∑' z : ℂ, (d z * Complex.exp ((z - (α : ℂ)) * t)).re) =
      (∑ z ∈ R, d z * Complex.exp ((z - (α : ℂ)) * t)).re := by
    rw [tsum_eq_sum (s := R) (fun z hz => by
      have hd : d z = 0 := by_contra fun hn => hz ((hmem z).mpr hn)
      simp only [hd, zero_mul, Complex.zero_re])]
    exact (map_sum Complex.reCLM (fun z => d z * Complex.exp ((z - (α : ℂ)) * t)) R).symm
  change -|K| - 2 * A * Real.exp (D * B + D ^ 2 * windowSquareBudget D r - T) ≤
    ∑' z : ℂ, (d z * Complex.exp ((z - (α : ℂ)) * t)).re at hfloor
  rw [hsum] at hfloor
  -- Leakage is bounded, whereas the retained negative excursion grows exponentially.
  have hlower : -(|K| + 1) ≤ (∑ z ∈ R, d z * Complex.exp ((z - (α : ℂ)) * t)).re := by
    linarith only [hfloor, herror]
  have hscaled := mul_le_mul_of_nonneg_right hlower (Real.exp_pos (α * t)).le
  rw [finite_sum_cexp_scale] at hscaled
  have hgt : |K| + 1 < η * Real.exp ((z₁.re - α) * t) :=
    hgrow.trans_le (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.1 hβα.le)) hη.le)
  have hmul := mul_lt_mul_of_pos_right hgt (Real.exp_pos (α * t))
  have he : Real.exp (z₁.re * t) = Real.exp ((z₁.re - α) * t) * Real.exp (α * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hneg
  nlinarith only [hscaled, hneg, hmul]

/-- The continuous square-root criterion for the actual zeta zeros. -/
theorem zeta_re_le_of_squareRoot_windows {α r K : ℝ} (hα : 0 ≤ α) (hr : 0 < r)
    (hwindow : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ, |u - T| ≤ r * Real.sqrt T →
      -(K * Real.exp (α * u)) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + α :=
  configuration_re_le_of_squareRoot_windows temperedConfig_zetaZeroConfig
    (fun _ hρ hzero => not_mem_carrier_of_im_eq_zero hρ hzero) hα hr hwindow

#print axioms configuration_re_le_of_squareRoot_windows
#print axioms zeta_re_le_of_squareRoot_windows

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
