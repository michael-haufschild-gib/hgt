import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.KernelLogarithmicTrace
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.FiniteSpectrumOscillation

/-!
# Upper bounds on logarithmic windows

Apply the positive quartet filter to the negative trace. Its finite
spectrum still has a nonzero deepest mode, so dense negative excursions
contradict a local floor for that negative trace. The logarithmic kernel
moment estimate controls the leakage outside the observation window.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open _root_.RHTower

/-- Positive kernels preserve a local floor of the negative normalized trace, with exponentially small leakage. -/
theorem zeta_negative_kernel_logarithmic_floor {k : ℝ → ℝ} {C : ℝ}
    (hC : 0 < C) (hkc : Continuous k) (hk : ∀ x, 0 < k x)
    (hm : ∀ s : ℝ, Integrable fun x => Real.exp (s * |x|) * |k x|)
    (hb : ∀ s : ℝ, 0 ≤ s → (∫ x, Real.exp (s * |x|) * k x) ≤
      C * Real.exp ((s + 6) * Real.log (s + 6)))
    (α : ℝ) {K T B t : ℝ} (hK : 0 ≤ K) (hT : 6 ≤ T)
    (hbT : 1 / 2 + 2 * |α| ≤ T)
    (hE : 3 / 2 + |α| ≤ Real.log (T + 2)) (ht : |t| ≤ T + B)
    (hlocal : ∀ u, |u - t| ≤ 8 * Real.log (T + 2) →
      -K ≤ Real.exp (-α * u) * (-(2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re))) :
    -K * (∫ x, Real.exp (α * x) * k x) -
      (∑' z : ℂ, ‖(-evenCoeff zetaZeroConfig (boxSpline 1 3) z)‖) * C *
        Real.exp ((1 / 2 + |α|) * B - T) ≤
      ∑' z : ℂ, ((-evenCoeff zetaZeroConfig (boxSpline 1 3) z) *
        sourceTransform (fun x => (k x : ℂ)) (I * z) *
        Complex.exp ((z - (α : ℂ)) * t)).re := by
  let c : ℂ → ℂ := fun z => -evenCoeff zetaZeroConfig (boxSpline 1 3) z
  let A : ℝ := ∑' z, ‖c z‖
  let D : ℝ := 1 / 2 + |α|
  let b : ℝ := D + |α|
  let κ : ℝ → ℝ := fun x => Real.exp (α * x) * k x
  let F : ℝ → ℝ := fun u => Real.exp (-α * u) *
    (-(2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb0 : 0 ≤ b := add_nonneg hD (abs_nonneg α)
  have hc : Summable (fun z => ‖c z‖) := by
    simpa only [c, norm_neg] using summable_norm_evenCoeff_spline temperedConfig_zetaZeroConfig
  have hw : ∀ z, c z ≠ 0 → |(z - (α : ℂ)).re| ≤ D :=
    fun z hz => configuration_shifted_exponent_bound α (neg_ne_zero.mp hz)
  have hseries (u : ℝ) : F u = ∑' z, (c z * Complex.exp ((z - (α : ℂ)) * u)).re :=
    by simpa only [F, c, neg_mul, mul_neg, Complex.neg_re, tsum_neg] using
      congrArg (fun x : ℝ => -x)
        (configuration_shifted_trace_series temperedConfig_zetaZeroConfig α u)
  have hFc : Continuous F := by
    have hc := continuous_two_re_lagStructure temperedConfig_zetaZeroConfig
    dsimp [F]
    fun_prop
  have hFbound (u : ℝ) : |F u| ≤ A * Real.exp (D * |u|) := by
    rw [hseries]
    exact abs_cexp_series_le c (fun z => z - (α : ℂ)) hc hw u
  have hκc : Continuous κ := by dsimp [κ]; fun_prop
  have hκ (x : ℝ) : 0 < κ x := mul_pos (Real.exp_pos _) (hk x)
  have hκm (s : ℝ) : Integrable fun x => Real.exp (s * |x|) * |κ x| :=
    integrable_tilted_abs_moment hkc hm α s
  have hκi : Integrable κ := by
    simpa only [zero_mul, Real.exp_zero, one_mul, abs_of_pos (hκ _)] using hκm 0
  have hκT : Integrable fun x => Real.exp ((D + T) * |x|) * κ x := by
    simpa only [abs_of_pos (hκ _)] using hκm (D + T)
  have hFi : Integrable fun x => κ x * F (t + x) :=
    integrable_kernel_of_strip_bound (A := A)
      (by dsimp [A]; positivity) hD hFc hκc (hκm D) hFbound t
  have hmoment : (∫ x, Real.exp ((D + T) * |x|) * κ x) ≤
      C * Real.exp ((b + T + 6) * Real.log (b + T + 6)) := by
    have hh := tilted_abs_moment_le hkc hm α (D + T)
    change (∫ x, Real.exp ((D + T) * |x|) * |κ x|) ≤
      ∫ x, Real.exp ((D + T + |α|) * |x|) * |k x| at hh
    simp only [abs_of_pos (hκ _), abs_of_pos (hk _)] at hh
    have he : D + T + |α| = b + T := by dsimp [b]; ring
    rw [he] at hh
    exact hh.trans (hb (b + T) (by linarith only [hb0, hT]))
  have hfloor := positive_kernel_logarithmic_floor (F := F) (k := κ) (A := A)
    (by dsimp [A]; positivity) hC.le hb0
    (show b ≤ T by dsimp [b, D]; linarith only [hbT]) hD hK hT
    (show D + 1 ≤ Real.log (T + 2) by dsimp [D]; linarith only [hE]) ht
    (fun x => (hκ x).le) hκi hκT hFi hFbound hmoment
    (fun x hx => hlocal (t + x) (by simpa only [add_sub_cancel_left] using hx))
  have hconv : (∫ x, κ x * F (t + x)) =
      ∑' z : ℂ, (c z * sourceTransform (fun x => (k x : ℂ)) (I * z) *
        Complex.exp ((z - (α : ℂ)) * t)).re := by
    simp_rw [hseries]
    rw [integral_kernel_cexp_tsum c (fun z => z - (α : ℂ)) hD hc hw hκc hκm t]
    apply tsum_congr
    intro z
    dsimp only [κ]
    rw [integral_tilt_cexp_shift, ← sourceTransform_I_mul_eq_laplace]
  rw [hconv] at hfloor
  exact hfloor

/-- An upper bound on arbitrarily late logarithmic windows detects every deeper zeta zero. -/
theorem zeta_re_le_of_upper_logarithmic_windows {α K : ℝ} (hα : 0 ≤ α)
    (hwindow : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ,
      |u - T| ≤ 16 * Real.log (T + 2) →
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re ≤ K * Real.exp (α * u)) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + α := by
  classical
  intro ρ hρ
  by_contra hρle
  have hρdeep : 1 / 2 + α < ρ.re := lt_of_not_ge hρle
  let z₀ : ℂ := ρ - 1 / 2
  let c : ℂ → ℂ := fun z => -evenCoeff zetaZeroConfig (boxSpline 1 3) z
  let D : ℝ := 1 / 2 + |α|
  have hc₀ : c z₀ ≠ 0 := neg_ne_zero.mpr
    (evenCoeff_spline_sees hρ (by linarith only [hρdeep, hα]))
  have hz₀pos : 0 < z₀.re := by
    dsimp only [z₀]
    simp only [Complex.sub_re]
    norm_num
    linarith only [hρdeep, hα]
  obtain ⟨k, Ck, S, hCk, hkc, hk, hm, hb, hkeep, hdelete⟩ :=
    exists_zeta_quartet_log_filter (neg_ne_zero.mp hc₀) hz₀pos
  let d : ℂ → ℂ := fun z => c z * sourceTransform (fun x => (k x : ℂ)) (I * z)
  have hdout : ∀ z ∉ S, d z = 0 := by
    intro z hz
    by_cases hcz : c z = 0
    · simp only [d, hcz, zero_mul]
    change c z * sourceTransform (fun x => (k x : ℂ)) (I * z) = 0
    rw [hdelete z hz (neg_ne_zero.mp hcz), mul_zero]
  let R : Finset ℂ := S.filter fun z => d z ≠ 0
  have hmem (z : ℂ) : z ∈ R ↔ d z ≠ 0 := by
    simp only [R, Finset.mem_filter]
    exact ⟨fun hz => hz.2, fun hz => ⟨by_contra fun hn => hz (hdout z hn), hz⟩⟩
  have hdconj (z : ℂ) : d (conj z) = conj (d z) := by
    simp only [d, c, evenCoeff_conj, sourceTransform_I_mul_conj, map_mul, map_neg]
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
    exact evenCoeff_spline_real (neg_ne_zero.mp hcz)
  have hz₀R : z₀ ∈ R := (hmem z₀).mpr (mul_ne_zero hc₀ hkeep)
  obtain ⟨z₁, hz₁, hmax⟩ := R.exists_max_image Complex.re ⟨z₀, hz₀R⟩
  have hβα : 0 < z₁.re - α := by
    have hh := hmax z₀ hz₀R
    dsimp only [z₀] at hh
    simp only [Complex.sub_re] at hh
    norm_num at hh
    linarith only [hρdeep, hh]
  obtain ⟨B, η, U₀, hB, hη, hnegative⟩ := finite_spectrum_dense_negative R d
    hRconj (fun z _ => hdconj z) hRreal hz₁ ((hmem z₁).mp hz₁) hmax
  let A : ℝ := ∑' z, ‖c z‖
  let M : ℝ := ∫ x, Real.exp (α * x) * k x
  have hleak : Tendsto (fun T : ℝ => A * Ck * Real.exp (D * B - T)) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (A * Ck * Real.exp (D * B))
    simpa only [mul_zero, sub_eq_add_neg, Real.exp_add, mul_assoc] using ht
  have hgrowth : Tendsto (fun T : ℝ => η * Real.exp ((z₁.re - α) * T)) atTop atTop := by
    simpa only [Function.comp_def, id_eq] using
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hβα)).const_mul_atTop hη
  let C : ℝ := max 1 (max (3 / 2 + |α|) (B / 8))
  let V : ℝ := max U₀ (max (1 / 2 + 2 * |α|) (max 6 (Real.exp C)))
  have hlate : ∀ᶠ T : ℝ in atTop, V ≤ T ∧
      A * Ck * Real.exp (D * B - T) ≤ 1 ∧ |K| * M + 1 < η * Real.exp ((z₁.re - α) * T) := by
    filter_upwards [eventually_ge_atTop V,
      hleak.eventually_le_const (by norm_num : (0 : ℝ) < 1),
      hgrowth.eventually_gt_atTop (|K| * M + 1)] with T hV hE hG
    exact ⟨hV, hE, hG⟩
  obtain ⟨U, hU⟩ := eventually_atTop.mp hlate
  obtain ⟨T, hTU, hbound⟩ := hwindow U
  obtain ⟨hTV, herror, hgrow⟩ := hU T hTU
  simp only [V, max_le_iff] at hTV
  obtain ⟨hTU₀, hbT, hT₆, hTC⟩ := hTV
  have hT : 0 ≤ T := by linarith only [hT₆]
  have hEC : C ≤ Real.log (T + 2) := by
    have hh := Real.log_le_log (Real.exp_pos C)
      (show Real.exp C ≤ T + 2 by linarith only [hTC])
    rwa [Real.log_exp] at hh
  have hED : 3 / 2 + |α| ≤ Real.log (T + 2) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hEC)
  have hspan : B ≤ 8 * Real.log (T + 2) := by
    have hh : B / 8 ≤ Real.log (T + 2) :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hEC)
    linarith only [hh]
  obtain ⟨t, ht, hneg⟩ := hnegative T hTU₀
  have ht0 : 0 ≤ t := hT.trans ht.1
  have htB : |t| ≤ T + B := by rw [abs_of_nonneg ht0]; exact ht.2
  have hlocal : ∀ u, |u - t| ≤ 8 * Real.log (T + 2) →
      -|K| ≤ Real.exp (-α * u) *
        (-(2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re)) := by
    intro u hu
    have htT : |t - T| ≤ B := abs_le.mpr ⟨by linarith only [ht.1, hB], by linarith only [ht.2]⟩
    have huT : |u - T| ≤ 16 * Real.log (T + 2) := by
      have htri : |u - T| ≤ |u - t| + |t - T| := by
        calc |u - T| = |(u - t) + (t - T)| := by congr 1; ring
          _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_add_le (u - t) (t - T)
      linarith only [htri, htT, hu, hspan]
    have hh := mul_le_mul_of_nonneg_left (neg_le_neg (hbound u huT)) (Real.exp_pos (-α * u)).le
    have he : Real.exp (-α * u) * (-(K * Real.exp (α * u))) = -K := by
      have hp : Real.exp (-α * u) * Real.exp (α * u) = 1 := by
        rw [← Real.exp_add]
        simp only [neg_mul, neg_add_cancel, Real.exp_zero]
      calc _ = -K * (Real.exp (-α * u) * Real.exp (α * u)) := by ring
        _ = _ := by rw [hp, mul_one]
    rw [he] at hh
    exact (neg_le_neg (le_abs_self K)).trans hh
  have hfloor := zeta_negative_kernel_logarithmic_floor hCk hkc hk hm hb α
    (abs_nonneg K) hT₆ hbT hED htB hlocal
  have hsum : (∑' z : ℂ, (d z * Complex.exp ((z - (α : ℂ)) * t)).re) =
      (∑ z ∈ R, d z * Complex.exp ((z - (α : ℂ)) * t)).re := by
    rw [tsum_eq_sum (s := R) (fun z hz => by
      have hd : d z = 0 := by_contra fun hn => hz ((hmem z).mpr hn)
      simp only [hd, zero_mul, Complex.zero_re])]
    exact (map_sum Complex.reCLM (fun z => d z * Complex.exp ((z - (α : ℂ)) * t)) R).symm
  change -|K| * M - A * Ck * Real.exp (D * B - T) ≤
    ∑' z : ℂ, (d z * Complex.exp ((z - (α : ℂ)) * t)).re at hfloor
  rw [hsum] at hfloor
  have hlower : -(|K| * M + 1) ≤ (∑ z ∈ R, d z * Complex.exp ((z - (α : ℂ)) * t)).re := by
    linarith only [hfloor, herror]
  have hscaled := mul_le_mul_of_nonneg_right hlower (Real.exp_pos (α * t)).le
  rw [finite_sum_cexp_scale] at hscaled
  have hgt : |K| * M + 1 < η * Real.exp ((z₁.re - α) * t) :=
    hgrow.trans_le (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.1 hβα.le)) hη.le)
  have hmul := mul_lt_mul_of_pos_right hgt (Real.exp_pos (α * t))
  have he : Real.exp (z₁.re * t) = Real.exp ((z₁.re - α) * t) * Real.exp (α * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hneg
  nlinarith only [hscaled, hneg, hmul]


end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

