import GaloisForLFunctions.ArithmeticProduction.TheGaussianAveragingOfTheWindow
import GaloisForLFunctions.RHTower.SmoothDiagonalContour
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorAdmissibleContour
import GaloisForLFunctions.RHTower.DirichletPolynomialLineSmallValues

/-!
# The interpolation at a large height

The analytic inputs of the necessary-length law, at heights `t₀ ∈ [T, 2T]` with window width `w = log²T`:

* the body `ζ(s)M(s)(s−1)/(s+1)` compared with `ζM` on the two relevant lines (`linePower_zero_le`, `le_linePower_left`);
* the tail of the window outside `[T, 2T]` (`exists_center_tail`, `center_remainder_le_of_small`);
* the spectrum outside the band, uniformly in the mollifier (`remainder_le_of_small`);
* the error of the right floor (`right_floor_error_le_of_small`);
* horizontal slices free of zeros and the left floor at the height `T` (`exists_admissible_slices`, `exists_left_floor_of_small`);
* every estimate is stated with explicit smallness conditions, so that the exponent `θ` may grow with `T`;
* the arithmetic of the interpolation at `aΛ = log 2` (`final_numeric`).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower

/-! ### Comparison of the body with `ζM` -/

/-- On the line, the body is at most `ζM`. -/
theorem linePower_zero_le (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    linePower b N 0 t ≤ ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  unfold linePower
  rw [add_zero]
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have hne : s ≠ 1 := by
    intro h
    rw [h] at hre
    norm_num at hre
  have hne' : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hre] at this
    linarith
  have hratio : ‖s - 1‖ / ‖s + 1‖ ≤ 1 := by
    rw [div_le_one (norm_pos_iff.mpr hne'), ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.one_im, hre]
    nlinarith
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  unfold windowBody
  rw [zetaEntire_eq hne, norm_div, norm_mul, norm_mul, norm_mul]
  calc ‖s - 1‖ * ‖riemannZeta s‖ * ‖edPoly b (Finset.Icc 1 N) s‖ / ‖s + 1‖
      = (‖s - 1‖ / ‖s + 1‖) * (‖riemannZeta s‖ * ‖edPoly b (Finset.Icc 1 N) s‖) := by ring
    _ ≤ 1 * (‖riemannZeta s‖ * ‖edPoly b (Finset.Icc 1 N) s‖) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := one_mul _

/-- Left of the line, the body is `ζM` up to `1 − 4/t²`. -/
theorem le_linePower_left (b : ℕ → ℂ) (N : ℕ) {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (ht : 2 ≤ t) :
    (1 - 4 / t ^ 2) * ‖riemannZeta (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      linePower b N (-a) t := by
  unfold linePower
  rw [show (1 / 2 + -a : ℝ) = 1 / 2 - a by ring]
  set s : ℂ := ((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = 1 / 2 - a := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hne : s ≠ 1 := by
    intro h
    rw [h] at him
    simp at him
    linarith
  have hne' : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hre] at this
    linarith
  have ht2 : 0 < t ^ 2 := by positivity
  have hn1 : t ^ 2 ≤ ‖s - 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hre, him]
    nlinarith [sq_nonneg (1 / 2 - a - 1)]
  have hn2 : ‖s + 1‖ ^ 2 ≤ t ^ 2 + 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, hre, him]
    nlinarith
  have hpos : 0 < ‖s + 1‖ := norm_pos_iff.mpr hne'
  have hratio : 1 - 4 / t ^ 2 ≤ ‖s - 1‖ ^ 2 / ‖s + 1‖ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h4 : (1 - 4 / t ^ 2) * (t ^ 2 + 4) ≤ t ^ 2 := by
      have : (1 - 4 / t ^ 2) * (t ^ 2 + 4) = t ^ 2 - 16 / t ^ 2 := by
        field_simp
        ring
      rw [this]
      have : 0 ≤ 16 / t ^ 2 := by positivity
      linarith
    by_cases hsign : 0 ≤ 1 - 4 / t ^ 2
    · calc (1 - 4 / t ^ 2) * ‖s + 1‖ ^ 2 ≤ (1 - 4 / t ^ 2) * (t ^ 2 + 4) :=
            mul_le_mul_of_nonneg_left hn2 hsign
        _ ≤ t ^ 2 := h4
        _ ≤ _ := hn1
    · have h5 : (1 - 4 / t ^ 2) * ‖s + 1‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_le.mp hsign).le (by positivity)
      exact h5.trans (by positivity)
  unfold windowBody
  have hX : 0 ≤ ‖riemannZeta s * edPoly b (Finset.Icc 1 N) s‖ ^ 2 := by positivity
  have hval : ‖(s - 1) * riemannZeta s * edPoly b (Finset.Icc 1 N) s / (s + 1)‖ ^ 2 =
      (‖s - 1‖ ^ 2 / ‖s + 1‖ ^ 2) * ‖riemannZeta s * edPoly b (Finset.Icc 1 N) s‖ ^ 2 := by
    rw [mul_assoc, norm_div, norm_mul, div_pow, mul_pow]
    ring
  rw [zetaEntire_eq hne, hval]
  exact mul_le_mul_of_nonneg_right hratio hX

/-! ### The spectrum at the centre -/

/-- The window on the line, outside a long interval, is negligible. -/
theorem exists_center_tail :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (t₀ : ℝ) {w R T₃ T₄ : ℝ} (_ : 0 < w) (_ : 0 ≤ R) (_ : T₃ + R ≤ t₀)
      (_ : t₀ + R ≤ T₄) {b : ℕ → ℂ} {N : ℕ} (_ : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1),
      ∫ t, ‖lineFun (mollifiedWindow t₀ w b N) 0 t‖ ^ 2 ≤
        (∫ t in T₃..T₄, linePower b N 0 t * gaussKernel w t t₀) +
          Cc * (N : ℝ) ^ (3 : ℝ) * ((2 * (1 + |t₀|) ^ 2 * (1 + 4 * w ^ 2)) ^ 2 * 2 * Real.exp 1) *
            Real.exp (-(R ^ 2 / (4 * w ^ 2))) * (w * √(2 * Real.pi)) := by
  obtain ⟨C, hC, hζ⟩ := exists_norm_riemannZeta_le_leftStrip
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro t₀ w R T₃ T₄ hw hR h3 h4 b N hb
  obtain ⟨Cs, hCs⟩ := exists_stripDecay_mollifiedWindow t₀ hw hb
  have h0mem : (0 : ℝ) ∈ Icc (-1 : ℝ) (3 / 2) := ⟨by norm_num, by norm_num⟩
  have hint : Integrable fun t => ‖lineFun (mollifiedWindow t₀ w b N) 0 t‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm (hCs.continuous_lineFun h0mem).aestronglyMeasurable).mp
      (hCs.memLp_two_lineFun h0mem)
  have hval : ∀ t, ‖lineFun (mollifiedWindow t₀ w b N) 0 t‖ ^ 2 =
      linePower b N 0 t * gaussKernel w t t₀ := by
    intro t
    rw [norm_sq_lineFun_mollifiedWindow t₀ hw]
    simp
  have hT34 : T₃ ≤ T₄ := by linarith
  have hsplit := integral_add_compl (measurableSet_Ioc (a := T₃) (b := T₄)) hint
  rw [← hsplit, intervalIntegral.integral_of_le hT34]
  refine add_le_add (le_of_eq (setIntegral_congr_fun measurableSet_Ioc fun t _ => hval t)) ?_
  set S : ℝ := C ^ 2 * (N : ℝ) ^ (3 : ℝ) *
    ((2 * (1 + |t₀|) ^ 2 * (1 + 4 * w ^ 2)) ^ 2 * 2 * Real.exp 1) *
      Real.exp (-(R ^ 2 / (4 * w ^ 2))) with hS
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hw' : 0 < √2 * w := by positivity
  have hsq : 2 * (√2 * w) ^ 2 = 4 * w ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hg : Integrable fun t : ℝ => S * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) :=
    (integrable_gauss t₀ hw).const_mul S
  have hle : ∫ t in (Ioc T₃ T₄)ᶜ, ‖lineFun (mollifiedWindow t₀ w b N) 0 t‖ ^ 2 ≤
      ∫ t in (Ioc T₃ T₄)ᶜ, S * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) := by
    refine setIntegral_mono_on hint.integrableOn hg.integrableOn measurableSet_Ioc.compl
      fun t ht => ?_
    rw [hval]
    have hdist : R ^ 2 ≤ (t - t₀) ^ 2 := by
      have hnot : ¬ (T₃ < t ∧ t ≤ T₄) := ht
      by_cases h1 : t ≤ T₃
      · have h2 : R ≤ t₀ - t := by linarith
        have h5 := pow_le_pow_left₀ hR h2 2
        have h6 : (t₀ - t) ^ 2 = (t - t₀) ^ 2 := by ring
        rwa [h6] at h5
      · have h2 : T₄ < t := by
          by_contra h5
          exact hnot ⟨not_le.mp h1, not_lt.mp h5⟩
        have h5 : R ≤ t - t₀ := by linarith
        exact pow_le_pow_left₀ hR h5 2
    -- the body on the line
    have hbody : linePower b N 0 t ≤ C ^ 2 * (1 + |t|) ^ (2 * 2) * (N : ℝ) ^ (3 : ℝ) := by
      refine (linePower_zero_le b N t).trans ?_
      have hz := hζ (1 / 2) t (by norm_num) (by norm_num)
      have hM := norm_edPoly_le_three_halves hb
        (s := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (by simp)
      have hprod : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
          (C * (1 + |t|) ^ 2) * (N : ℝ) ^ ((3 : ℝ) / 2) := by
        rw [norm_mul]
        exact mul_le_mul hz hM (norm_nonneg _) (by positivity)
      refine (pow_le_pow_left₀ (norm_nonneg _) hprod 2).trans (le_of_eq ?_)
      have hN : ((N : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (N : ℝ) ^ (3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
        norm_num
      rw [mul_pow, mul_pow, hN, ← pow_mul]
    -- the Gaussian splits into three
    have hsup := one_add_abs_pow_mul_gauss_le 2 t₀ t hw'
    rw [hsq] at hsup
    have hsup' : (1 + |t|) ^ (2 * 2) * Real.exp (-((t - t₀) ^ 2 / (4 * w ^ 2))) ≤
        (2 * (1 + |t₀|) ^ 2 * (1 + 4 * w ^ 2)) ^ 2 * 2 * Real.exp 1 := by
      refine hsup.trans (le_of_eq ?_)
      norm_num
    have hsplitK : gaussKernel w t t₀ = Real.exp (-((t - t₀) ^ 2 / (4 * w ^ 2))) *
        (Real.exp (-((t - t₀) ^ 2 / (4 * w ^ 2))) * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2)))) := by
      unfold gaussKernel
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      field_simp
      ring
    have hfar : Real.exp (-((t - t₀) ^ 2 / (4 * w ^ 2))) ≤ Real.exp (-(R ^ 2 / (4 * w ^ 2))) := by
      refine Real.exp_le_exp.mpr (neg_le_neg ?_)
      exact div_le_div_of_nonneg_right hdist (by positivity)
    have hE := Real.exp_pos (-((t - t₀) ^ 2 / (2 * w ^ 2)))
    have hE4 := Real.exp_pos (-((t - t₀) ^ 2 / (4 * w ^ 2)))
    calc linePower b N 0 t * gaussKernel w t t₀
        ≤ (C ^ 2 * (1 + |t|) ^ (2 * 2) * (N : ℝ) ^ (3 : ℝ)) * gaussKernel w t t₀ :=
          mul_le_mul_of_nonneg_right hbody (gaussKernel_pos _ _ _).le
      _ = C ^ 2 * (N : ℝ) ^ (3 : ℝ) *
            ((1 + |t|) ^ (2 * 2) * Real.exp (-((t - t₀) ^ 2 / (4 * w ^ 2)))) *
              Real.exp (-((t - t₀) ^ 2 / (4 * w ^ 2))) *
                Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) := by
          rw [hsplitK]
          ring
      _ ≤ C ^ 2 * (N : ℝ) ^ (3 : ℝ) *
            ((2 * (1 + |t₀|) ^ 2 * (1 + 4 * w ^ 2)) ^ 2 * 2 * Real.exp 1) *
              Real.exp (-(R ^ 2 / (4 * w ^ 2))) *
                Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) := by
          refine mul_le_mul_of_nonneg_right ?_ hE.le
          refine mul_le_mul (mul_le_mul_of_nonneg_left hsup' (by positivity)) hfar hE4.le
            (by positivity)
      _ = S * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) := by rw [hS]
  refine hle.trans ?_
  have hle2 := setIntegral_le_integral (s := (Ioc T₃ T₄)ᶜ) hg
    (Filter.Eventually.of_forall fun t => by
      show 0 ≤ _
      positivity)
  have hRHS : ∫ t : ℝ, S * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) = S * (w * √(2 * Real.pi)) := by
    rw [integral_const_mul, integral_gauss t₀ hw]
  rw [hRHS] at hle2
  exact hle2

/-! ### Eventual smallness -/

/-- `(log T)^k T^{−c}` tends to `0`. -/
theorem eventually_log_pow_mul_exp_le (k : ℕ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, Real.log T ^ k * Real.exp (-(c * Real.log T)) ≤ ε := by
  have h1 : Tendsto (fun x : ℝ => (c * x) ^ k * Real.exp (-(c * x))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp (tendsto_id.const_mul_atTop hc)
  have h2 : Tendsto (fun x : ℝ => (c ^ k)⁻¹ * ((c * x) ^ k * Real.exp (-(c * x)))) atTop (𝓝 0) := by
    simpa using h1.const_mul ((c ^ k)⁻¹)
  have h3 := (h2.comp Real.tendsto_log_atTop).eventually (Iio_mem_nhds hε)
  filter_upwards [h3] with T hT
  simp only [Function.comp_apply] at hT
  have hck : c ^ k ≠ 0 := by positivity
  have hval : (c ^ k)⁻¹ * ((c * Real.log T) ^ k * Real.exp (-(c * Real.log T))) =
      Real.log T ^ k * Real.exp (-(c * Real.log T)) := by
    rw [mul_pow]
    field_simp
  rw [hval] at hT
  exact (mem_Iio.mp hT).le

/-! ### The final numerics -/

/-- The arithmetic of the interpolation at `aΛ = log 2`. -/
theorem final_numeric {p ε x y z T J : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hε : ε = p / 2000)
    (hx : x = Real.exp ((1 - p / 100) * Real.log 2))
    (hy : y = Real.exp (-((1 - p / 100) * Real.log 2)))
    (hz : z = Real.exp (99 / 100 * p * Real.log 2)) (hT : 0 < T)
    (h : (1 - ε) ^ 2 * x * T + y * ((1 - ε) ^ 3 * z * T) ≤ 5 / 2 * J + 2 * ε * T) :
    (1 + 129 / 1000 * p) * T ≤ J := by
  set u := Real.log 2 with hu
  have hu1 : 0.6931 < u := by
    have := Real.log_two_gt_d9
    linarith
  have hu2 : u < 0.6932 := by
    have := Real.log_two_lt_d9
    linarith
  have hexpu : Real.exp u = 2 := Real.exp_log two_pos
  have hexpnegu : Real.exp (-u) = 1 / 2 := by
    rw [Real.exp_neg, hexpu]
    norm_num
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hε1 : ε ≤ 1 / 2000 := by rw [hε]; linarith
  set w := y * z with hw
  have hwval : w = 1 / 2 * Real.exp (p * u) := by
    rw [hw, hy, hz, ← Real.exp_add]
    have : -((1 - p / 100) * u) + 99 / 100 * p * u = -u + p * u := by ring
    rw [this, Real.exp_add, hexpnegu]
  have hxval : x = 2 * Real.exp (-(p / 100 * u)) := by
    rw [hx]
    have : (1 - p / 100) * u = u + -(p / 100 * u) := by ring
    rw [this, Real.exp_add, hexpu]
  have hxlow : 2 * (1 - p / 100 * u) ≤ x := by
    rw [hxval]
    have := Real.add_one_le_exp (-(p / 100 * u))
    linarith
  have hxup : x ≤ 2 := by
    rw [hxval]
    have : Real.exp (-(p / 100 * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ p / 100 * u := by positivity
      linarith)
    linarith
  have hwlow : 1 / 2 * (1 + p * u) ≤ w := by
    rw [hwval]
    have := Real.add_one_le_exp (p * u)
    linarith
  have hu0 : 0 ≤ u := by linarith
  have hwup : w ≤ 1 := by
    rw [hwval]
    have h1 : Real.exp (p * u) ≤ Real.exp u :=
      Real.exp_le_exp.mpr (mul_le_of_le_one_left hu0 hp1)
    rw [hexpu] at h1
    linarith
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hw0 : 0 ≤ w := by rw [hwval]; positivity
  have h1 : 1 - 2 * ε ≤ (1 - ε) ^ 2 := by
    have h3 : (1 - ε) ^ 2 = 1 - 2 * ε + ε ^ 2 := by ring
    rw [h3]
    linarith [sq_nonneg ε]
  have h2 : 1 - 3 * ε ≤ (1 - ε) ^ 3 := by
    have h3 : (1 - ε) ^ 3 = 1 - 3 * ε + 3 * ε ^ 2 - ε ^ 3 := by ring
    have h4 : ε ^ 3 ≤ 3 * ε ^ 2 := by
      have h5 : ε ^ 3 = ε ^ 2 * ε := by ring
      have h6 : ε ≤ 3 := by linarith
      have h7 := mul_le_mul_of_nonneg_left h6 (sq_nonneg ε)
      linarith
    linarith
  have hlow1 : x - 4 * ε ≤ (1 - ε) ^ 2 * x := by
    have h3 := mul_le_mul_of_nonneg_right h1 hx0
    have h4 : ε * x ≤ ε * 2 := mul_le_mul_of_nonneg_left hxup hε0
    have h5 : (1 - 2 * ε) * x = x - 2 * (ε * x) := by ring
    linarith
  have hlow2 : w - 3 * ε ≤ (1 - ε) ^ 3 * w := by
    have h3 := mul_le_mul_of_nonneg_right h2 hw0
    have h4 : ε * w ≤ ε * 1 := mul_le_mul_of_nonneg_left hwup hε0
    have h5 : (1 - 3 * ε) * w = w - 3 * (ε * w) := by ring
    linarith
  have hsum : (x - 4 * ε + (w - 3 * ε)) * T ≤ 5 / 2 * J + 2 * ε * T := by
    calc (x - 4 * ε + (w - 3 * ε)) * T ≤ ((1 - ε) ^ 2 * x + (1 - ε) ^ 3 * w) * T :=
          mul_le_mul_of_nonneg_right (add_le_add hlow1 hlow2) hT.le
      _ = (1 - ε) ^ 2 * x * T + y * ((1 - ε) ^ 3 * z * T) := by rw [hw]; ring
      _ ≤ _ := h
  have hval : 5 / 2 + 323 / 1000 * p ≤ x + w - 9 * ε := by
    rw [hε]
    have h3 : p * 0.6931 ≤ p * u := mul_le_mul_of_nonneg_left hu1.le hp.le
    have h4 : p / 100 * u = p * u / 100 := by ring
    rw [h4] at hxlow
    linarith
  have hfinal : (5 / 2 + 323 / 1000 * p) * T ≤ 5 / 2 * J := by
    have h3 := mul_le_mul_of_nonneg_right hval hT.le
    have h4 : (x + w - 9 * ε) * T = (x - 4 * ε + (w - 3 * ε)) * T - 2 * ε * T := by ring
    linarith
  have hp2 : 0 ≤ p * T := by positivity
  linarith

/-! ### The remainder of the interpolation -/

/-- `exp x ≤ 3` for `x ≤ 1`. -/
private theorem exp_le_three {x : ℝ} (hx : x ≤ 1) : Real.exp x ≤ 3 := by
  have h1 : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx
  have h2 := Real.exp_one_lt_d9
  linarith

/-- The part of the spectrum right of the band. -/
private theorem remainder_right_le {w c L a ℓ : ℝ} (hw4 : 4 ≤ w) (hc2 : c ^ 2 = 2 * Real.pi)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hℓ0 : 0 < ℓ) (hexpLa : Real.exp (L * a) ≤ 2) :
    (4 * Real.exp (9 / 4 / (2 * w ^ 2)) * (w * c)) ^ 2 * Real.exp (L * a) *
        Real.exp (-(2 * (ℓ / 100) * (3 / 2 - a))) / (2 * Real.pi * (3 / 2 - a)) ≤
      288 * w ^ 2 * Real.exp (-(1 / 50 * ℓ)) := by
  have hπ := Real.pi_pos
  have hw0 : 0 < w := by linarith
  have hw16 : (16 : ℝ) ≤ w ^ 2 := by
    calc (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ w ^ 2 := pow_le_pow_left₀ (by norm_num) hw4 2
  have hE₁ : Real.exp (9 / 4 / (2 * w ^ 2)) ≤ 3 := by
    refine exp_le_three ?_
    rw [div_le_one (by positivity)]
    linarith
  have hd : 2 * Real.pi ≤ 2 * Real.pi * (3 / 2 - a) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have hE2 : Real.exp (-(2 * (ℓ / 100) * (3 / 2 - a))) ≤ Real.exp (-(1 / 50 * ℓ)) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : 2 * (ℓ / 100) * 1 ≤ 2 * (ℓ / 100) * (3 / 2 - a) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hsq : (4 * Real.exp (9 / 4 / (2 * w ^ 2)) * (w * c)) ^ 2 ≤ 144 * w ^ 2 * (2 * Real.pi) := by
    have h3 : (4 * Real.exp (9 / 4 / (2 * w ^ 2)) * (w * c)) ^ 2 =
        16 * Real.exp (9 / 4 / (2 * w ^ 2)) ^ 2 * (w ^ 2 * c ^ 2) := by ring
    rw [h3, hc2]
    have h4 : Real.exp (9 / 4 / (2 * w ^ 2)) ^ 2 ≤ 3 ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hE₁ 2
    have h5 : 0 ≤ w ^ 2 * (2 * Real.pi) := by positivity
    calc 16 * Real.exp (9 / 4 / (2 * w ^ 2)) ^ 2 * (w ^ 2 * (2 * Real.pi))
        ≤ 16 * 3 ^ 2 * (w ^ 2 * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num)) h5
      _ = _ := by ring
  have hd0 : 0 < 2 * Real.pi * (3 / 2 - a) := mul_pos (by positivity) (by linarith)
  rw [div_le_iff₀ hd0]
  calc (4 * Real.exp (9 / 4 / (2 * w ^ 2)) * (w * c)) ^ 2 * Real.exp (L * a) *
        Real.exp (-(2 * (ℓ / 100) * (3 / 2 - a)))
      ≤ (144 * w ^ 2 * (2 * Real.pi)) * 2 * Real.exp (-(1 / 50 * ℓ)) :=
        mul_le_mul (mul_le_mul hsq hexpLa (Real.exp_pos _).le (by positivity)) hE2
          (Real.exp_pos _).le (by positivity)
    _ = 288 * w ^ 2 * Real.exp (-(1 / 50 * ℓ)) * (2 * Real.pi) := by ring
    _ ≤ 288 * w ^ 2 * Real.exp (-(1 / 50 * ℓ)) * (2 * Real.pi * (3 / 2 - a)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)

/-- The size of the coefficient of the part of the spectrum left of the band. -/
private theorem remainder_left_square_le {A θ T ℓ w c t₀ : ℝ} {N : ℕ} (hT0 : 0 < T) (hT1 : 1 ≤ T)
    (hℓdef : ℓ = Real.log T) (hw4 : 4 ≤ w) (hc : c = √(2 * Real.pi)) (ht1 : T ≤ t₀) (ht2 : t₀ ≤ 2 * T)
    (hN : (N : ℝ) ≤ T ^ θ) :
    (A * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * w ^ 2)) *
        (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c))) ^ 2 ≤
      A ^ 2 * 9 * 432 ^ 2 * Real.exp (3 * θ * ℓ) * T ^ 4 * w ^ 6 := by
  have hw0 : 0 < w := by linarith
  have hw16 : (16 : ℝ) ≤ w ^ 2 := by
    calc (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ w ^ 2 := pow_le_pow_left₀ (by norm_num) hw4 2
  have hc0 : 0 < c := by rw [hc]; positivity
  have hsqrtπ2 : √Real.pi ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith [Real.pi_le_four]⟩
  have hE₂ : Real.exp (1 / (2 * w ^ 2)) ≤ 3 := by
    refine exp_le_three ?_
    rw [div_le_one (by positivity)]
    linarith
  have ht0 : 0 ≤ t₀ := by linarith
  have ht3 : (1 + |t₀|) ^ 2 ≤ 9 * T ^ 2 := by
    rw [abs_of_nonneg ht0]
    have h3 : 1 + t₀ ≤ 3 * T := by linarith
    calc (1 + t₀) ^ 2 ≤ (3 * T) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
      _ = 9 * T ^ 2 := by ring
  have hw3 : 1 + 2 * w ^ 2 ≤ 3 * w ^ 2 := by linarith
  have hsq2 : √2 * w * c ≤ 4 * w := by
    have h3 : √(2 : ℝ) * c = 2 * √Real.pi := by
      rw [hc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have h4 : √2 * w * c = w * (√(2 : ℝ) * c) := by ring
    rw [h4, h3]
    calc w * (2 * √Real.pi) ≤ w * (2 * 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hw0.le
      _ = 4 * w := by ring
  have hY : 4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c) ≤ 432 * T ^ 2 * w ^ 3 := by
    calc 4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c)
        ≤ 4 * (9 * T ^ 2) * (3 * w ^ 2) * (4 * w) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left ht3 (by norm_num)) hw3
            (by positivity) (by positivity)) hsq2 (by positivity) (by positivity)
      _ = 432 * T ^ 2 * w ^ 3 := by ring
  have hN3 : ((N : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 ≤ Real.exp (3 * θ * ℓ) := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h3 : ((N : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (N : ℝ) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0, ← Real.rpow_natCast]
      norm_num
    rw [h3]
    have h4 : (T ^ θ) ^ (3 : ℕ) = Real.exp (3 * θ * ℓ) := by
      rw [Real.rpow_def_of_pos hT0, ← Real.exp_nat_mul, ← hℓdef]
      congr 1
      push_cast
      ring
    rw [← h4]
    exact pow_le_pow_left₀ hN0 hN 3
  have h3 : (A * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * w ^ 2)) *
      (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c))) ^ 2 =
      A ^ 2 * ((N : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 * Real.exp (1 / (2 * w ^ 2)) ^ 2 *
        (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c)) ^ 2 := by ring
  rw [h3]
  have h4 : Real.exp (1 / (2 * w ^ 2)) ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le hE₂ 2
  have h5 : (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c)) ^ 2 ≤ (432 * T ^ 2 * w ^ 3) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hY 2
  calc A ^ 2 * ((N : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 * Real.exp (1 / (2 * w ^ 2)) ^ 2 *
        (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c)) ^ 2
      ≤ A ^ 2 * Real.exp (3 * θ * ℓ) * 3 ^ 2 * (432 * T ^ 2 * w ^ 3) ^ 2 := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hN3 (by positivity)) h4
          (by positivity) (by positivity)) h5 (by positivity) (by positivity)
    _ = _ := by ring

/-- The part of the spectrum left of the band. -/
private theorem remainder_left_le {A θ T ℓ w c L a t₀ B₁ : ℝ} {N : ℕ} (hT0 : 0 < T) (hT1 : 1 ≤ T)
    (hℓdef : ℓ = Real.log T) (hw4 : 4 ≤ w) (hc : c = √(2 * Real.pi)) (ha1 : a ≤ 1 / 4)
    (ht1 : T ≤ t₀) (ht2 : t₀ ≤ 2 * T) (hN : (N : ℝ) ≤ T ^ θ)
    (hL : L = (2 + 3 / 2 * θ + 1 / 100) * ℓ) (hLa0 : 0 ≤ L * a)
    (hLBa : (L + ℓ / 100) * a ≤ Real.log 2) (hB₁ : B₁ = 4 * (A ^ 2 * 9 * 432 ^ 2)) :
    (A * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * w ^ 2)) *
        (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c))) ^ 2 * Real.exp (-(L * a)) *
        Real.exp (-(2 * (L + ℓ / 100) * (1 - a))) / (2 * Real.pi * (1 - a)) ≤
      B₁ * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) := by
  have hX := remainder_left_square_le (A := A) (c := c) (t₀ := t₀) hT0 hT1 hℓdef hw4 hc ht1 ht2 hN
  have hw0 : 0 < w := by linarith
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
  have hTexp : T = Real.exp ℓ := by rw [hℓdef, Real.exp_log hT0]
  have hπ3 := Real.pi_gt_three
  have hd : (1 : ℝ) ≤ 2 * Real.pi * (1 - a) := by
    have h3 : 2 * 3 * (3 / 4 : ℝ) ≤ 2 * Real.pi * (1 - a) :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (by positivity)
    linarith
  have hE3 : Real.exp (-(L * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE4 : Real.exp (-(2 * (L + ℓ / 100) * (1 - a))) ≤
      4 * Real.exp (-(2 * (L + ℓ / 100))) := by
    have h3 : -(2 * (L + ℓ / 100) * (1 - a)) = 2 * ((L + ℓ / 100) * a) + -(2 * (L + ℓ / 100)) := by ring
    rw [h3, Real.exp_add]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have h4 : 2 * ((L + ℓ / 100) * a) ≤ Real.log 4 := by
      have h5 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [h5]
      linarith
    have h6 := Real.exp_le_exp.mpr h4
    rwa [Real.exp_log (by norm_num)] at h6
  have hexpmain : Real.exp (3 * θ * ℓ) * T ^ 4 * Real.exp (-(2 * (L + ℓ / 100))) =
      Real.exp (-(1 / 25 * ℓ)) := by
    rw [hTexp, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, hL]
    congr 1
    push_cast
    ring
  rw [div_le_iff₀ (by linarith)]
  have hnn : 0 ≤ B₁ * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) := by positivity
  calc _ ≤ (A ^ 2 * 9 * 432 ^ 2 * Real.exp (3 * θ * ℓ) * T ^ 4 * w ^ 6) * 1 *
          (4 * Real.exp (-(2 * (L + ℓ / 100)))) :=
        mul_le_mul (mul_le_mul hX hE3 (Real.exp_pos _).le (by positivity)) hE4
          (Real.exp_pos _).le (by positivity)
    _ = B₁ * w ^ 6 * (Real.exp (3 * θ * ℓ) * T ^ 4 * Real.exp (-(2 * (L + ℓ / 100)))) := by
        rw [hB₁]
        ring
    _ = B₁ * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) := by rw [hexpmain]
    _ ≤ B₁ * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) * (2 * Real.pi * (1 - a)) :=
        le_mul_of_one_le_right hnn hd

/-- **The spectrum outside the band is negligible**, uniformly in the mollifier and in the exponent. -/
theorem remainder_le_of_small {θ A ε T : ℝ} (hθ : 0 < θ) (hε : 0 < ε)
    (h1 : Real.log T ^ 2 * Real.exp (-(1 / 50 * Real.log T)) ≤ ε / (2 * 288))
    (h2 : Real.log T ^ 10 * Real.exp (-(1 / 25 * Real.log T)) ≤
      ε / (2 * (4 * (A ^ 2 * 9 * 432 ^ 2) + 1)))
    (hℓ : 2 ≤ Real.log T) (hT1 : 1 < T) (N : ℕ) (t₀ a : ℝ) (hN : (N : ℝ) ≤ T ^ θ) (ht1 : T ≤ t₀)
    (ht2 : t₀ ≤ 2 * T) (ha0 : 0 < a) (ha1 : a ≤ 1 / 4)
    (haq : a * ((2 + 3 / 2 * θ + 3 / 100) * Real.log T) = Real.log 2) :
    (4 * Real.exp (9 / 4 / (2 * (Real.log T ^ 2) ^ 2)) * (Real.log T ^ 2 * √(2 * Real.pi))) ^ 2 *
          Real.exp ((2 + 3 / 2 * θ + 1 / 100) * Real.log T * a) *
          Real.exp (-(2 * (Real.log T / 100) * (3 / 2 - a))) / (2 * Real.pi * (3 / 2 - a)) +
        (A * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * (Real.log T ^ 2) ^ 2)) *
            (4 * (1 + |t₀|) ^ 2 * (1 + 2 * (Real.log T ^ 2) ^ 2) *
              (√2 * Real.log T ^ 2 * √(2 * Real.pi)))) ^ 2 *
          Real.exp (-((2 + 3 / 2 * θ + 1 / 100) * Real.log T * a)) *
          Real.exp (-(2 * ((2 + 3 / 2 * θ + 1 / 100) * Real.log T + Real.log T / 100) * (1 - a))) /
            (2 * Real.pi * (1 - a)) ≤
      ε * (Real.log T ^ 2 * √Real.pi) := by
  obtain ⟨B₁, hB₁⟩ : ∃ B₁ : ℝ, B₁ = 4 * (A ^ 2 * 9 * 432 ^ 2) := ⟨_, rfl⟩
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
  rw [← hB₁] at h2
  set ℓ := Real.log T with hℓdef
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  set w := ℓ ^ 2 with hw
  have hw4 : 4 ≤ w := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := pow_le_pow_left₀ (by norm_num) hℓ 2
  have hw0 : 0 < w := by linarith
  set L := (2 + 3 / 2 * θ + 1 / 100) * ℓ with hL
  have hLq : L + 2 * (ℓ / 100) = (2 + 3 / 2 * θ + 3 / 100) * ℓ := by
    rw [hL]
    ring
  have hLa : L * a ≤ Real.log 2 := by
    rw [← haq]
    have h3 : L ≤ (2 + 3 / 2 * θ + 3 / 100) * ℓ := by
      rw [← hLq]
      linarith
    rw [mul_comm a]
    exact mul_le_mul_of_nonneg_right h3 ha0.le
  have hLBa : (L + ℓ / 100) * a ≤ Real.log 2 := by
    rw [← haq]
    have h3 : L + ℓ / 100 ≤ (2 + 3 / 2 * θ + 3 / 100) * ℓ := by
      rw [← hLq]
      linarith
    rw [mul_comm a]
    exact mul_le_mul_of_nonneg_right h3 ha0.le
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hLa0 : 0 ≤ L * a := by positivity
  have hexpLa : Real.exp (L * a) ≤ 2 := by
    have := Real.exp_le_exp.mpr hLa
    rwa [Real.exp_log two_pos] at this
  have hπ := Real.pi_pos
  set c := √(2 * Real.pi) with hc
  have hc2 : c ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hsqrtπ : 1 ≤ √Real.pi := by
    rw [Real.one_le_sqrt]
    linarith [Real.pi_gt_three]
  refine (add_le_add (remainder_right_le hw4 hc2 ha0 ha1 hℓ0 hexpLa)
    (remainder_left_le hT0 hT1.le hℓdef hw4 hc ha1 ht1 ht2 hN hL hLa0 hLBa hB₁)).trans ?_
  -- compare with the target
  have hw2 : w ^ 2 = w * ℓ ^ 2 := by rw [hw]; ring
  have hfirst : 288 * w ^ 2 * Real.exp (-(1 / 50 * ℓ)) ≤ ε / 2 * w := by
    have h3 : 288 * (ℓ ^ 2 * Real.exp (-(1 / 50 * ℓ))) ≤ ε / 2 := by
      have h4 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 288)
      have h5 : 288 * (ε / (2 * 288)) = ε / 2 := by ring
      linarith
    calc 288 * w ^ 2 * Real.exp (-(1 / 50 * ℓ)) = w * (288 * (ℓ ^ 2 * Real.exp (-(1 / 50 * ℓ)))) := by
          rw [hw2]
          ring
      _ ≤ w * (ε / 2) := mul_le_mul_of_nonneg_left h3 hw0.le
      _ = _ := by ring
  have hsecond : B₁ * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) ≤ ε / 2 * w := by
    have h3 : B₁ * (ℓ ^ 10 * Real.exp (-(1 / 25 * ℓ))) ≤ ε / 2 := by
      have h4 : B₁ * (ε / (2 * (B₁ + 1))) ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      exact (mul_le_mul_of_nonneg_left h2 hB₁0).trans h4
    calc B₁ * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) = w * (B₁ * (ℓ ^ 10 * Real.exp (-(1 / 25 * ℓ)))) := by
          rw [hw]
          ring
      _ ≤ w * (ε / 2) := mul_le_mul_of_nonneg_left h3 hw0.le
      _ = _ := by ring
  have hw' : ε * w ≤ ε * (w * √Real.pi) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hw0.le hsqrtπ) hε.le
  linarith

/-! ### The right floor at a large height -/

/-- The far line of the right floor at precision `ε`. -/
def rightFloorParam (ε : ℝ) : ℝ := max 5 (Real.log (152 / ε) / Real.log 2)

theorem five_le_rightFloorParam (ε : ℝ) : 5 ≤ rightFloorParam ε := le_max_left _ _

/-- At the far line `rightFloorParam ε` the right-floor error is at most `ε`, under explicit smallness. -/
theorem right_floor_error_le_of_small {ε T t₀ : ℝ} (hε : 0 < ε)
    (h1 : Real.log T ^ 4 * Real.exp (-(1 * Real.log T)) ≤ 1 / 16) (hT8 : 128 / ε ≤ T) (hT96 : 96 / ε ≤ T)
    (hT1 : 1 < T) (hw : 2 * (rightFloorParam ε - 1 / 2) ^ 2 + 1 ≤ (Real.log T ^ 2) ^ 2)
    (hℓ : 1 ≤ Real.log T) (ht : T ≤ t₀) :
    Real.exp ((rightFloorParam ε - 1 / 2) ^ 2 / (Real.log T ^ 2) ^ 2) *
      (19 * Real.exp (-(Real.log 2 * rightFloorParam ε)) + 8 / t₀ +
        6 * Real.exp (-(t₀ ^ 2 / (8 * (Real.log T ^ 2) ^ 2)))) ≤ ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = rightFloorParam ε := ⟨_, rfl⟩
  rw [← hK] at hw ⊢
  have hK5 : 5 ≤ K := by rw [hK]; exact five_le_rightFloorParam ε
  have hη : 19 * Real.exp (-(Real.log 2 * K)) ≤ ε / 8 := by
    have h1 : Real.log (152 / ε) ≤ Real.log 2 * K := by
      have h2 : Real.log (152 / ε) / Real.log 2 ≤ K := by
        rw [hK]
        exact le_max_right _ _
      rw [div_le_iff₀ hlog2] at h2
      linarith
    have h3 : Real.exp (-(Real.log 2 * K)) ≤ Real.exp (-Real.log (152 / ε)) :=
      Real.exp_le_exp.mpr (neg_le_neg h1)
    rw [Real.exp_neg (Real.log (152 / ε)), Real.exp_log (by positivity)] at h3
    have h4 : (152 / ε)⁻¹ = ε / 152 := by
      rw [inv_div]
    rw [h4] at h3
    linarith
  set ℓ := Real.log T with hℓdef
  have hT0 : 0 < T := by linarith
  set w := ℓ ^ 2 with hwdef
  have hw2 : 0 < w ^ 2 := by
    have : 0 < 2 * (K - 1 / 2) ^ 2 + 1 := by positivity
    linarith
  have ht0 : 0 < t₀ := by linarith
  -- the exponential prefactor
  have hG : Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) ≤ 2 := by
    have h2 : (K - 1 / 2) ^ 2 / w ^ 2 ≤ Real.log 2 := by
      rw [div_le_iff₀ hw2]
      have h3 := Real.log_two_gt_d9
      have h4 : (K - 1 / 2) ^ 2 ≤ w ^ 2 / 2 := by linarith
      nlinarith
    have h5 := Real.exp_le_exp.mpr h2
    rwa [Real.exp_log two_pos] at h5
  have h8 : 8 / t₀ ≤ ε / 16 := by
    rw [div_le_iff₀ ht0]
    have h3 : 128 / ε ≤ t₀ := hT8.trans ht
    rw [div_le_iff₀ hε] at h3
    linarith
  -- the Gaussian tail
  have hTexp : Real.exp (-ℓ) = T⁻¹ := by
    rw [Real.exp_neg, hℓdef, Real.exp_log hT0]
  have hw4T : 16 * w ^ 2 ≤ T := by
    have h3 : ℓ ^ 4 * T⁻¹ ≤ 1 / 16 := by
      have h4 := h1
      simp only [one_mul] at h4
      rwa [hTexp] at h4
    have hw' : w ^ 2 = ℓ ^ 4 := by rw [hwdef]; ring
    rw [hw']
    rw [← div_eq_mul_inv, div_le_iff₀ hT0] at h3
    linarith
  have h6 : 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2))) ≤ ε / 16 := by
    have h3 : T ≤ t₀ ^ 2 / (8 * w ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have hT1' : 1 ≤ T := hT1.le
      calc T * (8 * w ^ 2) ≤ T * T := mul_le_mul_of_nonneg_left (by linarith) hT0.le
        _ ≤ t₀ * t₀ := mul_le_mul ht ht hT0.le ht0.le
        _ = t₀ ^ 2 := by ring
    have h4 : Real.exp (-(t₀ ^ 2 / (8 * w ^ 2))) ≤ Real.exp (-T) :=
      Real.exp_le_exp.mpr (neg_le_neg h3)
    have h5 : Real.exp (-T) ≤ T⁻¹ := by
      rw [Real.exp_neg]
      refine inv_anti₀ hT0 ?_
      linarith [Real.add_one_le_exp T]
    have h7 : T⁻¹ ≤ ε / 96 := by
      rw [inv_le_comm₀ hT0 (by positivity)]
      calc (ε / 96)⁻¹ = 96 / ε := by rw [inv_div]
        _ ≤ T := hT96
    linarith
  have hsum : 19 * Real.exp (-(Real.log 2 * K)) + 8 / t₀ + 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2))) ≤
      ε / 4 := by linarith
  have hnn : 0 ≤ 19 * Real.exp (-(Real.log 2 * K)) + 8 / t₀ +
      6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2))) := by positivity
  calc _ ≤ 2 * (ε / 4) := mul_le_mul hG hsum hnn (by norm_num)
    _ ≤ ε := by linarith

/-! ### The left floor at a large height -/

/-- Heights with horizontal segments free of zeros of `ζ` and `M`. -/
theorem exists_admissible_slices {b : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (hb1 : b 1 = 1)
    (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) {A₁ B₁ A₂ B₂ : ℝ} (h20 : 20 ≤ A₁) (h1 : A₁ < B₁)
    (h2 : B₁ < A₂) (h3 : A₂ < B₂) :
    ∃ T₁ ∈ Ioo A₁ B₁, ∃ T₂ ∈ Ioo A₂ B₂,
      (∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 ∧
        edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 ∧
        edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) := by
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  set F : ℂ → ℂ := fun z => zetaEntire z * edPoly b (Finset.Icc 1 N) z with hF
  have hFd : Differentiable ℂ F := differentiable_zetaEntire.mul (differentiable_edPoly _ hs)
  have hFan : AnalyticOnNhd ℂ F Set.univ := hFd.differentiableOn.analyticOnNhd isOpen_univ
  have hFne : ∃ z : ℂ, F z ≠ 0 := by
    refine ⟨((15 / 2 : ℝ) : ℂ), mul_ne_zero ?_ ?_⟩
    · rw [zetaEntire_eq (by intro h; have := congrArg Complex.re h; simp at this; norm_num at this)]
      refine mul_ne_zero (by intro h; have := congrArg Complex.re h; simp at this; norm_num at this) ?_
      exact riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)
    · intro h0
      have h := norm_edPoly_sub_one_le_half_of_six_le b hs
        (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) hb1 hb (z := ((15 / 2 : ℝ) : ℂ)) (by simp; norm_num)
      rw [h0] at h
      norm_num at h
  obtain ⟨T₁, hT₁, T₂, hT₂, hF1, hF2⟩ :=
    exists_horizontal_slices_avoiding_entire_zeros hFan hFne (c := (1 / 4 : ℝ)) (d := 15 / 2)
      (by norm_num) h1 h2 h3
  have hedge : ∀ T : ℝ, 20 ≤ T →
      (∀ x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2), F ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      ∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 ∧
        edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
    intro T hT hFT x hx
    have hx' : x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2) := by
      rw [Set.uIcc_of_le (by norm_num)]
      exact hx
    have hne1 : ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hFx := hFT x hx'
    simp only [hF] at hFx
    rw [zetaEntire_eq hne1] at hFx
    exact ⟨fun h0 => hFx (by rw [h0]; ring), fun h0 => hFx (by rw [h0]; ring)⟩
  exact ⟨T₁, hT₁, T₂, hT₂, hedge T₁ (by linarith [hT₁.1]) hF1,
    hedge T₂ (by linarith [hT₂.1, hT₁.2]) hF2⟩

/-- `Σ_{n ≤ N} |b_n| n⁴ ≤ N⁵`. -/
theorem sum_norm_mul_rpow_four_le {b : ℕ → ℂ} {N : ℕ} (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ (N : ℝ) ^ 5 := by
  have hterm : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ)) ≤ (N : ℝ) ^ 4 := by
    intro n hn
    obtain ⟨-, h2⟩ := Finset.mem_Icc.mp hn
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast h2
    have h3 : (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h3]
    calc ‖b n‖ * (n : ℝ) ^ 4 ≤ 1 * (N : ℝ) ^ 4 :=
          mul_le_mul (hb n hn) (pow_le_pow_left₀ (Nat.cast_nonneg n) hnN 4) (by positivity)
            (by norm_num)
      _ = _ := one_mul _
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans (le_of_eq ?_)
  simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  ring

/-- The Riemann–von Mangoldt count between heights near `T` and near `2T`. -/
theorem eventually_zero_count_increment :
    ∀ᶠ T : ℝ in atTop, ∀ T₁ T₂ : ℝ, T ≤ T₁ → T₁ ≤ 1001 / 1000 * T → 1999 / 1000 * T ≤ T₂ → T₂ ≤ 2 * T →
      996 / 1000 * (T * Real.log T) ≤
        2 * Real.pi * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) := by
  have hπ := Real.pi_pos
  set ε' : ℝ := (1 / 10000) / (2 * Real.pi) with hε'
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  obtain ⟨T₀, -, hrvm⟩ := exists_xiZeroCount_close ε' hε'0
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (20 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT₀ hT20 hℓ1 T₁ T₂ h1a h1b h2a h2b
  set ℓ := Real.log T with hℓdef
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hT₁0 : 0 < T₁ := by linarith
  have hT₂0 : 0 < T₂ := by linarith
  have hcast : ∀ U : ℝ, 0 ≤ U → ((xiZeroCount U : ℤ) : ℝ) = (xiPosZeroCount U : ℝ) := by
    intro U hU
    rw [← xiPosZeroCount_eq_xiZeroCount hU]
    simp
  have hN₂ := hrvm T₂ (by linarith)
  have hN₁ := hrvm T₁ (by linarith)
  rw [hcast T₂ hT₂0.le] at hN₂
  rw [hcast T₁ hT₁0.le] at hN₁
  have hlog₂ : ℓ ≤ Real.log T₂ := Real.log_le_log hT0 (by linarith)
  have hlog₁0 : 0 ≤ Real.log T₁ := Real.log_nonneg (by linarith)
  have hlog₁ : Real.log T₁ ≤ ℓ + 1 / 1000 := by
    have h3 : Real.log T₁ ≤ Real.log (1001 / 1000 * T) := Real.log_le_log hT₁0 h1b
    rw [Real.log_mul (by norm_num) hT0.ne'] at h3
    have h4 : Real.log (1001 / 1000 : ℝ) ≤ 1001 / 1000 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have h2π : 2 * Real.pi * ε' = 1 / 10000 := by
    rw [hε']
    field_simp
  set x₂ := T₂ * Real.log T₂ with hx₂
  set x₁ := T₁ * Real.log T₁ with hx₁
  have hx₂low : 1999 / 1000 * (T * ℓ) ≤ x₂ := by
    calc 1999 / 1000 * (T * ℓ) = (1999 / 1000 * T) * ℓ := by ring
      _ ≤ T₂ * Real.log T₂ := mul_le_mul h2a hlog₂ hℓ0.le hT₂0.le
  have hx₁up : x₁ ≤ 1001 / 1000 * T * (ℓ + 1 / 1000) :=
    mul_le_mul h1b hlog₁ hlog₁0 (by positivity)
  have hinv : 2 * Real.pi * (1 / (2 * Real.pi)) = 1 := by field_simp
  have hN₂low : (1 - 1 / 10000) * x₂ ≤ 2 * Real.pi * (xiPosZeroCount T₂ : ℝ) := by
    have h3 := (abs_le.mp hN₂).1
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 2 * Real.pi)
    have h5 : 2 * Real.pi * (-(ε' * x₂)) = -((1 / 10000) * x₂) := by rw [← h2π]; ring
    have h6 : 2 * Real.pi * ((xiPosZeroCount T₂ : ℝ) - 1 / (2 * Real.pi) * x₂) =
        2 * Real.pi * (xiPosZeroCount T₂ : ℝ) - (2 * Real.pi * (1 / (2 * Real.pi))) * x₂ := by ring
    rw [h5, h6, hinv] at h4
    linarith
  have hN₁up : 2 * Real.pi * (xiPosZeroCount T₁ : ℝ) ≤ (1 + 1 / 10000) * x₁ := by
    have h3 := (abs_le.mp hN₁).2
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 2 * Real.pi)
    have h5 : 2 * Real.pi * (ε' * x₁) = (1 / 10000) * x₁ := by rw [← h2π]; ring
    have h6 : 2 * Real.pi * ((xiPosZeroCount T₁ : ℝ) - 1 / (2 * Real.pi) * x₁) =
        2 * Real.pi * (xiPosZeroCount T₁ : ℝ) - (2 * Real.pi * (1 / (2 * Real.pi))) * x₁ := by ring
    rw [h5, h6, hinv] at h4
    linarith
  have h3 : 2 * Real.pi * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) =
      2 * Real.pi * (xiPosZeroCount T₂ : ℝ) - 2 * Real.pi * (xiPosZeroCount T₁ : ℝ) := by ring
  rw [h3]
  have hT1 : T ≤ T * ℓ := le_mul_of_one_le_right hT0.le hℓ1
  have h4 : 1001 / 1000 * T * (ℓ + 1 / 1000) = 1001 / 1000 * (T * ℓ) + 1001 / 1000000 * T := by ring
  rw [h4] at hx₁up
  linarith

/-- The lower-order terms of the left floor are negligible against the count. -/
private theorem left_floor_small {θ C K₁ v T T₂ ℓ : ℝ} {N : ℕ} (hθ : 0 < θ) (hC : 0 < C) (hK₁ : 0 < K₁)
    (hv0 : 0 < v) (hT0 : 0 < T) (hℓdef : ℓ = Real.log T) (hℓ1 : 1 ≤ ℓ) (hN : 1 ≤ N)
    (hNT : (N : ℝ) ≤ T ^ θ) (hT₂0 : 0 < T₂) (h2b : T₂ ≤ 2 * T)
    (hs : ℓ ^ 1 * Real.exp (-(1 * ℓ)) ≤ 6 / 1000 * v / (2 * (K₁ * (1 + 5 * θ) + C + K₁ + 1))) :
    C + K₁ * (Real.log T₂ + Real.log ((N : ℝ) ^ 5)) ≤ 6 / 1000 * (v * T) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hlogMb : Real.log ((N : ℝ) ^ 5) ≤ 5 * θ * ℓ := by
    rw [Real.log_pow]
    have hN1 : (0 : ℝ) < N := by exact_mod_cast hN
    have h3 : Real.log N ≤ Real.log (T ^ θ) := Real.log_le_log hN1 hNT
    rw [Real.log_rpow hT0, ← hℓdef] at h3
    push_cast
    linarith
  have hlog₂up : Real.log T₂ ≤ ℓ + 1 := by
    have h3 : Real.log T₂ ≤ Real.log (2 * T) := Real.log_le_log hT₂0 h2b
    rw [Real.log_mul two_ne_zero hT0.ne', ← hℓdef] at h3
    have h4 := Real.log_two_lt_d9
    linarith
  have hTe : Real.exp (-(1 * ℓ)) = T⁻¹ := by
    rw [one_mul, Real.exp_neg, hℓdef, Real.exp_log hT0]
  have h3 := hs
  rw [hTe, pow_one, ← div_eq_mul_inv, div_le_iff₀ hT0] at h3
  obtain ⟨D₀, hD₀⟩ : ∃ D₀ : ℝ, D₀ = K₁ * (1 + 5 * θ) + C + K₁ + 1 := ⟨_, rfl⟩
  rw [← hD₀] at h3
  have hD₀0 : 0 < D₀ := by rw [hD₀]; positivity
  have h4 : D₀ * ℓ ≤ 6 / 1000 * (v * T) / 2 := by
    have h5 := mul_le_mul_of_nonneg_left h3 hD₀0.le
    have h6 : D₀ * (6 / 1000 * v / (2 * D₀) * T) = 6 / 1000 * (v * T) / 2 := by
      field_simp
    linarith
  have h7 : K₁ * (Real.log T₂ + Real.log ((N : ℝ) ^ 5)) ≤ K₁ * (ℓ + 1 + 5 * θ * ℓ) :=
    mul_le_mul_of_nonneg_left (by linarith) hK₁.le
  have h8 : C + K₁ * (ℓ + 1 + 5 * θ * ℓ) ≤ D₀ * ℓ := by
    rw [hD₀]
    have h9 : 0 ≤ C * (ℓ - 1) := mul_nonneg hC.le (by linarith)
    have h10 : 0 ≤ K₁ * (ℓ - 1) := mul_nonneg hK₁.le (by linarith)
    linarith
  have hvT : 0 ≤ 6 / 1000 * (v * T) := by positivity
  linarith

/-- The exponent of the left floor. -/
private theorem left_floor_exponent {q v T X δ : ℝ} (hv : v = Real.log 2 / q) (hv0 : 0 < v) (hT0 : 0 < T)
    (hδ0 : 0 < δ) (hδ : δ ≤ T) (hXlow : 99 / 100 * (v * T) ≤ X) :
    99 / 100 * (2 / q) * Real.log 2 ≤ 2 / δ * X := by
  have hexp : 99 / 100 * (2 / q) * Real.log 2 = 2 * (99 / 100) * v := by
    rw [hv]
    ring
  rw [hexp]
  have h3 : 2 / T ≤ 2 / δ := div_le_div_of_nonneg_left (by norm_num) hδ0 hδ
  have h4 : 2 / T * (99 / 100 * (v * T)) ≤ 2 / δ * X :=
    mul_le_mul h3 hXlow (by positivity) (by positivity)
  have h5 : 2 / T * (99 / 100 * (v * T)) = 2 * (99 / 100) * v := by
    field_simp
  linarith

/-- **The left floor at a large height.**  Between heights near `T` and `2T`, the mollified second moment left of the line is at least
`(T₂ − T₁) 2^{0.99 p}`, `p = 2/q`, `a q log T = log 2`, uniformly in real mollifiers of length `T^θ`, under explicit smallness. -/
theorem exists_left_floor_of_small :
    ∃ C K₁ : ℝ, 0 < C ∧ 0 < K₁ ∧ ∀ θ T : ℝ, 0 < θ →
      Real.log T ^ 1 * Real.exp (-(1 * Real.log T)) ≤
        6 / 1000 * (Real.log 2 / (2 + 3 / 2 * θ + 3 / 100)) / (2 * (K₁ * (1 + 5 * θ) + C + K₁ + 1)) →
      (∀ T₁ T₂ : ℝ, T ≤ T₁ → T₁ ≤ 1001 / 1000 * T → 1999 / 1000 * T ≤ T₂ → T₂ ≤ 2 * T →
        996 / 1000 * (T * Real.log T) ≤ 2 * Real.pi * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)) →
      20 ≤ T → 1 ≤ Real.log T →
      ∀ (b : ℕ → ℂ) (N : ℕ) (a T₁ T₂ : ℝ), 1 ≤ N → (N : ℝ) ≤ T ^ θ → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      0 < a → a ≤ 1 / 4 → a * ((2 + 3 / 2 * θ + 3 / 100) * Real.log T) = Real.log 2 →
      T ≤ T₁ → T₁ ≤ 1001 / 1000 * T → 1999 / 1000 * T ≤ T₂ → T₂ ≤ 2 * T →
      (∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 ∧
        edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
      (∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 ∧
        edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      (T₂ - T₁) * Real.exp (99 / 100 * (2 / (2 + 3 / 2 * θ + 3 / 100)) * Real.log 2) ≤
        ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨C, K₁, hC, hK₁, hfloor⟩ := exists_left_floor
  refine ⟨C, K₁, hC, hK₁, ?_⟩
  intro θ T hθ hs hcount0 hT20 hℓ1 b N a T₁ T₂ hN hNT hb1 hb hbr ha0 ha1 haq h1a h1b h2a h2b hs1 hs2
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 2 + 3 / 2 * θ + 3 / 100 := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = Real.log 2 / q := ⟨_, rfl⟩
  have hv0 : 0 < v := by rw [hv]; positivity
  rw [← hq, ← hv] at hs
  rw [← hq] at haq ⊢
  have hT0 : 0 < T := by linarith
  have haℓ : a * Real.log T = v := by
    rw [hv, ← haq, eq_div_iff hq0.ne']
    ring
  have hT12 : T₁ < T₂ := by linarith
  have hlen0 : 0 < T₂ - T₁ := by linarith
  have hlen : T₂ - T₁ ≤ T := by linarith
  have hT₂0 : 0 < T₂ := by linarith
  have hcount := hcount0 T₁ T₂ h1a h1b h2a h2b
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁ := ⟨_, rfl⟩
  rw [← hΔ] at hcount
  have hMb1 : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hN)
  have hmainterm : 996 / 1000 * (v * T) ≤ 2 * Real.pi * (a * Δ) := by
    have h3 := mul_le_mul_of_nonneg_left hcount ha0.le
    have h4 : a * (996 / 1000 * (T * Real.log T)) = 996 / 1000 * ((a * Real.log T) * T) := by ring
    rw [h4, haℓ] at h3
    have h5 : a * (2 * Real.pi * Δ) = 2 * Real.pi * (a * Δ) := by ring
    linarith
  have hsmallK := left_floor_small (N := N) (T₂ := T₂) hθ hC hK₁ hv0 hT0 rfl hℓ1 hN hNT hT₂0 h2b hs
  obtain ⟨X, hX⟩ : ∃ X : ℝ,
      X = 2 * Real.pi * (a * Δ) - C - K₁ * (Real.log T₂ + Real.log ((N : ℝ) ^ 5)) := ⟨_, rfl⟩
  have hXlow : 99 / 100 * (v * T) ≤ X := by
    rw [hX]
    linarith
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hXlow
  have hfl := hfloor b N hN hb1 hb hbr ((N : ℝ) ^ 5) hMb1 (sum_norm_mul_rpow_four_le hb) a T₁ T₂ ha0 ha1
    (by linarith) hT12 (fun x hx => (hs1 x hx).1) (fun x hx => (hs2 x hx).1)
    (fun x hx => (hs1 x hx).2) (fun x hx => (hs2 x hx).2) (by rw [← hΔ, ← hX]; exact hXpos)
  rw [← hΔ, ← hX] at hfl
  exact le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (left_floor_exponent hv hv0 hT0 hlen0 hlen hXlow)) hlen0.le) hfl

/-! ### The tail of the window on the critical line -/

/-- The tail of the window outside `[T, 2T]` at distance `log³T` is negligible: the Gaussian `exp(−log²T/4)` beats `T^{4+3θ}` as soon as `log T ≥ 4(3θ+5)`. -/
theorem center_remainder_le_of_small {θ Cc ε T : ℝ} (hCc : 0 ≤ Cc)
    (hT1 : Real.log T ^ 8 * Real.exp (-(1 * Real.log T)) ≤
      ε / (Cc * 8100 * (2 * Real.exp 1) * 2 + 1))
    (hℓ : 4 * (3 * θ + 5) ≤ Real.log T) (hℓ1 : 1 ≤ Real.log T) (hT : 1 ≤ T) (N : ℕ) (t₀ : ℝ)
    (hN : (N : ℝ) ≤ T ^ θ) (ht₁ : T ≤ t₀) (ht₂ : t₀ ≤ 2 * T) :
    Cc * (N : ℝ) ^ (3 : ℝ) *
        ((2 * (1 + |t₀|) ^ 2 * (1 + 4 * (Real.log T ^ 2) ^ 2)) ^ 2 * 2 * Real.exp 1) *
        Real.exp (-((Real.log T ^ 3) ^ 2 / (4 * (Real.log T ^ 2) ^ 2))) *
        (Real.log T ^ 2 * √(2 * Real.pi)) ≤
      ε * (Real.log T ^ 2 * √Real.pi) := by
  set C' : ℝ := Cc * 8100 * (2 * Real.exp 1) * 2 with hC'
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  set ℓ := Real.log T with hℓdef
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hTexp : Real.exp ℓ = T := Real.exp_log hT0
  have hℓne : ℓ ≠ 0 := hℓ0.ne'
  -- the Gaussian
  have hgauss : (ℓ ^ 3) ^ 2 / (4 * (ℓ ^ 2) ^ 2) = ℓ ^ 2 / 4 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    ring
  -- the length
  have hN3 : (N : ℝ) ^ (3 : ℝ) ≤ Real.exp (3 * θ * ℓ) := by
    have h1 := Real.rpow_le_rpow (Nat.cast_nonneg N) hN (by norm_num : (0 : ℝ) ≤ 3)
    refine h1.trans (le_of_eq ?_)
    rw [← Real.rpow_mul hT0.le, Real.rpow_def_of_pos hT0]
    congr 1
    ring
  -- the height
  have ht0 : |t₀| ≤ 2 * T := by
    rw [abs_of_nonneg (by linarith)]
    exact ht₂
  have hbase : 2 * (1 + |t₀|) ^ 2 * (1 + 4 * (ℓ ^ 2) ^ 2) ≤ 90 * T ^ 2 * ℓ ^ 4 := by
    have h1 : (1 + |t₀|) ^ 2 ≤ 9 * T ^ 2 := by
      have h2 : 1 + |t₀| ≤ 3 * T := by linarith
      calc (1 + |t₀|) ^ 2 ≤ (3 * T) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
        _ = _ := by ring
    have h3 : 1 + 4 * (ℓ ^ 2) ^ 2 ≤ 5 * ℓ ^ 4 := by
      have h4 : 1 ≤ ℓ ^ 4 := one_le_pow₀ hℓ1
      have h5 : (ℓ ^ 2) ^ 2 = ℓ ^ 4 := by ring
      rw [h5]
      linarith
    calc 2 * (1 + |t₀|) ^ 2 * (1 + 4 * (ℓ ^ 2) ^ 2) ≤ 2 * (9 * T ^ 2) * (5 * ℓ ^ 4) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h3 (by positivity) (by positivity)
      _ = _ := by ring
  have hbase2 : (2 * (1 + |t₀|) ^ 2 * (1 + 4 * (ℓ ^ 2) ^ 2)) ^ 2 ≤ 8100 * Real.exp (4 * ℓ) * ℓ ^ 8 := by
    refine (pow_le_pow_left₀ (by positivity) hbase 2).trans (le_of_eq ?_)
    have hT4 : Real.exp (4 * ℓ) = T ^ 4 := by
      rw [← hTexp, ← Real.exp_nat_mul]
      norm_num
    rw [hT4]
    ring
  -- the exponents
  have hexpo : Real.exp (3 * θ * ℓ) * Real.exp (4 * ℓ) * Real.exp (-(ℓ ^ 2 / 4)) ≤ Real.exp (-(1 * ℓ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : 4 * (3 * θ + 5) * ℓ ≤ ℓ * ℓ := mul_le_mul_of_nonneg_right hℓ hℓ0.le
    have h2 : ℓ ^ 2 = ℓ * ℓ := by ring
    rw [h2]
    linarith
  have hsqrt : √(2 * Real.pi) ≤ 2 * √Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right
      (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (Real.sqrt_nonneg _)
  have hsmall2 : C' * (ℓ ^ 8 * Real.exp (-(1 * ℓ))) ≤ ε := by
    have h1 : (C' + 1) * (ℓ ^ 8 * Real.exp (-(1 * ℓ))) ≤ (C' + 1) * (ε / (C' + 1)) :=
      mul_le_mul_of_nonneg_left hT1 (by positivity)
    rw [mul_div_cancel₀ _ (by positivity)] at h1
    have h2 : 0 ≤ ℓ ^ 8 * Real.exp (-(1 * ℓ)) := by positivity
    linarith
  rw [hgauss]
  have hW : 0 ≤ ℓ ^ 2 * √Real.pi := by positivity
  have he1 : 0 ≤ 2 * Real.exp 1 := by positivity
  calc Cc * (N : ℝ) ^ (3 : ℝ) * ((2 * (1 + |t₀|) ^ 2 * (1 + 4 * (ℓ ^ 2) ^ 2)) ^ 2 * 2 * Real.exp 1) *
        Real.exp (-(ℓ ^ 2 / 4)) * (ℓ ^ 2 * √(2 * Real.pi))
      ≤ Cc * Real.exp (3 * θ * ℓ) * ((8100 * Real.exp (4 * ℓ) * ℓ ^ 8) * 2 * Real.exp 1) *
          Real.exp (-(ℓ ^ 2 / 4)) * (ℓ ^ 2 * (2 * √Real.pi)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul
          (mul_le_mul_of_nonneg_left hN3 hCc) ?_ (by positivity) (by positivity)) (by positivity))
          (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbase2 (by norm_num)) (by positivity)
    _ = C' * (ℓ ^ 8 * (Real.exp (3 * θ * ℓ) * Real.exp (4 * ℓ) * Real.exp (-(ℓ ^ 2 / 4)))) *
          (ℓ ^ 2 * √Real.pi) := by
        rw [hC']
        ring
    _ ≤ C' * (ℓ ^ 8 * Real.exp (-(1 * ℓ))) * (ℓ ^ 2 * √Real.pi) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC'0) hW
        exact mul_le_mul_of_nonneg_left hexpo (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall2 hW

end GaloisForLFunctions.ArithmeticProduction
