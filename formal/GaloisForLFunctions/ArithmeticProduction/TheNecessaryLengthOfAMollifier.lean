import GaloisForLFunctions.ArithmeticProduction.TheGaussianAveragingOfTheWindow
import GaloisForLFunctions.RHTower.SmoothDiagonalContour

/-!
# The necessary length of a mollifier

**Theorem** (`necessary_length`).  For every `θ > 0` and all large `T`, every real Dirichlet polynomial `M` of length `N ≤ T^θ` with `b₁ = 1`,
`|b_n| ≤ 1` satisfies

  `∫_T^{2T} |ζ(½+it) M(½+it)|² dt ≥ (1 + 1/(8 + 6θ)) T`.

So a mollified second moment tending to `1` forces the length exponent `θ → ∞`.  The proof has three ingredients:

* the floors `∫|ζM(½+a+it)|² ≳ T` (first moment) and `∫|ζM(½−a+it)|² ≳ e^{2a log T} T` (Littlewood and the count of zeros);
* the second-moment profile `x ↦ ∫|F(½+x+it)|²` is a Laplace transform of a measure on `u ∈ [0, log(T²N^{3/2})]`;
* the interpolation `e^{La}Φ(a) + e^{−La}Φ(−a) ≤ 2cosh(aL)Φ(0)` at `aL ≈ log 2`, which forbids the kink between the two floors.

The theorem uses no bound on pair correlation, and the only fact about the zeros is their number.
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
        (s := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (by simp; norm_num)
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
    have h4 : (x + w - 9 * ε) * T = (x - 4 * ε + (w - 3 * ε)) * T - 2 * ε * T - 5 * (ε * T) := by ring
    have h5 : 0 ≤ ε * T := by positivity
    linarith
  have hp2 : 0 ≤ p * T := by positivity
  linarith

end GaloisForLFunctions.ArithmeticProduction
