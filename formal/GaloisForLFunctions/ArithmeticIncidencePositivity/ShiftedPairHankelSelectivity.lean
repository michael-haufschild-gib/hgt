import GaloisForLFunctions.ArithmeticIncidencePositivity.ShiftedPairOddWindowSelectivity

/-!
# The infinite-shift limit of `ζ(s − a) ζ(s + a)`: a Hankel form, and selectivity below `21/200`

For a profile `H` supported in `[y₀, r]`, `0 < y₀`, put `G_a(y) = e^{−ay} H(y)` and let
`F_a = G_a − G_a(−·)` be its odd extension. The zero form of the shifted pair on `F_a` decomposes, by
the exact comparison `shiftedPairZeroForm_eq`, into `2Ẑ(F_a)`, a same-side term built on the
autocorrelation of `G_a`, and a crossing term built on the self-convolution
`(G_a ∗ G_a)(t) = e^{−at} (H ∗ H)(t)` (`selfConv_exp_mul`). Since `(cosh(at) − 1) e^{−at} = (1 − e^{−at})²/2`,
the crossing term converges to

    2 ∫ f(t) (H ∗ H)(t) dt = 2 ∫∫ f(y + z) H(y) H(z) dy dz,       f(t) = ω(t) − 2 cosh(t/2),

the Hankel form of the screw weight `f`, while the other two terms are `O(a² e^{−2a y₀})`
(`exists_fullZeroForm_le_lipschitz`, `abs_integral_correction_reweightedHankel_le`). So the shifted pair is selective on a window
as soon as the Hankel form of `f` on functions supported in `(0, r]` is indefinite.

On `(0, t_*)` the weight `f` is positive and decreasing, `f ≈ 1/(2t)` near `0`, `f → 0` at the plastic
threshold: it is log-convex near `0` and log-concave near `t_*`. Three separations `0.12, 0.16, 0.20`
already violate log-convexity (`f(0.16)² > f(0.12) f(0.20)`), and the two-bump profile
`H = φ_{0.06} − (93/50) φ_{0.10}` has negative Hankel form (`integral_weighted_hankelProfile_le`). Hence
(`exists_odd_shiftedPairZeroForm_neg_below_markovWindow`): for every large `a` some odd `F ∈ C²_c`
supported in `[−13/125, 13/125]` has negative `ζ(s − a) ζ(s + a)` zero form, although every odd (indeed
every) test supported in `[−21/200, 21/200]` has `Ẑ(F) ≥ (1/30)∫F²` for `ζ`. Window positivity is selective
against the shifted pair well below the plastic threshold, already at the Markov window.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyCoshCrossover
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### An upper bound for the full zero form on a window -/

/-- **The full zero form is controlled by the Lipschitz constant and the mass.** For every window
`[−r, r]`, `2r < log 2`, there is `C` with `Ẑ(F) ≤ K² + C ∫F²` for every `K`-Lipschitz `F ∈ C²_c`
supported in the window. -/
theorem exists_fullZeroForm_le_lipschitz {r : ℝ} (hr0 : 0 ≤ r) (hrlog : 2 * r < Real.log 2) :
    ∃ C : ℝ, ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, r < |x| → F x = 0) →
      ∀ K : ℝ, (∀ a b, |F a - F b| ≤ K * |a - b|) → fullZeroForm F ≤ K ^ 2 + C * ∫ x, F x ^ 2 := by
  set R := comparisonRadius r with hRdef
  have hrR : r < R := by rw [hRdef, comparisonRadius]; linarith
  have hlog : 2 * R < Real.log 2 := by rw [hRdef, comparisonRadius]; linarith
  have hR0 : 0 ≤ R := by linarith
  have hR1 : R ≤ 1 / 2 := by have := Real.log_two_lt_d9; linarith
  set δ := R - r with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set P := plateauGauge R δ with hPdef
  have hPd : ContDiff ℝ 2 P := contDiff_plateauGauge R δ
  have hPcs : HasCompactSupport P := hasCompactSupport_plateauGauge hδ
  have hP0 : ∀ y, 0 ≤ P y := plateauGauge_nonneg R δ
  have hP1 : ∀ y, P y ≤ 1 := plateauGauge_le_one R δ
  have hPB : ∀ y, R ≤ |y| → P y = 0 := fun y hy => plateauGauge_eq_zero hδ hy
  obtain ⟨KP, -, hKP⟩ := exists_lipschitz_bound_of_compactSupport (hPd.of_le (by norm_num)) hPcs
  have hdec8 : ∀ y, |P y| ≤ Real.exp (8 * |R|) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hP0 y), ← Real.exp_add]
      exact (hP1 y).trans (Real.one_le_exp (by nlinarith [le_abs_self R]))
    · rw [hPB y (not_lt.mp hy), abs_zero]
      positivity
  have hWc : Continuous fun x => -poleFreeWeilOperator P x :=
    (continuous_poleFreeWeilOperator hPd.continuous (fun u v => hKP v u) hdec8).neg
  have hGc : Continuous fun x => ∫ y, P y * Real.cosh ((x - y) / 2) := by
    have e := funext (integral_gauge_cosh_eq hPd.continuous hPcs)
    rw [e]
    fun_prop
  set V : ℝ → ℝ := fun x => P x * -poleFreeWeilOperator P x +
    2 * ∫ y, P y * Real.cosh ((x - y) / 2) with hVdef
  have hVc : Continuous V := (hPd.continuous.mul hWc).add (continuous_const.mul hGc)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hVc.continuousOn
  refine ⟨C, fun F hF hFc hsupp K hK => ?_⟩
  have hFP : ∀ x, F x ≠ 0 → P x = 1 := fun x hx => plateauGauge_eq_one hδ (by
    rw [hδdef]
    by_contra h
    exact hx (hsupp x (by linarith)))
  have hW := fullZeroForm_eq_window hF hFc hPd hPcs hP1 hP0 hPB hlog hFP
  -- the archimedean jump term
  have hI0 : ∀ t, 0 ≤ gaugeJumpProfile P F t := fun t => integral_nonneg fun x => by
    unfold signedShiftJump
    exact mul_nonneg (mul_nonneg (hP0 _) (hP0 _)) (sq_nonneg _)
  have hωI := integrableOn_archLevy_mul_gaugeJumpProfile hP1 hP0 hPB hR0 hR1 hF.continuous
    hPd.continuous hPcs hK
  have hbound : IntegrableOn (fun t => (Ioc 0 (2 * R)).indicator (fun t => 3 * R * K ^ 2 * t) t)
      (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioc).mpr
      ((continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self)).integrableOn
  have hjump : (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) ≤
      3 * R * K ^ 2 * (2 * R) ^ 2 / 2 := by
    have h1 : (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) ≤
        ∫ t in Ioi (0 : ℝ), (Ioc 0 (2 * R)).indicator (fun t => 3 * R * K ^ 2 * t) t := by
      refine setIntegral_mono_on hωI hbound measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := ht
      by_cases h2R : t ≤ 2 * R
      · rw [Set.indicator_of_mem (show t ∈ Ioc 0 (2 * R) from ⟨ht0, h2R⟩)]
        have hω := archLevyDensity_le_of_le_one ht0 (by linarith)
        have hI := gaugeJumpProfile_le hP1 hP0 hPB hR0 hF.continuous hPd.continuous hPcs hK ht0.le
        calc archLevyDensity t * gaugeJumpProfile P F t ≤ 3 / 2 / t * (2 * R * (K ^ 2 * t ^ 2)) :=
              mul_le_mul hω hI (hI0 t) (by positivity)
          _ = 3 * R * K ^ 2 * t := by field_simp
      · rw [Set.indicator_of_notMem (fun h => h2R h.2),
          gaugeJumpProfile_eq_zero_of_ge hPB (not_le.mp h2R).le, mul_zero]
    have h2 : (∫ t in Ioi (0 : ℝ), (Ioc 0 (2 * R)).indicator (fun t => 3 * R * K ^ 2 * t) t) =
        3 * R * K ^ 2 * (2 * R) ^ 2 / 2 := by
      rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Ioc_subset_Ioi_self,
        ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
        integral_id]
      ring
    linarith
  have hR3 : 3 * R * K ^ 2 * (2 * R) ^ 2 / 2 ≤ K ^ 2 := by
    have h1 : R ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hR0 hR1 3
    have h2 : 0 ≤ K ^ 2 := sq_nonneg K
    nlinarith
  -- the cosh jump term is nonpositive
  have hcosh : 0 ≤ ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile P F t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => mul_nonneg (Real.cosh_pos _).le (hI0 t)
  -- the potential term
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hpot1 : Integrable fun x => F x ^ 2 * P x * -poleFreeWeilOperator P x :=
    (((hF.continuous.pow 2).mul hPd.continuous).mul hWc).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  have hpot2 : Integrable fun x => F x ^ 2 * ∫ y, P y * Real.cosh ((x - y) / 2) :=
    ((hF.continuous.pow 2).mul hGc).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc).mul_right
  have hpot : (∫ x, F x ^ 2 * P x * -poleFreeWeilOperator P x) +
      2 * (∫ x, F x ^ 2 * ∫ y, P y * Real.cosh ((x - y) / 2)) ≤ C * ∫ x, F x ^ 2 := by
    rw [← integral_const_mul, ← integral_add hpot1 (hpot2.const_mul 2), ← integral_const_mul]
    refine integral_mono (hpot1.add (hpot2.const_mul 2)) (hF2.const_mul C) fun x => ?_
    by_cases h : F x = 0
    · simp [h]
    · have hx : x ∈ Icc (-R) R := by
        have : |x| ≤ r := by by_contra h'; exact h (hsupp x (not_le.mp h'))
        exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
      have hb := hC x hx
      rw [Real.norm_eq_abs] at hb
      have hVx : V x ≤ C := (le_abs_self _).trans hb
      simp only [hVdef] at hVx
      have hF0 := sq_nonneg (F x)
      nlinarith [mul_le_mul_of_nonneg_left hVx hF0]
  rw [hW]
  linarith

/-! ### Exponential reweighting -/

/-- `|e^{−ap} − e^{−aq}| ≤ a e^{−a y₀} |p − q|` for `p, q ≥ y₀`, `a ≥ 0`. -/
theorem abs_exp_neg_sub_le {a y₀ p q : ℝ} (ha : 0 ≤ a) (hp : y₀ ≤ p) (hq : y₀ ≤ q) :
    |Real.exp (-a * p) - Real.exp (-a * q)| ≤ a * Real.exp (-a * y₀) * |p - q| := by
  wlog hpq : p ≤ q generalizing p q
  · rw [abs_sub_comm, abs_sub_comm p q]; exact this hq hp (le_of_not_ge hpq)
  have h1 : Real.exp (-a * q) ≤ Real.exp (-a * p) := Real.exp_le_exp.mpr (by nlinarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h2 : Real.exp (-a * q) = Real.exp (-a * p) * Real.exp (-(a * (q - p))) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 1 - Real.exp (-(a * (q - p))) ≤ a * (q - p) := by
    have := Real.add_one_le_exp (-(a * (q - p))); linarith
  have h4 : Real.exp (-a * p) ≤ Real.exp (-a * y₀) := Real.exp_le_exp.mpr (by nlinarith)
  have h5 : 0 ≤ a * (q - p) := mul_nonneg ha (by linarith)
  rw [h2]
  calc Real.exp (-a * p) - Real.exp (-a * p) * Real.exp (-(a * (q - p))) =
      Real.exp (-a * p) * (1 - Real.exp (-(a * (q - p)))) := by ring
    _ ≤ Real.exp (-a * y₀) * (a * (q - p)) :=
        mul_le_mul h4 h3 (by linarith [Real.exp_le_one_iff.mpr (show -(a * (q - p)) ≤ 0 by linarith)])
          (Real.exp_pos _).le
    _ = a * Real.exp (-a * y₀) * -(p - q) := by ring

/-- **Lipschitz constant of an exponentially reweighted profile.** If `H` vanishes below `y₀`, is
`L`-Lipschitz and bounded by `M`, then `y ↦ e^{−ay} H(y)` is `e^{−a y₀}(L + aM)`-Lipschitz. -/
theorem lipschitz_exp_mul {H : ℝ → ℝ} {y₀ a L M : ℝ} (ha : 0 ≤ a) (hH0 : ∀ y, y < y₀ → H y = 0)
    (hL : ∀ u v, |H u - H v| ≤ L * |u - v|) (hM : ∀ y, |H y| ≤ M) (u v : ℝ) :
    |Real.exp (-a * u) * H u - Real.exp (-a * v) * H v| ≤
      Real.exp (-a * y₀) * (L + a * M) * |u - v| := by
  set g : ℝ → ℝ := fun y => Real.exp (-a * max y y₀) with hg
  have hgH : ∀ y, Real.exp (-a * y) * H y = g y * H y := fun y => by
    by_cases hy : y < y₀
    · rw [hH0 y hy, mul_zero, mul_zero]
    · simp only [hg, max_eq_left (not_lt.mp hy)]
  have hg1 : ∀ y, |g y| ≤ Real.exp (-a * y₀) := fun y => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith [le_max_right y y₀])
  have hg2 : |g u - g v| ≤ a * Real.exp (-a * y₀) * |u - v| := by
    have h := abs_exp_neg_sub_le ha (le_max_right u y₀) (le_max_right v y₀)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg ha (Real.exp_pos _).le))
    exact abs_max_sub_max_le_abs u v y₀
  have hL0 : 0 ≤ L := by
    by_contra hneg
    have h := hL 1 0
    have : L * |(1 : ℝ) - 0| < 0 := by norm_num; linarith
    linarith [abs_nonneg (H 1 - H 0)]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [hgH, hgH]
  calc |g u * H u - g v * H v| = |g u * (H u - H v) + H v * (g u - g v)| := by ring_nf
    _ ≤ |g u * (H u - H v)| + |H v * (g u - g v)| := abs_add_le _ _
    _ = |g u| * |H u - H v| + |H v| * |g u - g v| := by rw [abs_mul, abs_mul]
    _ ≤ Real.exp (-a * y₀) * (L * |u - v|) + M * (a * Real.exp (-a * y₀) * |u - v|) :=
        add_le_add (mul_le_mul (hg1 u) (hL u v) (abs_nonneg _) (Real.exp_pos _).le)
          (mul_le_mul (hM v) hg2 (abs_nonneg _) hM0)
    _ = Real.exp (-a * y₀) * (L + a * M) * |u - v| := by ring

/-! ### The odd extension of a half-line profile -/

/-- The self-convolution `(G ∗ G)(t) = ∫ G(s) G(t − s) ds`. -/
def selfConv (G : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s, G s * G (t - s)

/-- For `G` supported in `(0, ∞)` and `t > 0`, the autocorrelation of the odd extension
`G − G(−·)` is `2 A_G(t) − (G ∗ G)(t)`. -/
theorem autoCorr_sub_reflect {G : ℝ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G)
    (hG0 : ∀ x, x ≤ 0 → G x = 0) {t : ℝ} (ht : 0 < t) :
    autoCorr (fun x => G x - G (-x)) t = 2 * autoCorr G t - selfConv G t := by
  have hint : ∀ g h : ℝ → ℝ, Continuous g → Continuous h → HasCompactSupport g →
      Integrable fun x => g x * h x := fun g h hg hh hgc =>
    (hg.mul hh).integrable_of_hasCompactSupport hgc.mul_right
  have hc1 : Continuous fun x => G (x + t) := hG.comp (continuous_id.add continuous_const)
  have hc2 : Continuous fun x => G (-x - t) := hG.comp (continuous_neg.sub continuous_const)
  have hc3 : Continuous fun x => G (-x) := hG.comp continuous_neg
  have hGc' := hGc.comp_homeomorph (Homeomorph.neg ℝ)
  have i1 := hint (fun x => G x) (fun x => G (x + t)) hG hc1 hGc
  have i2 := hint (fun x => G x) (fun x => G (-x - t)) hG hc2 hGc
  have i3 := hint (fun x => G (-x)) (fun x => G (x + t)) hc3 hc1 hGc'
  have i4 := hint (fun x => G (-x)) (fun x => G (-x - t)) hc3 hc2 hGc'
  have h0 : ∀ x, G x * G (-x - t) = 0 := fun x => by
    by_cases hx : x ≤ 0
    · rw [hG0 x hx, zero_mul]
    · rw [hG0 (-x - t) (by linarith), mul_zero]
  have h4 : (∫ x, G (-x) * G (-x - t)) = autoCorr G t := by
    have e1 : (∫ x, G (-x) * G (-x - t)) = ∫ x, G x * G (x - t) :=
      integral_neg_eq_self (fun y => G y * G (y - t)) volume
    rw [e1, ← integral_add_right_eq_self (fun x => G x * G (x - t)) t]
    unfold autoCorr
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [add_sub_cancel_right]
    ring
  have h3 : (∫ x, G (-x) * G (x + t)) = selfConv G t := by
    have e1 : (∫ x, G (-x) * G (x + t)) = ∫ x, G x * G (-x + t) := by
      rw [← integral_neg_eq_self (fun y => G y * G (-y + t)) volume]
      simp only [neg_neg]
    rw [e1]
    unfold selfConv
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [show -x + t = t - x by ring]
  unfold autoCorr
  have e : (fun x => (G x - G (-x)) * (G (x + t) - G (-(x + t)))) =
      fun x => G x * G (x + t) - G x * G (-x - t) - G (-x) * G (x + t) + G (-x) * G (-x - t) := by
    funext x; rw [show -(x + t) = -x - t by ring]; ring
  have i12 : Integrable fun x => G x * G (x + t) - G x * G (-x - t) := i1.sub i2
  have i123 : Integrable fun x => G x * G (x + t) - G x * G (-x - t) - G (-x) * G (x + t) :=
    i12.sub i3
  rw [e, integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2, h4, h3]
  simp only [h0, integral_zero]
  unfold autoCorr
  ring

/-- `(e^{−a·}H ∗ e^{−a·}H)(t) = e^{−at} (H ∗ H)(t)`. -/
theorem selfConv_exp_mul (H : ℝ → ℝ) (a t : ℝ) :
    selfConv (fun y => Real.exp (-a * y) * H y) t = Real.exp (-a * t) * selfConv H t := by
  unfold selfConv
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only
  have : Real.exp (-a * s) * Real.exp (-a * (t - s)) = Real.exp (-a * t) := by
    rw [← Real.exp_add]; ring_nf
  calc Real.exp (-a * s) * H s * (Real.exp (-a * (t - s)) * H (t - s)) =
      (Real.exp (-a * s) * Real.exp (-a * (t - s))) * (H s * H (t - s)) := by ring
    _ = _ := by rw [this]

/-- `|A_{e^{−a·}H}(t)| ≤ e^{−a(2y₀ + t)} ∫ |H(x)| |H(x + t)| dx` when `H` vanishes below `y₀`, `a ≥ 0`. -/
theorem abs_autoCorr_exp_mul_le {H : ℝ → ℝ} {y₀ a : ℝ} (hH : Continuous H)
    (hHc : HasCompactSupport H) (ha : 0 ≤ a) (hH0 : ∀ y, y < y₀ → H y = 0) (t : ℝ) :
    |autoCorr (fun y => Real.exp (-a * y) * H y) t| ≤
      Real.exp (-a * (2 * y₀ + t)) * ∫ x, |H x| * |H (x + t)| := by
  unfold autoCorr
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x => abs_nonneg _) ?_ (Eventually.of_forall fun x => ?_))
  · exact (continuous_const.mul ((continuous_abs.comp hH).mul
      (continuous_abs.comp (hH.comp (continuous_id.add continuous_const))))).integrable_of_hasCompactSupport
      ((hHc.comp_left (by simp : |(0 : ℝ)| = 0)).mul_right.mul_left)
  · simp only
    by_cases hx : x < y₀
    · rw [hH0 x hx]; simp
    · have h1 : Real.exp (-a * x) * Real.exp (-a * (x + t)) ≤ Real.exp (-a * (2 * y₀ + t)) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [not_lt.mp hx])
      calc |Real.exp (-a * x) * H x * (Real.exp (-a * (x + t)) * H (x + t))| =
          (Real.exp (-a * x) * Real.exp (-a * (x + t))) * (|H x| * |H (x + t)|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _)]; ring
        _ ≤ Real.exp (-a * (2 * y₀ + t)) * (|H x| * |H (x + t)|) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)

/-! ### The screw weight -/

/-- The screw weight `f(t) = ω(t) − 2 cosh(t/2)`, positive and decreasing on `(0, t_*)`. -/
def screwWeight (t : ℝ) : ℝ := archLevyDensity t - 2 * Real.cosh (t / 2)

theorem screwWeight_antitone {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : screwWeight t ≤ screwWeight s := by
  unfold screwWeight
  linarith [screwWeight_mono hs hst]

/-- `2 + u² ≤ 2 cosh u`. -/
theorem two_add_sq_le_two_cosh (u : ℝ) : 2 + u ^ 2 ≤ 2 * Real.cosh u := by
  rcases le_or_gt 0 u with hu | hu
  · linarith [sq_div_two_le_cosh_sub_one hu]
  · have := sq_div_two_le_cosh_sub_one (show 0 ≤ -u by linarith)
    rw [Real.cosh_neg, neg_sq] at this
    linarith

/-- **Three values of the screw weight.** `f(0.1198) ≤ 2.43`, `f(0.1602) ≥ 1.35`, `f(0.1998) ≤ 0.74`. -/
theorem screwWeight_values :
    screwWeight (1198 / 10000) ≤ 243 / 100 ∧ 135 / 100 ≤ screwWeight (1602 / 10000) ∧
      screwWeight (1998 / 10000) ≤ 74 / 100 := by
  have low : ∀ x : ℝ, 0 ≤ x → ∑ i ∈ Finset.range 5, x ^ i / (i.factorial : ℝ) ≤ Real.exp x :=
    fun x hx => Real.sum_le_exp_of_nonneg hx 5
  have up : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 100 := fun x hx hx1 => by
    have := exp_le_taylor_five (x := x) (by rw [abs_of_nonneg hx]; exact hx1)
    rwa [abs_of_nonneg hx] at this
  have hω : ∀ t : ℝ, archLevyDensity t = (Real.exp (t / 2))⁻¹ / (1 - (Real.exp (2 * t))⁻¹) :=
    fun t => by
      unfold archLevyDensity
      rw [← Real.exp_neg, ← Real.exp_neg]; ring_nf
  have hc : ∀ t : ℝ, 2 * Real.cosh (t / 2) = Real.exp (t / 2) + (Real.exp (t / 2))⁻¹ := fun t => by
    rw [Real.cosh_eq, Real.exp_neg]; ring
  refine ⟨?_, ?_, ?_⟩
  · -- `t = 0.1198`
    have h1 := low (1198 / 20000) (by norm_num)
    have h2 := low (1198 / 5000) (by norm_num)
    have h3 := two_add_sq_le_two_cosh (1198 / 20000)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2
    norm_num at h1 h2 h3
    unfold screwWeight
    rw [hω, show (1198 / 10000 : ℝ) / 2 = 1198 / 20000 by norm_num,
      show (2 : ℝ) * (1198 / 10000) = 1198 / 5000 by norm_num]
    have e1 := Real.exp_pos (1198 / 20000)
    have e2 := Real.exp_pos (1198 / 5000)
    have hi1 : (Real.exp (1198 / 20000))⁻¹ ≤ 1 / 1.0617301 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hi2 : (Real.exp (1198 / 5000))⁻¹ ≤ 1 / 1.2707 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hden : 0.213 ≤ 1 - (Real.exp (1198 / 5000))⁻¹ := by norm_num at hi2 ⊢; linarith
    have hnum : 0 ≤ (Real.exp (1198 / 20000))⁻¹ := (inv_pos.mpr e1).le
    have hq : (Real.exp (1198 / 20000))⁻¹ / (1 - (Real.exp (1198 / 5000))⁻¹) ≤
        (1 / 1.0617301) / 0.213 := div_le_div₀ (by norm_num) hi1 (by norm_num) hden
    norm_num at hq
    linarith
  · -- `t = 0.1602`
    have h1 := up (801 / 10000) (by norm_num) (by norm_num)
    have h2 := up (801 / 2500) (by norm_num) (by norm_num)
    have h1' := low (801 / 10000) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1'
    norm_num at h1 h2 h1'
    unfold screwWeight
    rw [hω, hc, show (1602 / 10000 : ℝ) / 2 = 801 / 10000 by norm_num,
      show (2 : ℝ) * (1602 / 10000) = 801 / 2500 by norm_num]
    have e1 := Real.exp_pos (801 / 10000)
    have e2 := Real.exp_pos (801 / 2500)
    have hgt : 1 < Real.exp (801 / 2500) := by
      have := Real.add_one_le_exp (801 / 2500 : ℝ); linarith
    have hi1 : 1 / 1.0834 ≤ (Real.exp (801 / 10000))⁻¹ := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le e1 (by linarith)
    have hi2 : 1 / 1.3777 ≤ (Real.exp (801 / 2500))⁻¹ := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le e2 (by linarith)
    have hi3 : (Real.exp (801 / 10000))⁻¹ ≤ 1 / 1.0833 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hden0 : 0 < 1 - (Real.exp (801 / 2500))⁻¹ := by
      have : (Real.exp (801 / 2500))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
      linarith
    have hden : 1 - (Real.exp (801 / 2500))⁻¹ ≤ 0.2742 := by norm_num at hi2 ⊢; linarith
    have hq : (1 / 1.0834) / 0.2742 ≤
        (Real.exp (801 / 10000))⁻¹ / (1 - (Real.exp (801 / 2500))⁻¹) :=
      div_le_div₀ (inv_pos.mpr e1).le hi1 hden0 hden
    norm_num at hq hi3
    linarith
  · -- `t = 0.1998`
    have h1 := low (999 / 10000) (by norm_num)
    have h2 := low (999 / 2500) (by norm_num)
    have h3 := two_add_sq_le_two_cosh (999 / 10000)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2
    norm_num at h1 h2 h3
    unfold screwWeight
    rw [hω, show (1998 / 10000 : ℝ) / 2 = 999 / 10000 by norm_num,
      show (2 : ℝ) * (1998 / 10000) = 999 / 2500 by norm_num]
    have e1 := Real.exp_pos (999 / 10000)
    have e2 := Real.exp_pos (999 / 2500)
    have hi1 : (Real.exp (999 / 10000))⁻¹ ≤ 1 / 1.10505 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hi2 : (Real.exp (999 / 2500))⁻¹ ≤ 1 / 1.4911 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hden : 0.3293 ≤ 1 - (Real.exp (999 / 2500))⁻¹ := by norm_num at hi2 ⊢; linarith
    have hq : (Real.exp (999 / 10000))⁻¹ / (1 - (Real.exp (999 / 2500))⁻¹) ≤
        (1 / 1.10505) / 0.3293 := div_le_div₀ (by norm_num) hi1 (by norm_num) hden
    norm_num at hq
    linarith

/-! ### Convolutions of bumps -/

/-- The convolution `(φ ∗ ψ)(t) = ∫ φ(s) ψ(t − s) ds`. -/
def bumpConv (φ ψ : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s, φ s * ψ (t - s)

section BumpConv

variable {y y' w : ℝ} (hw : 0 < w)

theorem bumpConv_nonneg (t : ℝ) : 0 ≤ bumpConv (bumpAt y w) (bumpAt y' w) t :=
  integral_nonneg fun _ => mul_nonneg (bumpAt_nonneg _ _ _) (bumpAt_nonneg _ _ _)

include hw in
theorem bumpConv_eq_zero {t : ℝ} (ht : 2 * w ≤ |t - (y + y')|) :
    bumpConv (bumpAt y w) (bumpAt y' w) t = 0 := by
  unfold bumpConv
  refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
  simp only [Pi.zero_apply]
  by_cases h1 : bumpAt y w s = 0
  · rw [h1, zero_mul]
  · have a1 := bumpAt_ne_zero_imp hw h1
    rw [bumpAt_eq_zero hw (x := t - s) (by
      have h2 := abs_sub_abs_le_abs_sub (t - (y + y')) (s - y)
      rw [show t - (y + y') - (s - y) = t - s - y' by ring] at h2
      linarith), mul_zero]

include hw in
theorem integrable_bumpConv_kernel :
    Integrable (fun p : ℝ × ℝ => bumpAt y w p.2 * bumpAt y' w (p.1 - p.2))
      ((volume : Measure ℝ).prod volume) := by
  refine integrable_prod_of_box (B := |y| + |y'| + 2 * w + 1) (by
    have h1 := (contDiff_bumpAt y w).continuous
    have h2 := (contDiff_bumpAt y' w).continuous
    fun_prop) fun p hp => ?_
  have a1 := bumpAt_ne_zero_imp hw (left_ne_zero_of_mul hp)
  have a2 := bumpAt_ne_zero_imp hw (right_ne_zero_of_mul hp)
  rw [abs_lt] at a1 a2
  constructor <;> rw [abs_le] <;> constructor <;>
    linarith [neg_abs_le y, le_abs_self y, neg_abs_le y', le_abs_self y']

include hw in
theorem integrable_bumpConv : Integrable (bumpConv (bumpAt y w) (bumpAt y' w)) :=
  (integrable_bumpConv_kernel hw).integral_prod_left

theorem integral_bumpAt_eq (y w : ℝ) : (∫ x, bumpAt y w x) = ∫ x, bumpAt 0 w x := by
  unfold bumpAt
  simp only [sub_zero]
  exact integral_sub_right_eq_self (fun x => plateauGauge w (w / 2) x) y

include hw in
/-- `∫ (φ_y ∗ φ_{y'}) = m²`, `m = ∫ φ_0`. -/
theorem integral_bumpConv : (∫ t, bumpConv (bumpAt y w) (bumpAt y' w) t) =
    (∫ x, bumpAt 0 w x) ^ 2 := by
  have hswap := integral_integral_swap (f := fun t s => bumpAt y w s * bumpAt y' w (t - s))
    (integrable_bumpConv_kernel hw)
  unfold bumpConv
  rw [hswap]
  have hin : ∀ s, (∫ t, bumpAt y w s * bumpAt y' w (t - s)) = bumpAt y w s * ∫ t, bumpAt y' w t :=
    fun s => by rw [integral_const_mul, integral_sub_right_eq_self (fun t => bumpAt y' w t) s]
  simp_rw [hin]
  rw [integral_mul_const, integral_bumpAt_eq y w, integral_bumpAt_eq y' w]
  ring

include hw in
/-- If `g ≤ U` on the support `|t − (y + y')| < 2w` of `φ_y ∗ φ_{y'}` and `g` is measurable and bounded
there, then `∫ g (φ_y ∗ φ_{y'}) ≤ U m²`; similarly from below. -/
theorem integral_mul_bumpConv_bounds {g : ℝ → ℝ} (hg : Measurable g) {L U : ℝ}
    (hgL : ∀ t, |t - (y + y')| < 2 * w → L ≤ g t) (hgU : ∀ t, |t - (y + y')| < 2 * w → g t ≤ U) :
    Integrable (fun t => g t * bumpConv (bumpAt y w) (bumpAt y' w) t) ∧
      L * (∫ x, bumpAt 0 w x) ^ 2 ≤ ∫ t, g t * bumpConv (bumpAt y w) (bumpAt y' w) t ∧
      (∫ t, g t * bumpConv (bumpAt y w) (bumpAt y' w) t) ≤ U * (∫ x, bumpAt 0 w x) ^ 2 := by
  have hI := integrable_bumpConv hw (y := y) (y' := y')
  have hpt : ∀ t, L * bumpConv (bumpAt y w) (bumpAt y' w) t ≤
      g t * bumpConv (bumpAt y w) (bumpAt y' w) t ∧
      g t * bumpConv (bumpAt y w) (bumpAt y' w) t ≤ U * bumpConv (bumpAt y w) (bumpAt y' w) t :=
    fun t => by
      by_cases ht : |t - (y + y')| < 2 * w
      · exact ⟨mul_le_mul_of_nonneg_right (hgL t ht) (bumpConv_nonneg t),
          mul_le_mul_of_nonneg_right (hgU t ht) (bumpConv_nonneg t)⟩
      · rw [bumpConv_eq_zero hw (not_lt.mp ht)]; simp
  have hmeas : AEStronglyMeasurable (fun t => g t * bumpConv (bumpAt y w) (bumpAt y' w) t) volume :=
    hg.aestronglyMeasurable.mul hI.aestronglyMeasurable
  have hint : Integrable (fun t => g t * bumpConv (bumpAt y w) (bumpAt y' w) t) := by
    refine ((hI.const_mul |L|).add (hI.const_mul |U|)).mono' hmeas (Eventually.of_forall fun t => ?_)
    obtain ⟨h1, h2⟩ := hpt t
    have hb := bumpConv_nonneg (y := y) (y' := y') (w := w) t
    have k1 := mul_le_mul_of_nonneg_right (neg_abs_le L) hb
    have k2 := mul_le_mul_of_nonneg_right (le_abs_self U) hb
    have k3 := mul_nonneg (abs_nonneg L) hb
    have k4 := mul_nonneg (abs_nonneg U) hb
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  refine ⟨hint, ?_, ?_⟩
  · rw [← integral_bumpConv hw, ← integral_const_mul]
    exact integral_mono (hI.const_mul L) hint fun t => (hpt t).1
  · rw [← integral_bumpConv hw, ← integral_const_mul]
    exact integral_mono hint (hI.const_mul U) fun t => (hpt t).2

end BumpConv

/-! ### The two-bump Hankel profile -/

/-- The plateau mass `w ≤ ∫ φ_y`. -/
theorem le_integral_bumpAt {y w : ℝ} (hw : 0 < w) : w ≤ ∫ x, bumpAt y w x := by
  have hint : Integrable (bumpAt y w) :=
    (contDiff_bumpAt y w).continuous.integrable_of_hasCompactSupport (hasCompactSupport_bumpAt hw)
  have h1 : (∫ x in Icc (y - w / 2) (y + w / 2), (1 : ℝ)) ≤
      ∫ x in Icc (y - w / 2) (y + w / 2), bumpAt y w x :=
    setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn measurableSet_Icc
      fun x hx => by
        rw [bumpAt_eq_one hw (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])]
  have h2 : (∫ x in Icc (y - w / 2) (y + w / 2), bumpAt y w x) ≤ ∫ x, bumpAt y w x :=
    setIntegral_le_integral hint (Eventually.of_forall fun x => bumpAt_nonneg _ _ _)
  rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc, max_eq_left (by linarith)] at h1
  linarith

/-- The Hankel test profile `H = φ_{0.06} − (93/50) φ_{0.10}`, bumps of half-width `10⁻⁴`. -/
def hankelProfile (y : ℝ) : ℝ :=
  bumpAt (3 / 50) (1 / 10000) y - 93 / 50 * bumpAt (1 / 10) (1 / 10000) y

theorem contDiff_hankelProfile : ContDiff ℝ 2 hankelProfile :=
  (contDiff_bumpAt _ _).sub (contDiff_const.mul (contDiff_bumpAt _ _))

theorem hasCompactSupport_hankelProfile : HasCompactSupport hankelProfile :=
  (hasCompactSupport_bumpAt (by norm_num)).sub
    ((hasCompactSupport_bumpAt (by norm_num)).mul_left)

theorem hankelProfile_eq_zero_of_lt {y : ℝ} (hy : y < 59 / 1000) : hankelProfile y = 0 := by
  unfold hankelProfile
  rw [bumpAt_eq_zero (by norm_num) (by rw [abs_of_neg (by linarith)]; linarith),
    bumpAt_eq_zero (by norm_num) (by rw [abs_of_neg (by linarith)]; linarith)]
  ring

theorem hankelProfile_eq_zero_of_gt {y : ℝ} (hy : 13 / 125 < y) : hankelProfile y = 0 := by
  unfold hankelProfile
  rw [bumpAt_eq_zero (by norm_num) (by rw [abs_of_pos (by linarith)]; linarith),
    bumpAt_eq_zero (by norm_num) (by rw [abs_of_pos (by linarith)]; linarith)]
  ring

theorem abs_hankelProfile_le (y : ℝ) : |hankelProfile y| ≤ 3 := by
  unfold hankelProfile
  have h1 := bumpAt_nonneg (3 / 50) (1 / 10000) y
  have h2 := plateauGauge_le_one (1 / 10000) (1 / 10000 / 2) (y - 3 / 50)
  have h3 := bumpAt_nonneg (1 / 10) (1 / 10000) y
  have h4 := plateauGauge_le_one (1 / 10000) (1 / 10000 / 2) (y - 1 / 10)
  unfold bumpAt at *
  rw [abs_le]; constructor <;> nlinarith

/-- The self-convolution of the Hankel profile as a combination of bump convolutions. -/
theorem selfConv_hankelProfile (t : ℝ) :
    selfConv hankelProfile t =
      bumpConv (bumpAt (3 / 50) (1 / 10000)) (bumpAt (3 / 50) (1 / 10000)) t -
        93 / 50 * bumpConv (bumpAt (3 / 50) (1 / 10000)) (bumpAt (1 / 10) (1 / 10000)) t -
        93 / 50 * bumpConv (bumpAt (1 / 10) (1 / 10000)) (bumpAt (3 / 50) (1 / 10000)) t +
        (93 / 50) ^ 2 * bumpConv (bumpAt (1 / 10) (1 / 10000)) (bumpAt (1 / 10) (1 / 10000)) t := by
  set φ := bumpAt (3 / 50) (1 / 10000) with hφ
  set ψ := bumpAt (1 / 10) (1 / 10000) with hψ
  have hφc := (contDiff_bumpAt (3 / 50) (1 / 10000)).continuous
  have hψc := (contDiff_bumpAt (1 / 10) (1 / 10000)).continuous
  have hφs : HasCompactSupport φ := hasCompactSupport_bumpAt (by norm_num)
  have hψs : HasCompactSupport ψ := hasCompactSupport_bumpAt (by norm_num)
  have hint : ∀ g h : ℝ → ℝ, Continuous g → Continuous h → HasCompactSupport g →
      Integrable fun s => g s * h (t - s) := fun g h hg hh hgs =>
    (hg.mul (hh.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hgs.mul_right
  have i1 := hint φ φ hφc hφc hφs
  have i2 := (hint φ ψ hφc hψc hφs).const_mul (93 / 50)
  have i3 := (hint ψ φ hψc hφc hψs).const_mul (93 / 50)
  have i4 := (hint ψ ψ hψc hψc hψs).const_mul ((93 / 50) ^ 2)
  unfold selfConv bumpConv hankelProfile
  rw [← hφ, ← hψ]
  have e : (fun s => (φ s - 93 / 50 * ψ s) * (φ (t - s) - 93 / 50 * ψ (t - s))) =
      fun s => φ s * φ (t - s) - 93 / 50 * (φ s * ψ (t - s)) - 93 / 50 * (ψ s * φ (t - s)) +
        (93 / 50) ^ 2 * (ψ s * ψ (t - s)) := by funext s; ring
  have i12 : Integrable fun s => φ s * φ (t - s) - 93 / 50 * (φ s * ψ (t - s)) := i1.sub i2
  have i123 : Integrable fun s => φ s * φ (t - s) - 93 / 50 * (φ s * ψ (t - s)) -
      93 / 50 * (ψ s * φ (t - s)) := i12.sub i3
  rw [e, integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2, integral_const_mul,
    integral_const_mul, integral_const_mul]

/-! ### The weighted Hankel form of the two-bump profile -/

theorem measurable_screwWeight : Measurable screwWeight := by
  unfold screwWeight
  exact measurable_archLevyDensity.sub (by fun_prop)

/-- The plastic threshold exceeds `0.24`. -/
theorem screwSignThreshold_gt : (24 : ℝ) / 100 < GaloisForLFunctions.RHTower.screwSignThreshold := by
  have hρ1 := plasticRoot_gt
  have hρ0 : 0 < GaloisForLFunctions.RHTower.plasticRoot := by linarith
  unfold GaloisForLFunctions.RHTower.screwSignThreshold
  have h := Real.one_sub_inv_le_log_of_pos hρ0
  have h2 : (GaloisForLFunctions.RHTower.plasticRoot)⁻¹ < 250 / 331 := by
    rw [inv_lt_comm₀ hρ0 (by norm_num)]; norm_num; linarith
  linarith

theorem screwWeight_nonneg {t : ℝ} (ht : 0 < t) (ht' : t ≤ 24 / 100) : 0 ≤ screwWeight t := by
  have := two_mul_cosh_le_archLevyDensity_of_le_threshold ht (by linarith [screwSignThreshold_gt])
  unfold screwWeight; linarith

/-- **The weighted Hankel form of the two-bump profile is negative up to `e^{−0.1598 a}`.**
With `m = ∫ φ_0`, `∫_0^∞ (1 − e^{−at})² f(t) (H ∗ H)(t) dt ≤ m² (Q₀ + 5.4 c e^{−0.1598 a})`,
`Q₀ = 2.43 − 2.7c + 0.74c²`, `c = 93/50`. -/
theorem integral_weighted_hankelProfile_le {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in Ioi (0 : ℝ), (1 - Real.exp (-a * t)) ^ 2 * screwWeight t * selfConv hankelProfile t) ≤
      (∫ x, bumpAt 0 (1 / 10000) x) ^ 2 * ((243 / 100 - 27 / 10 * (93 / 50) + 74 / 100 * (93 / 50) ^ 2) +
        27 / 5 * (93 / 50) * Real.exp (-a * (1598 / 10000))) := by
  obtain ⟨v1, v2, v3⟩ := screwWeight_values
  set wt : ℝ → ℝ := fun t => (1 - Real.exp (-a * t)) ^ 2 * screwWeight t with hwt
  have hwm : Measurable wt := ((by fun_prop : Continuous fun t => (1 - Real.exp (-a * t)) ^ 2).measurable).mul
    measurable_screwWeight
  have hw0 : (0 : ℝ) < 1 / 10000 := by norm_num
  -- bounds of the weight on the four supports
  have hsq1 : ∀ t, 0 ≤ t → (1 - Real.exp (-a * t)) ^ 2 ≤ 1 := fun t ht => by
    have h1 : Real.exp (-a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 := Real.exp_pos (-a * t)
    nlinarith
  have hwle : ∀ t, 0 < t → t ≤ 24 / 100 → wt t ≤ screwWeight t := fun t ht ht' => by
    have := screwWeight_nonneg ht ht'
    simp only [hwt]
    nlinarith [hsq1 t ht.le, sq_nonneg (1 - Real.exp (-a * t))]
  have hwnn : ∀ t, 0 < t → t ≤ 24 / 100 → 0 ≤ wt t := fun t ht ht' =>
    mul_nonneg (sq_nonneg _) (screwWeight_nonneg ht ht')
  have b11 := integral_mul_bumpConv_bounds hw0 (y := 3 / 50) (y' := 3 / 50) hwm (L := 0)
    (U := 243 / 100) (fun t ht => by
      rw [abs_lt] at ht; exact hwnn t (by linarith) (by linarith))
    (fun t ht => by
      rw [abs_lt] at ht
      exact (hwle t (by linarith) (by linarith)).trans
        ((screwWeight_antitone (by norm_num) (by linarith)).trans v1))
  have hL12 : ∀ t, |t - (3 / 50 + 1 / 10)| < 2 * (1 / 10000) →
      (1 - Real.exp (-a * (1598 / 10000))) ^ 2 * (135 / 100) ≤ wt t := fun t ht => by
    rw [abs_lt] at ht
    have hexp : Real.exp (-a * t) ≤ Real.exp (-a * (1598 / 10000)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have he1 : Real.exp (-a * (1598 / 10000)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hb : 0 ≤ 1 - Real.exp (-a * (1598 / 10000)) := by linarith
    have hsq : (1 - Real.exp (-a * (1598 / 10000))) ^ 2 ≤ (1 - Real.exp (-a * t)) ^ 2 :=
      pow_le_pow_left₀ hb (by linarith) 2
    have hf : 135 / 100 ≤ screwWeight t :=
      v2.trans (screwWeight_antitone (by linarith) (by linarith))
    simp only [hwt]
    exact mul_le_mul hsq hf (by norm_num) (sq_nonneg _)
  have hU12 : ∀ t, |t - (3 / 50 + 1 / 10)| < 2 * (1 / 10000) → wt t ≤ 243 / 100 := fun t ht => by
    rw [abs_lt] at ht
    exact (hwle t (by linarith) (by linarith)).trans
      ((screwWeight_antitone (by norm_num) (by linarith)).trans v1)
  have b12 := integral_mul_bumpConv_bounds hw0 (y := 3 / 50) (y' := 1 / 10) hwm hL12 hU12
  have b21 := integral_mul_bumpConv_bounds hw0 (y := 1 / 10) (y' := 3 / 50) hwm
    (fun t ht => hL12 t (by rwa [add_comm (3 / 50 : ℝ)])) (fun t ht => hU12 t (by rwa [add_comm (3 / 50 : ℝ)]))
  have b22 := integral_mul_bumpConv_bounds hw0 (y := 1 / 10) (y' := 1 / 10) hwm (L := 0)
    (U := 74 / 100) (fun t ht => by
      rw [abs_lt] at ht; exact hwnn t (by linarith) (by linarith))
    (fun t ht => by
      rw [abs_lt] at ht
      exact (hwle t (by linarith) (by linarith)).trans
        ((screwWeight_antitone (by norm_num) (by linarith)).trans v3))
  -- the set integral is the full integral
  have hzero : ∀ t, t ∉ Ioi (0 : ℝ) → wt t * selfConv hankelProfile t = 0 := fun t ht => by
    rw [mem_Ioi, not_lt] at ht
    have : selfConv hankelProfile t = 0 := by
      unfold selfConv
      refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
      simp only [Pi.zero_apply]
      by_cases hs : s < 59 / 1000
      · rw [hankelProfile_eq_zero_of_lt hs, zero_mul]
      · rw [hankelProfile_eq_zero_of_lt (show t - s < 59 / 1000 by linarith [not_lt.mp hs]),
          mul_zero]
    rw [this, mul_zero]
  have hset : (∫ t in Ioi (0 : ℝ), wt t * selfConv hankelProfile t) =
      ∫ t, wt t * selfConv hankelProfile t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have hsplit : (fun t => wt t * selfConv hankelProfile t) = fun t =>
      wt t * bumpConv (bumpAt (3 / 50) (1 / 10000)) (bumpAt (3 / 50) (1 / 10000)) t -
        93 / 50 * (wt t * bumpConv (bumpAt (3 / 50) (1 / 10000)) (bumpAt (1 / 10) (1 / 10000)) t) -
        93 / 50 * (wt t * bumpConv (bumpAt (1 / 10) (1 / 10000)) (bumpAt (3 / 50) (1 / 10000)) t) +
        (93 / 50) ^ 2 *
          (wt t * bumpConv (bumpAt (1 / 10) (1 / 10000)) (bumpAt (1 / 10) (1 / 10000)) t) := by
    funext t; rw [selfConv_hankelProfile]; ring
  have i2 := b12.1.const_mul (93 / 50 : ℝ)
  have i3 := b21.1.const_mul (93 / 50 : ℝ)
  have i4 := b22.1.const_mul ((93 / 50 : ℝ) ^ 2)
  have i12 : Integrable fun t => wt t * bumpConv (bumpAt (3 / 50) (1 / 10000)) (bumpAt (3 / 50) (1 / 10000)) t -
      93 / 50 * (wt t * bumpConv (bumpAt (3 / 50) (1 / 10000)) (bumpAt (1 / 10) (1 / 10000)) t) :=
    b11.1.sub i2
  have i123 : Integrable fun t =>
      wt t * bumpConv (bumpAt (3 / 50) (1 / 10000)) (bumpAt (3 / 50) (1 / 10000)) t -
        93 / 50 * (wt t * bumpConv (bumpAt (3 / 50) (1 / 10000)) (bumpAt (1 / 10) (1 / 10000)) t) -
        93 / 50 * (wt t * bumpConv (bumpAt (1 / 10) (1 / 10000)) (bumpAt (3 / 50) (1 / 10000)) t) :=
    i12.sub i3
  have hfull : (∫ t, wt t * selfConv hankelProfile t) =
      (∫ t, wt t * bumpConv (bumpAt (3 / 50) (1 / 10000)) (bumpAt (3 / 50) (1 / 10000)) t) -
        93 / 50 * (∫ t, wt t * bumpConv (bumpAt (3 / 50) (1 / 10000)) (bumpAt (1 / 10) (1 / 10000)) t) -
        93 / 50 * (∫ t, wt t * bumpConv (bumpAt (1 / 10) (1 / 10000)) (bumpAt (3 / 50) (1 / 10000)) t) +
        (93 / 50) ^ 2 *
          (∫ t, wt t * bumpConv (bumpAt (1 / 10) (1 / 10000)) (bumpAt (1 / 10) (1 / 10000)) t) := by
    rw [hsplit, integral_add i123 i4, integral_sub i12 i3, integral_sub b11.1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul]
  have hε : (1 - 2 * Real.exp (-a * (1598 / 10000))) ≤ (1 - Real.exp (-a * (1598 / 10000))) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp (-a * (1598 / 10000)))]
  set m2 := (∫ x, bumpAt 0 (1 / 10000) x) ^ 2 with hm2
  have hm0 : 0 ≤ m2 := sq_nonneg _
  have e1 := b11.2.2
  have e2 := b12.2.1
  have e3 := b21.2.1
  have e4 := b22.2.2
  have hL : (1 - 2 * Real.exp (-a * (1598 / 10000))) * (135 / 100) * m2 ≤
      (1 - Real.exp (-a * (1598 / 10000))) ^ 2 * (135 / 100) * m2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε (by norm_num)) hm0
  show (∫ t in Ioi (0 : ℝ), wt t * selfConv hankelProfile t) ≤ _
  rw [hset, hfull]
  nlinarith [e1, e2, e3, e4, hL]

/-! ### The same-side term vanishes at infinite shift -/

/-- `(cosh u − 1) e^{−u} = (1 − e^{−u})²/2`. -/
theorem cosh_sub_one_mul_exp_neg (u : ℝ) :
    (Real.cosh u - 1) * Real.exp (-u) = (1 - Real.exp (-u)) ^ 2 / 2 := by
  have h : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  rw [Real.cosh_eq]
  linear_combination (1 / 2 : ℝ) * h

/-- The reweighted Hankel profile `G_a(y) = e^{−ay} H(y)`. -/
def reweightedHankel (a y : ℝ) : ℝ := Real.exp (-a * y) * hankelProfile y

theorem contDiff_reweightedHankel (a : ℝ) : ContDiff ℝ 2 (reweightedHankel a) :=
  (by fun_prop : ContDiff ℝ 2 fun y : ℝ => Real.exp (-a * y)).mul contDiff_hankelProfile

theorem hasCompactSupport_reweightedHankel (a : ℝ) : HasCompactSupport (reweightedHankel a) :=
  hasCompactSupport_hankelProfile.mul_left

/-- **The same-side term is `O(a e^{−0.118 a})`.** -/
theorem abs_integral_correction_reweightedHankel_le {a : ℝ} (ha : 0 ≤ a) :
    |∫ t in Ioi (0 : ℝ), (Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) *
        autoCorr (reweightedHankel a) t| ≤
      81 / 4 * (13 / 125) ^ 2 * a * Real.exp (-a * (59 / 500)) := by
  set r : ℝ := 13 / 125 with hr
  set K : ℝ := 81 / 4 * r * a * Real.exp (-a * (59 / 500)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hH := contDiff_hankelProfile.continuous
  have hHc := hasCompactSupport_hankelProfile
  have hH0 : ∀ y, y < 59 / 1000 → hankelProfile y = 0 := fun y hy => hankelProfile_eq_zero_of_lt hy
  -- the overlap integral of `|H|`
  have hover : ∀ t, (∫ x, |hankelProfile x| * |hankelProfile (x + t)|) ≤ 9 * r := by
    intro t
    have hint : Integrable fun x => |hankelProfile x| * |hankelProfile (x + t)| :=
      ((continuous_abs.comp hH).mul (continuous_abs.comp (hH.comp
        (continuous_id.add continuous_const)))).integrable_of_hasCompactSupport
          ((hHc.comp_left (by simp : |(0 : ℝ)| = 0)).mul_right)
    calc (∫ x, |hankelProfile x| * |hankelProfile (x + t)|) ≤
        ∫ x, (Icc 0 r).indicator (fun _ => (9 : ℝ)) x := by
          refine integral_mono hint ((integrable_indicator_iff measurableSet_Icc).mpr
            (integrableOn_const (by simp))) fun x => ?_
          by_cases hx : x ∈ Icc 0 r
          · rw [Set.indicator_of_mem hx]
            have h1 := abs_hankelProfile_le x
            have h2 := abs_hankelProfile_le (x + t)
            nlinarith [abs_nonneg (hankelProfile x), abs_nonneg (hankelProfile (x + t))]
          · rw [Set.indicator_of_notMem hx]
            have : hankelProfile x = 0 := by
              rw [mem_Icc, not_and_or, not_le, not_le] at hx
              rcases hx with hx | hx
              · exact hH0 x (by linarith)
              · exact hankelProfile_eq_zero_of_gt (by rw [hr] at hx; linarith)
            rw [this, abs_zero, zero_mul]
      _ = 9 * r := by
          rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
            Real.volume_real_Icc, max_eq_left (by rw [hr]; norm_num)]
          ring
  -- pointwise bound by the indicator of `(0, r]`
  have hpt : ∀ t ∈ Ioi (0 : ℝ), |(Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) *
      autoCorr (reweightedHankel a) t| ≤ (Ioc 0 r).indicator (fun _ => K) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases htr : t ≤ r
    · rw [Set.indicator_of_mem (show t ∈ Ioc 0 r from ⟨ht0, htr⟩)]
      have hA := abs_autoCorr_exp_mul_le hH hHc ha hH0 t
      have hA' : |autoCorr (reweightedHankel a) t| ≤
          Real.exp (-a * (2 * (59 / 1000) + t)) * (9 * r) := by
        unfold reweightedHankel
        exact hA.trans (mul_le_mul_of_nonneg_left (hover t) (Real.exp_pos _).le)
      have hω := archLevyDensity_le_of_le_one ht0 (by rw [hr] at htr; linarith)
      have hω0 := (archLevyDensity_pos ht0).le
      have hch : Real.cosh (t / 2) ≤ 3 / 2 := by
        have h1 := Real.cosh_le_exp_half_sq (t / 2)
        have h2 : (t / 2) ^ 2 / 2 ≤ 1 / 8 := by
          have : t ≤ 1 := by rw [hr] at htr; linarith
          nlinarith
        have h3 : Real.exp ((t / 2) ^ 2 / 2) ≤ Real.exp (1 / 8) := Real.exp_le_exp.mpr h2
        have h4 : Real.exp (1 / 8) ≤ 3 / 2 := by
          have := Real.exp_bound' (show (0 : ℝ) ≤ 1 / 8 by norm_num) (show (1 / 8 : ℝ) ≤ 1 by norm_num)
            (show 0 < 3 by norm_num)
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
          norm_num at this ⊢
          linarith
        linarith
      have hk : |2 * Real.cosh (t / 2) - archLevyDensity t| ≤ 3 + 3 / 2 / t := by
        have hcp := Real.cosh_pos (t / 2)
        have h32 : 0 ≤ 3 / 2 / t := by positivity
        rw [abs_le]; constructor <;> linarith
      have hc1 : 0 ≤ Real.cosh (a * t) - 1 := by linarith [Real.one_le_cosh (a * t)]
      have hce : (Real.cosh (a * t) - 1) * Real.exp (-(a * t)) ≤ a * t / 2 := by
        rw [cosh_sub_one_mul_exp_neg]
        have e1 : Real.exp (-(a * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        have e2 : 1 - a * t ≤ Real.exp (-(a * t)) := by linarith [Real.add_one_le_exp (-(a * t))]
        have e3 : 0 ≤ 1 - Real.exp (-(a * t)) := by linarith
        have e4 : 1 - Real.exp (-(a * t)) ≤ 1 := by linarith [Real.exp_pos (-(a * t))]
        have e5 := mul_le_mul_of_nonneg_left e4 e3
        nlinarith
      have hsplit : Real.exp (-a * (2 * (59 / 1000) + t)) =
          Real.exp (-a * (59 / 500)) * Real.exp (-(a * t)) := by
        rw [← Real.exp_add]; ring_nf
      rw [abs_mul, abs_mul, abs_of_nonneg hc1]
      calc (Real.cosh (a * t) - 1) * |2 * Real.cosh (t / 2) - archLevyDensity t| *
            |autoCorr (reweightedHankel a) t|
          ≤ (Real.cosh (a * t) - 1) * (3 + 3 / 2 / t) *
              (Real.exp (-a * (59 / 500)) * Real.exp (-(a * t)) * (9 * r)) := by
            rw [← hsplit]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hk hc1) hA' (abs_nonneg _)
              (mul_nonneg hc1 (by positivity))
        _ = ((Real.cosh (a * t) - 1) * Real.exp (-(a * t))) * (3 + 3 / 2 / t) *
              (9 * r * Real.exp (-a * (59 / 500))) := by ring
        _ ≤ (a * t / 2) * (3 + 3 / 2 / t) * (9 * r * Real.exp (-a * (59 / 500))) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hce (by positivity))
              (by positivity)
        _ = a * (3 / 2 * t + 3 / 4) * (9 * r * Real.exp (-a * (59 / 500))) := by
            field_simp; ring
        _ ≤ a * (9 / 4) * (9 * r * Real.exp (-a * (59 / 500))) := by
            have : t ≤ 1 := by rw [hr] at htr; linarith
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ha)
              (by positivity)
        _ = K := by rw [hK]; ring
    · rw [Set.indicator_of_notMem (fun h => htr h.2)]
      have hA0 : autoCorr (reweightedHankel a) t = 0 := by
        unfold autoCorr reweightedHankel
        refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
        simp only [Pi.zero_apply]
        by_cases hx : x < 59 / 1000
        · rw [hH0 x hx]; ring
        · rw [hankelProfile_eq_zero_of_gt (show 13 / 125 < x + t by
            rw [hr] at htr; linarith [not_lt.mp hx])]; ring
      rw [hA0, mul_zero, abs_zero]
  have hbound : IntegrableOn (fun t => (Ioc 0 r).indicator (fun _ => K) t) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))).integrableOn
  calc |∫ t in Ioi (0 : ℝ), (Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) *
        autoCorr (reweightedHankel a) t|
      ≤ ∫ t in Ioi (0 : ℝ), |(Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) *
          autoCorr (reweightedHankel a) t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi (0 : ℝ), (Ioc 0 r).indicator (fun _ => K) t := by
        refine setIntegral_mono_on ?_ hbound measurableSet_Ioi hpt
        refine hbound.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          rw [Real.norm_eq_abs, abs_abs]; exact hpt t ht)
        have hm : Measurable fun t => autoCorr (reweightedHankel a) t := by
          have hc : Continuous (Function.uncurry fun t x =>
              reweightedHankel a x * reweightedHankel a (x + t)) := by
            have := (contDiff_reweightedHankel a).continuous
            unfold Function.uncurry; fun_prop
          exact hc.stronglyMeasurable.integral_prod_right.measurable
        exact (((by fun_prop : Continuous fun t => Real.cosh (a * t) - 1).measurable.mul
          ((by fun_prop : Continuous fun t => 2 * Real.cosh (t / 2)).measurable.sub
            measurable_archLevyDensity)).mul hm).abs.aestronglyMeasurable
    _ = K * r := by
        rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Ioc_subset_Ioi_self,
          setIntegral_const, smul_eq_mul, Real.volume_real_Ioc, max_eq_left (by rw [hr]; norm_num)]
        ring
    _ = 81 / 4 * (13 / 125) ^ 2 * a * Real.exp (-a * (59 / 500)) := by rw [hK, hr]; ring

/-! ### Selectivity below the Markov window -/

/-- The odd extension `F_a(x) = G_a(x) − G_a(−x)` of the reweighted Hankel profile. -/
def oddReweightedHankel (a x : ℝ) : ℝ := reweightedHankel a x - reweightedHankel a (-x)

/-- The plateau mass `m = ∫ φ_0` of the bumps of half-width `10⁻⁴`. -/
def hankelMass : ℝ := ∫ x, bumpAt 0 (1 / 10000) x

theorem reweightedHankel_eq_zero_of_lt (a : ℝ) {y : ℝ} (hy : y < 59 / 1000) :
    reweightedHankel a y = 0 := by
  rw [reweightedHankel, hankelProfile_eq_zero_of_lt hy, mul_zero]

theorem reweightedHankel_eq_zero_of_abs (a : ℝ) {x : ℝ} (hx : 13 / 125 < |x|) :
    reweightedHankel a x = 0 := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx
    rw [reweightedHankel, hankelProfile_eq_zero_of_gt hx, mul_zero]
  · exact reweightedHankel_eq_zero_of_lt a (by linarith)

theorem oddReweightedHankel_eq_zero (a : ℝ) {x : ℝ} (hx : 13 / 125 < |x|) :
    oddReweightedHankel a x = 0 := by
  rw [oddReweightedHankel, reweightedHankel_eq_zero_of_abs a hx,
    reweightedHankel_eq_zero_of_abs a (by rwa [abs_neg]), sub_zero]

theorem oddReweightedHankel_neg (a x : ℝ) :
    oddReweightedHankel a (-x) = -oddReweightedHankel a x := by
  rw [oddReweightedHankel, oddReweightedHankel, neg_neg]; ring

theorem contDiff_oddReweightedHankel (a : ℝ) : ContDiff ℝ 2 (oddReweightedHankel a) :=
  (contDiff_reweightedHankel a).sub ((contDiff_reweightedHankel a).comp contDiff_neg)

theorem lt_abs_of_notMem_Icc {c x : ℝ} (hx : x ∉ Icc (-c) c) : c < |x| :=
  not_le.mp fun h => hx (abs_le.mp h)

theorem hasCompactSupport_oddReweightedHankel (a : ℝ) :
    HasCompactSupport (oddReweightedHankel a) :=
  HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun x hx =>
    oddReweightedHankel_eq_zero a (by linarith [lt_abs_of_notMem_Icc hx])

theorem abs_reweightedHankel_le {a : ℝ} (ha : 0 ≤ a) (y : ℝ) :
    |reweightedHankel a y| ≤ 3 * Real.exp (-a * (59 / 1000)) := by
  by_cases hy : y < 59 / 1000
  · rw [reweightedHankel_eq_zero_of_lt a hy, abs_zero]; positivity
  · rw [reweightedHankel, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-a * y) ≤ Real.exp (-a * (59 / 1000)) :=
      Real.exp_le_exp.mpr (by nlinarith [not_lt.mp hy])
    calc Real.exp (-a * y) * |hankelProfile y| ≤ Real.exp (-a * (59 / 1000)) * 3 :=
          mul_le_mul he (abs_hankelProfile_le y) (abs_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring

theorem abs_oddReweightedHankel_le {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    |oddReweightedHankel a x| ≤ 3 * Real.exp (-a * (59 / 1000)) := by
  rw [oddReweightedHankel]
  rcases le_or_gt 0 x with h | h
  · rw [reweightedHankel_eq_zero_of_lt a (show -x < 59 / 1000 by linarith), sub_zero]
    exact abs_reweightedHankel_le ha x
  · rw [reweightedHankel_eq_zero_of_lt a (show x < 59 / 1000 by linarith), zero_sub, abs_neg]
    exact abs_reweightedHankel_le ha (-x)

theorem exp_sq_eq (a : ℝ) : Real.exp (-a * (59 / 1000)) ^ 2 = Real.exp (-a * (59 / 500)) := by
  rw [sq, ← Real.exp_add]; congr 1; ring

theorem integral_sq_oddReweightedHankel_le {a : ℝ} (ha : 0 ≤ a) :
    (∫ x, oddReweightedHankel a x ^ 2) ≤ 18 * (13 / 125) * Real.exp (-a * (59 / 500)) := by
  have hcs : HasCompactSupport fun x => oddReweightedHankel a x ^ 2 :=
    HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun x hx => by
      rw [oddReweightedHankel_eq_zero a (by linarith [lt_abs_of_notMem_Icc hx]), zero_pow two_ne_zero]
  have hint : Integrable fun x => oddReweightedHankel a x ^ 2 :=
    ((contDiff_oddReweightedHankel a).continuous.pow 2).integrable_of_hasCompactSupport hcs
  calc (∫ x, oddReweightedHankel a x ^ 2) ≤ ∫ x, (Icc (-(13 / 125 : ℝ)) (13 / 125)).indicator
        (fun _ => (3 * Real.exp (-a * (59 / 1000))) ^ 2) x := by
        refine integral_mono hint ((integrable_indicator_iff measurableSet_Icc).mpr
          (integrableOn_const (by simp))) fun x => ?_
        by_cases hx : x ∈ Icc (-(13 / 125 : ℝ)) (13 / 125)
        · rw [Set.indicator_of_mem hx, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_oddReweightedHankel_le ha x) 2
        · rw [Set.indicator_of_notMem hx, oddReweightedHankel_eq_zero a (lt_abs_of_notMem_Icc hx)]
          norm_num
    _ = 18 * (13 / 125) * Real.exp (-a * (59 / 500)) := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
          Real.volume_real_Icc, max_eq_left (by norm_num), mul_pow, exp_sq_eq]
        ring

theorem lipschitz_oddReweightedHankel {a LH : ℝ} (ha : 0 ≤ a)
    (hLH : ∀ x y, |hankelProfile y - hankelProfile x| ≤ LH * |y - x|) (u v : ℝ) :
    |oddReweightedHankel a u - oddReweightedHankel a v| ≤
      2 * Real.exp (-a * (59 / 1000)) * (LH + a * 3) * |u - v| := by
  have hG : ∀ u v, |reweightedHankel a u - reweightedHankel a v| ≤
      Real.exp (-a * (59 / 1000)) * (LH + a * 3) * |u - v| :=
    fun u v => lipschitz_exp_mul ha (fun y hy => hankelProfile_eq_zero_of_lt hy)
      (fun u v => hLH v u) abs_hankelProfile_le u v
  have h1 := hG u v
  have h2 := hG (-u) (-v)
  rw [show -u - -v = -(u - v) by ring, abs_neg] at h2
  rw [oddReweightedHankel, oddReweightedHankel,
    show reweightedHankel a u - reweightedHankel a (-u) -
        (reweightedHankel a v - reweightedHankel a (-v)) =
      (reweightedHankel a u - reweightedHankel a v) -
        (reweightedHankel a (-u) - reweightedHankel a (-v)) by ring]
  have h3 := abs_sub (reweightedHankel a u - reweightedHankel a v)
    (reweightedHankel a (-u) - reweightedHankel a (-v))
  linarith

/-- **The comparison identity for `F_a = G_a − G̃_a`.** The cross term between `G_a` and its
reflection is the weighted Hankel form of `H`:
`Ẑ_a(F_a) = 2Ẑ(F_a) + 8∫(cosh(at) − 1)κ A_{G_a} + 2∫(1 − e^{−at})² f (H ∗ H)`. -/
theorem shiftedPairZeroForm_oddReweightedHankel (a : ℝ) :
    shiftedPairZeroForm a (oddReweightedHankel a) = 2 * fullZeroForm (oddReweightedHankel a) +
      8 * (∫ t in Ioi (0 : ℝ), (Real.cosh (a * t) - 1) *
        (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (reweightedHankel a) t) +
      2 * ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-a * t)) ^ 2 * screwWeight t *
        selfConv hankelProfile t := by
  have hlog : 2 * (13 / 125 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  obtain ⟨hIF, hEF⟩ := shiftedPairZeroForm_eq (contDiff_oddReweightedHankel a)
    (hasCompactSupport_oddReweightedHankel a) (fun x hx => oddReweightedHankel_eq_zero a hx)
    (by norm_num) hlog a
  obtain ⟨hIG, -⟩ := shiftedPairZeroForm_eq (contDiff_reweightedHankel a)
    (hasCompactSupport_reweightedHankel a) (fun x hx => reweightedHankel_eq_zero_of_abs a hx)
    (by norm_num) hlog a
  have hptw : ∀ t ∈ Ioi (0 : ℝ), (Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (oddReweightedHankel a) t =
        2 * ((Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) *
          autoCorr (reweightedHankel a) t) +
        1 / 2 * ((1 - Real.exp (-a * t)) ^ 2 * screwWeight t * selfConv hankelProfile t) := by
    intro t ht
    have hA : autoCorr (oddReweightedHankel a) t =
        2 * autoCorr (reweightedHankel a) t - selfConv (reweightedHankel a) t :=
      autoCorr_sub_reflect (contDiff_reweightedHankel a).continuous
        (hasCompactSupport_reweightedHankel a)
        (fun x hx => reweightedHankel_eq_zero_of_lt a (by linarith)) ht
    have hS : selfConv (reweightedHankel a) t = Real.exp (-a * t) * selfConv hankelProfile t :=
      selfConv_exp_mul hankelProfile a t
    have hce := cosh_sub_one_mul_exp_neg (a * t)
    rw [← neg_mul] at hce
    rw [hA, hS, screwWeight]
    linear_combination
      (-(2 * Real.cosh (t / 2) - archLevyDensity t) * selfConv hankelProfile t) * hce
  have hIF' : Integrable (fun t => (Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (oddReweightedHankel a) t)
      (volume.restrict (Ioi 0)) := hIF
  have hIG' : Integrable (fun t => 2 * ((Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (reweightedHankel a) t))
      (volume.restrict (Ioi 0)) := hIG.const_mul 2
  have hdiff : Integrable (fun t => (Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (oddReweightedHankel a) t -
        2 * ((Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) *
          autoCorr (reweightedHankel a) t)) (volume.restrict (Ioi 0)) := hIF'.sub hIG'
  have hIW : Integrable (fun t => 1 / 2 *
      ((1 - Real.exp (-a * t)) ^ 2 * screwWeight t * selfConv hankelProfile t))
      (volume.restrict (Ioi 0)) :=
    hdiff.congr ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
      dsimp only; rw [hptw t ht]; ring)
  rw [hEF, setIntegral_congr_fun measurableSet_Ioi hptw, integral_add hIG' hIW,
    integral_const_mul, integral_const_mul]
  ring

/-- The explicit upper bound for `Ẑ_a(F_a)`: the Hankel main term `2m²Q₀` plus a polynomial
times `e^{−0.118 a}`. -/
theorem shiftedPairZeroForm_oddReweightedHankel_le {a C LH : ℝ} (ha : 0 ≤ a)
    (hC : ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, 13 / 125 < |x| → F x = 0) →
      ∀ K : ℝ, (∀ a b, |F a - F b| ≤ K * |a - b|) → fullZeroForm F ≤ K ^ 2 + C * ∫ x, F x ^ 2)
    (hLH : ∀ x y, |hankelProfile y - hankelProfile x| ≤ LH * |y - x|) :
    shiftedPairZeroForm a (oddReweightedHankel a) ≤
      2 * hankelMass ^ 2 * (243 / 100 - 27 / 10 * (93 / 50) + 74 / 100 * (93 / 50) ^ 2) +
        (72 * a ^ 2 + (48 * LH + 162 * (13 / 125) ^ 2) * a +
          (8 * LH ^ 2 + 36 * (13 / 125) * max C 0 + 54 / 5 * (93 / 50) * hankelMass ^ 2)) *
          Real.exp (-a * (59 / 500)) := by
  have hZ := hC _ (contDiff_oddReweightedHankel a) (hasCompactSupport_oddReweightedHankel a)
    (fun x hx => oddReweightedHankel_eq_zero a hx) _ (lipschitz_oddReweightedHankel ha hLH)
  have hI0 : 0 ≤ ∫ x, oddReweightedHankel a x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hCI : C * (∫ x, oddReweightedHankel a x ^ 2) ≤
      max C 0 * (18 * (13 / 125) * Real.exp (-a * (59 / 500))) :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hI0).trans
      (mul_le_mul_of_nonneg_left (integral_sq_oddReweightedHankel_le ha) (le_max_right C 0))
  have hK : (2 * Real.exp (-a * (59 / 1000)) * (LH + a * 3)) ^ 2 =
      4 * Real.exp (-a * (59 / 500)) * (LH + a * 3) ^ 2 := by
    rw [← exp_sq_eq]; ring
  have hT1 := (abs_le.mp (abs_integral_correction_reweightedHankel_le ha)).2
  rw [show -a * (59 / 500) = -a * (59 / 500 : ℝ) from rfl] at hT1
  have hT2 : (∫ t in Ioi (0 : ℝ), (1 - Real.exp (-a * t)) ^ 2 * screwWeight t *
      selfConv hankelProfile t) ≤ hankelMass ^ 2 *
        ((243 / 100 - 27 / 10 * (93 / 50) + 74 / 100 * (93 / 50) ^ 2) +
          27 / 5 * (93 / 50) * Real.exp (-a * (1598 / 10000))) :=
    integral_weighted_hankelProfile_le ha
  have he : Real.exp (-a * (1598 / 10000)) ≤ Real.exp (-a * (59 / 500)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hm : hankelMass ^ 2 * Real.exp (-a * (1598 / 10000)) ≤
      hankelMass ^ 2 * Real.exp (-a * (59 / 500)) :=
    mul_le_mul_of_nonneg_left he (sq_nonneg _)
  rw [shiftedPairZeroForm_oddReweightedHankel]
  linear_combination 2 * hZ + 2 * hCI + 2 * hK + 8 * hT1 + 2 * hT2 + 54 / 5 * (93 / 50) * hm

theorem tendsto_pow_mul_exp_neg_mul {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    Tendsto (fun a : ℝ => a ^ n * Real.exp (-a * β)) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop hβ)).const_mul ((β ^ n)⁻¹)
  rw [mul_zero] at h
  refine h.congr fun a => ?_
  have hβn : β ^ n ≠ 0 := pow_ne_zero n hβ.ne'
  simp only [Function.comp_apply, id_eq, mul_pow]
  rw [show -(β * a) = -a * β by ring, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hβn, one_mul]

/-- **The shifted pair fails below the Markov window.** For every large shift `a` there is an odd
`F ∈ C²_c` supported in `[−13/125, 13/125]` with negative `ζ(s − a) ζ(s + a)` zero form. -/
theorem exists_odd_shiftedPairZeroForm_neg_below_markovWindow :
    ∃ a₀ : ℝ, ∀ a, a₀ ≤ a → ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      (∀ x, F (-x) = -F x) ∧ (∀ x, 13 / 125 < |x| → F x = 0) ∧ shiftedPairZeroForm a F < 0 := by
  have hlog : 2 * (13 / 125 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  obtain ⟨C, hC⟩ := exists_fullZeroForm_le_lipschitz (r := 13 / 125) (by norm_num) hlog
  obtain ⟨LH, -, hLH⟩ := exists_lipschitz_bound_of_compactSupport
    (contDiff_hankelProfile.of_le (by norm_num)) hasCompactSupport_hankelProfile
  have hm : 0 < hankelMass ^ 2 := by
    have : (1 : ℝ) / 10000 ≤ hankelMass := le_integral_bumpAt (by norm_num)
    positivity
  have hε : 0 < -(2 * hankelMass ^ 2 * (243 / 100 - 27 / 10 * (93 / 50) + 74 / 100 * (93 / 50) ^ 2)) := by
    nlinarith
  have hβ : (0 : ℝ) < 59 / 500 := by norm_num
  have htend := (((tendsto_pow_mul_exp_neg_mul hβ 2).const_mul 72).add
    ((tendsto_pow_mul_exp_neg_mul hβ 1).const_mul (48 * LH + 162 * (13 / 125) ^ 2))).add
    ((tendsto_pow_mul_exp_neg_mul hβ 0).const_mul
      (8 * LH ^ 2 + 36 * (13 / 125) * max C 0 + 54 / 5 * (93 / 50) * hankelMass ^ 2))
  simp only [mul_zero, add_zero, pow_one, pow_zero, one_mul] at htend
  obtain ⟨a₁, ha₁⟩ := eventually_atTop.mp (htend.eventually (gt_mem_nhds hε))
  refine ⟨max a₁ 0, fun a ha => ⟨oddReweightedHankel a, contDiff_oddReweightedHankel a,
    hasCompactSupport_oddReweightedHankel a, oddReweightedHankel_neg a,
    fun x hx => oddReweightedHankel_eq_zero a hx, ?_⟩⟩
  have hbound := shiftedPairZeroForm_oddReweightedHankel_le (le_trans (le_max_right _ _) ha) hC hLH
  have hsmall := ha₁ a (le_trans (le_max_left _ _) ha)
  linarith

/-- **ζ against `ζ(s − a) ζ(s + a)` at the Markov window.** Every test supported in
`[−21/200, 21/200]` has `Ẑ(F) ≥ (1/30)∫F²` for `ζ`, while for every large shift `a` some odd test
supported in `[−13/125, 13/125]` has negative zero form for `ζ(s − a) ζ(s + a)`. -/
theorem markovWindow_selective :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, 21 / 200 < |x| → F x = 0) →
        1 / 30 * ∫ x, F x ^ 2 ≤ fullZeroForm F) ∧
      ∃ a₀ : ℝ, ∀ a, a₀ ≤ a → ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
        (∀ x, F (-x) = -F x) ∧ (∀ x, 13 / 125 < |x| → F x = 0) ∧ shiftedPairZeroForm a F < 0 :=
  ⟨fun _ hF hFc hsupp => fullZeroForm_ge_of_support_le_sharp hF hFc hsupp,
    exists_odd_shiftedPairZeroForm_neg_below_markovWindow⟩

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
