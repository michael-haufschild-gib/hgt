import GaloisForLFunctions.FloorFreeArithmetic.FiniteTopLayersAreSeenOnEveryWindow
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.LengthDependentFloorsGiveTheAbscissaLaw
import GaloisForLFunctions.SurfaceOfSpecZ.TwoFrobeniiSeeEveryConfiguration

/-!
# Moments on windows amplify the depth

For a configuration with a finite top layer at depth `b`, the even moments of the spline trace
over a window `[T, T + L]` of fixed length have the exact rate `2k·b`:

`η (c e^{bT})^{2k} ≤ ∫_T^{T+L} (2 Re S(u))^{2k} du ≤ L (B e^{b(T+L)})^{2k}`

with `c`, `η`, `B` independent of `k` and `T`. The order multiplies the depth and nothing else.
Hence a bound for all even moments with one growth exponent, on arbitrarily late windows of one
fixed length and with constants depending on the order, gives the asymptotic abscissa law: the
amplification receiver for the law.

* `abs_topTrace_sub_le`: the top trace of a finite layer is Lipschitz.
* `finite_top_moment_lower_bound`, `finite_top_moment_upper_bound`: the two-sided moment law.
* `asymptoticAbscissaLaw_of_window_moments`: the receiver.
* `asymptoticAbscissaLaw_of_moment_window_nonAttainment`: non-attainment in the mean of one
  order. A moment of one order that is of smaller order than its own rate `e^{2kbT}` on
  arbitrarily late windows gives the law; for `k = 1` this is non-attainment in mean square.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality

/-! ### The top trace is Lipschitz -/

/-- A phase moves at most at its frequency. -/
theorem norm_cexp_mul_I_sub_le (a b : ℝ) :
    ‖cexp ((a : ℂ) * I) - cexp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have h : cexp ((a : ℂ) * I) - cexp ((b : ℂ) * I) =
      cexp ((b : ℂ) * I) * (cexp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq (Real.norm_eq_abs _))

/-- The top trace of a finite layer is Lipschitz with constant `Σ 2|e_z| γ_z`. -/
theorem abs_topTrace_sub_le {Z : ZeroConfig} {b : ℝ} (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0) (u v : ℝ) :
    |topTrace Z b u - topTrace Z b v| ≤
      (∑ z ∈ S, 2 * ‖evenCoeff Z (boxSpline 1 3) z‖ * z.im) * |u - v| := by
  rw [topTrace_eq_positive_sum S hS hreal u, topTrace_eq_positive_sum S hS hreal v,
    ← Complex.sub_re, ← Finset.sum_sub_distrib]
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun z hz => ?_
  have hpos : 0 < z.im := ((hS z).mp hz).2.1
  have h2 : ‖(2 : ℂ) * evenCoeff Z (boxSpline 1 3) z‖ = 2 * ‖evenCoeff Z (boxSpline 1 3) z‖ := by
    rw [norm_mul, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  have hph := norm_cexp_mul_I_sub_le (z.im * u) (z.im * v)
  have hfreq : |z.im * u - z.im * v| = z.im * |u - v| := by
    rw [← mul_sub, abs_mul, abs_of_pos hpos]
  rw [hfreq] at hph
  rw [← mul_sub, norm_mul, h2]
  calc 2 * ‖evenCoeff Z (boxSpline 1 3) z‖ *
        ‖cexp (((z.im * u : ℝ) : ℂ) * I) - cexp (((z.im * v : ℝ) : ℂ) * I)‖
      ≤ 2 * ‖evenCoeff Z (boxSpline 1 3) z‖ * (z.im * |u - v|) :=
        mul_le_mul_of_nonneg_left hph (by positivity)
    _ = 2 * ‖evenCoeff Z (boxSpline 1 3) z‖ * z.im * |u - v| := by ring

/-- The top trace of a finite layer is bounded by `Σ 2|e_z|`. -/
theorem abs_topTrace_le {Z : ZeroConfig} {b : ℝ} (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0) (u : ℝ) :
    |topTrace Z b u| ≤ ∑ z ∈ S, 2 * ‖evenCoeff Z (boxSpline 1 3) z‖ := by
  rw [topTrace_eq_positive_sum S hS hreal u]
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_mul,
    show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
  norm_num

/-- The spline trace is the normalized trace times its rate. -/
theorem two_re_lagStructure_eq_normTrace_mul (Z : ZeroConfig) (b u : ℝ) :
    2 * (lagStructure Z (boxSpline 1 3) u).re = normTrace Z b u * Real.exp (b * u) := by
  have hone : Real.exp (-(b * u)) * Real.exp (b * u) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  unfold normTrace
  linear_combination (-(2 * (lagStructure Z (boxSpline 1 3) u).re)) * hone

/-! ### The moment law of a finite top layer -/

/-- **Lower moment bound.** A finite nonempty active top layer at depth `b ≥ 0` gives
`η (c e^{bT})^{2k} ≤ ∫_T^{T+L} (2 Re S)^{2k}` on every late window, for every order `k`, with
`c, η > 0` independent of `k` and `T`. -/
theorem finite_top_moment_lower_bound {Z : ZeroConfig} (hZ : TemperedConfig Z) {b L : ℝ}
    (hb : 0 ≤ b) (htop : TopDepth Z b) (hL : 0 < L) (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b) (hne : S.Nonempty)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0) :
    ∃ c η U : ℝ, 0 < c ∧ 0 < η ∧ ∀ T : ℝ, U ≤ T → ∀ k : ℕ,
      η * (c * Real.exp (b * T)) ^ (2 * k) ≤
        ∫ u in T..(T + L), (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k) := by
  obtain ⟨c, U₁, hc, hwin⟩ :=
    finite_top_seen_on_every_window hZ htop (half_pos hL) S hS hne hreal
  have hrem := tendsto_normTrace_sub_topTrace hZ htop
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    ((tendsto_order.mp hrem).1 (-(c / 8)) (by linarith only [hc]) |>.and
      ((tendsto_order.mp hrem).2 (c / 8) (by linarith only [hc])))
  set D : ℝ := ∑ z ∈ S, 2 * ‖evenCoeff Z (boxSpline 1 3) z‖ * z.im with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun z hz =>
    mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) ((hS z).mp hz).2.1.le
  -- a sub-window on which the trace stays large
  set η : ℝ := min (L / 2) (c / (8 * (D + 1))) with hη
  have hD1 : (0 : ℝ) < 8 * (D + 1) := by linarith only [hD0]
  have hη0 : 0 < η := lt_min (half_pos hL) (div_pos hc hD1)
  have hηL : η ≤ L / 2 := min_le_left _ _
  have hDη : D * η ≤ c / 8 := by
    have h1 : η ≤ c / (8 * (D + 1)) := min_le_right _ _
    have h2 := (le_div_iff₀ hD1).mp h1
    nlinarith only [h2, hη0, hD0]
  refine ⟨c / 2, η, max U₁ V, half_pos hc, hη0, fun T hT k => ?_⟩
  obtain ⟨u₀, hu₀, hbig⟩ := hwin T ((le_max_left _ _).trans hT)
  have hVT : V ≤ T := (le_max_right _ _).trans hT
  have hfc : Continuous fun u : ℝ => (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k) :=
    (continuous_two_re_lagStructure hZ).pow _
  have hf0 : ∀ u : ℝ, 0 ≤ (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k) :=
    fun u => (even_two_mul k).pow_nonneg _
  have hpt : ∀ u ∈ Icc u₀ (u₀ + η), (c / 2 * Real.exp (b * T)) ^ (2 * k) ≤
      (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k) := by
    intro u hu
    obtain ⟨hlo, hhi⟩ := hV u (hVT.trans (hu₀.1.trans hu.1))
    obtain ⟨hlo₀, hhi₀⟩ := hV u₀ (hVT.trans hu₀.1)
    have hdist : |u - u₀| ≤ η := by
      rw [abs_of_nonneg (by linarith only [hu.1])]
      linarith only [hu.2]
    have hlip : |topTrace Z b u - topTrace Z b u₀| ≤ c / 8 :=
      (abs_topTrace_sub_le S hS hreal u u₀).trans
        ((mul_le_mul_of_nonneg_left hdist hD0).trans hDη)
    obtain ⟨e1, e1'⟩ := abs_le.mp hlip
    have hclose : |normTrace Z b u₀ - normTrace Z b u| ≤ 3 * c / 8 :=
      abs_le.mpr ⟨by linarith only [hlo, hhi, hlo₀, hhi₀, e1, e1'],
        by linarith only [hlo, hhi, hlo₀, hhi₀, e1, e1']⟩
    have htri := abs_sub_abs_le_abs_sub (normTrace Z b u₀) (normTrace Z b u)
    have hnorm : c / 2 ≤ |normTrace Z b u| := by linarith only [htri, hclose, hbig, hc]
    have hexp : Real.exp (b * T) ≤ Real.exp (b * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hu₀.1.trans hu.1) hb)
    have habs : c / 2 * Real.exp (b * T) ≤ |2 * (lagStructure Z (boxSpline 1 3) u).re| := by
      rw [two_re_lagStructure_eq_normTrace_mul Z b u, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul hnorm hexp (Real.exp_pos _).le (abs_nonneg _)
    calc (c / 2 * Real.exp (b * T)) ^ (2 * k)
        ≤ |2 * (lagStructure Z (boxSpline 1 3) u).re| ^ (2 * k) :=
          pow_le_pow_left₀ (mul_nonneg (half_pos hc).le (Real.exp_pos _).le) habs _
      _ = (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k) := (even_two_mul k).pow_abs _
  have hsub : (∫ u in u₀..(u₀ + η), (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k)) ≤
      ∫ u in T..(T + L), (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k) :=
    intervalIntegral.integral_mono_interval hu₀.1 (by linarith only [hη0])
      (by linarith only [hu₀.2, hηL]) (Eventually.of_forall hf0) (hfc.intervalIntegrable _ _)
  have hconst := intervalIntegral.integral_mono_on (by linarith only [hη0] : u₀ ≤ u₀ + η)
    (intervalIntegrable_const (μ := volume) (c := (c / 2 * Real.exp (b * T)) ^ (2 * k)))
    (hfc.intervalIntegrable _ _) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hconst
  exact hconst.trans hsub

/-- **Upper moment bound.** With the same layer, `∫_T^{T+L} (2 Re S)^{2k} ≤ L (B e^{b(T+L)})^{2k}`
on every late window, for every order `k`. -/
theorem finite_top_moment_upper_bound {Z : ZeroConfig} (hZ : TemperedConfig Z) {b L : ℝ}
    (hb : 0 ≤ b) (htop : TopDepth Z b) (hL : 0 < L) (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0) :
    ∃ B U : ℝ, 0 < B ∧ ∀ T : ℝ, U ≤ T → ∀ k : ℕ,
      (∫ u in T..(T + L), (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k)) ≤
        L * (B * Real.exp (b * (T + L))) ^ (2 * k) := by
  have hrem := tendsto_normTrace_sub_topTrace hZ htop
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    ((tendsto_order.mp hrem).1 (-1) (by norm_num) |>.and
      ((tendsto_order.mp hrem).2 1 (by norm_num)))
  set B₀ : ℝ := ∑ z ∈ S, 2 * ‖evenCoeff Z (boxSpline 1 3) z‖ with hB₀
  have hB₀0 : 0 ≤ B₀ := Finset.sum_nonneg fun z _ => mul_nonneg zero_le_two (norm_nonneg _)
  have hB : 0 < B₀ + 1 := by linarith only [hB₀0]
  refine ⟨B₀ + 1, V, hB, fun T hT k => ?_⟩
  have hfc : Continuous fun u : ℝ => (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k) :=
    (continuous_two_re_lagStructure hZ).pow _
  have hpt : ∀ u ∈ Icc T (T + L), (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k) ≤
      ((B₀ + 1) * Real.exp (b * (T + L))) ^ (2 * k) := by
    intro u hu
    obtain ⟨hlo, hhi⟩ := hV u (hT.trans hu.1)
    obtain ⟨t1, t2⟩ := abs_le.mp (abs_topTrace_le S hS hreal u)
    have hnorm : |normTrace Z b u| ≤ B₀ + 1 :=
      abs_le.mpr ⟨by linarith only [hlo, t1], by linarith only [hhi, t2]⟩
    have hexp : Real.exp (b * u) ≤ Real.exp (b * (T + L)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hb)
    have habs : |2 * (lagStructure Z (boxSpline 1 3) u).re| ≤
        (B₀ + 1) * Real.exp (b * (T + L)) := by
      rw [two_re_lagStructure_eq_normTrace_mul Z b u, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul hnorm hexp (Real.exp_pos _).le hB.le
    calc (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k)
        = |2 * (lagStructure Z (boxSpline 1 3) u).re| ^ (2 * k) :=
          ((even_two_mul k).pow_abs _).symm
      _ ≤ ((B₀ + 1) * Real.exp (b * (T + L))) ^ (2 * k) :=
          pow_le_pow_left₀ (abs_nonneg _) habs _
  have hconst := intervalIntegral.integral_mono_on (by linarith only [hL] : T ≤ T + L)
    (hfc.intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume) (c := ((B₀ + 1) * Real.exp (b * (T + L))) ^ (2 * k))) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hconst
  exact hconst

/-! ### The amplification receiver -/

/-- **One growth exponent for all even moments gives the abscissa law.** Suppose that on
arbitrarily late windows of one fixed length `L` the `2k`-th moment of the spline trace is at
most `C_k e^{AT}`, with one exponent `A` for all orders `k ≥ 1`. Then the asymptotic abscissa
law holds. The constants and the windows may depend on the order. -/
theorem asymptoticAbscissaLaw_of_window_moments
    (h : ∃ L : ℝ, 0 < L ∧ ∃ A : ℝ, ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      (∫ u in T..(T + L),
        (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re) ^ (2 * k)) ≤
          C * Real.exp (A * T)) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  obtain ⟨L, hL, A, hA⟩ := h
  by_contra hnot
  obtain ⟨b, hb, htop, S, hS, hne⟩ := exists_finite_top_of_not_abscissaLaw hnot
  obtain ⟨c, η, U₀, hc, hη, hlow⟩ := finite_top_moment_lower_bound
    temperedConfig_zetaZeroConfig hb.le htop hL S hS hne (fun z hz _ => evenCoeff_spline_real hz)
  -- an order whose amplified depth exceeds the common exponent
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (|A| / (2 * b)))
  have hk1 : 1 ≤ k := by
    have h1 : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
    exact_mod_cast h1.le
  have hkA : |A| / (2 * b) < k := (le_max_right _ _).trans_lt hk
  have hg : 0 < 2 * (k : ℝ) * b - A := by
    have h1 := (div_lt_iff₀ (by linarith only [hb] : (0 : ℝ) < 2 * b)).mp hkA
    linarith only [h1, le_abs_self A]
  obtain ⟨C, hC⟩ := hA k hk1
  have hκ0 : 0 < η * c ^ (2 * k) := mul_pos hη (pow_pos hc _)
  have hκg : 0 < η * c ^ (2 * k) * (2 * (k : ℝ) * b - A) := mul_pos hκ0 hg
  obtain ⟨T, hT, hup⟩ :=
    hC (max U₀ (|C| / (η * c ^ (2 * k) * (2 * (k : ℝ) * b - A)) + 1))
  have hT1 : |C| / (η * c ^ (2 * k) * (2 * (k : ℝ) * b - A)) + 1 ≤ T :=
    (le_max_right _ _).trans hT
  have hlo := hlow T ((le_max_left _ _).trans hT) k
  have hE : 0 < Real.exp (A * T) := Real.exp_pos _
  have hpow : (c * Real.exp (b * T)) ^ (2 * k) =
      c ^ (2 * k) * (Real.exp ((2 * (k : ℝ) * b - A) * T) * Real.exp (A * T)) := by
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    push_cast
    ring
  rw [hpow] at hlo
  have h1 : η * c ^ (2 * k) * Real.exp ((2 * (k : ℝ) * b - A) * T) ≤ C := by
    have h2 : η * c ^ (2 * k) * Real.exp ((2 * (k : ℝ) * b - A) * T) * Real.exp (A * T) ≤
        C * Real.exp (A * T) := by
      have h3 := hlo.trans hup
      linarith only [h3, mul_assoc (η * c ^ (2 * k)) (Real.exp ((2 * (k : ℝ) * b - A) * T))
        (Real.exp (A * T)), mul_assoc η (c ^ (2 * k))
        (Real.exp ((2 * (k : ℝ) * b - A) * T) * Real.exp (A * T))]
    exact le_of_mul_le_mul_right h2 hE
  have h3 : (2 * (k : ℝ) * b - A) * T + 1 ≤ Real.exp ((2 * (k : ℝ) * b - A) * T) :=
    Real.add_one_le_exp _
  have h4 : |C| + η * c ^ (2 * k) * (2 * (k : ℝ) * b - A) ≤
      η * c ^ (2 * k) * (2 * (k : ℝ) * b - A) * T := by
    have h5 := mul_le_mul_of_nonneg_left hT1 hκg.le
    rw [mul_add, mul_one, mul_div_cancel₀ _ hκg.ne'] at h5
    exact h5
  have h5 := mul_le_mul_of_nonneg_left h3 hκ0.le
  have h6 : η * c ^ (2 * k) * ((2 * (k : ℝ) * b - A) * T + 1) =
      η * c ^ (2 * k) * (2 * (k : ℝ) * b - A) * T + η * c ^ (2 * k) := by ring
  linarith only [h1, h4, h5, h6, le_abs_self C, hκ0, hκg]

/-- **Non-attainment in the mean of one order gives the abscissa law.** Suppose that at every
depth `b > 0` bounding the zeros there are a length `L` and an order `k` such that on
arbitrarily late windows of length `L` the `2k`-th moment of the spline trace is at most
`ε e^{2kbT}`, for every `ε > 0`. Then the asymptotic abscissa law holds. -/
theorem asymptoticAbscissaLaw_of_moment_window_nonAttainment
    (h : ∀ b : ℝ, 0 < b → TopDepth zetaZeroConfig b → ∃ L : ℝ, 0 < L ∧ ∃ k : ℕ,
      ∀ ε : ℝ, 0 < ε → ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
        (∫ u in T..(T + L),
          (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re) ^ (2 * k)) ≤
            ε * Real.exp (b * T) ^ (2 * k)) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  obtain ⟨b, hb, htop, S, hS, hne⟩ := exists_finite_top_of_not_abscissaLaw hnot
  obtain ⟨L, hL, k, hk⟩ := h b hb htop
  obtain ⟨c, η, U₀, hc, hη, hlow⟩ := finite_top_moment_lower_bound
    temperedConfig_zetaZeroConfig hb.le htop hL S hS hne (fun z hz _ => evenCoeff_spline_real hz)
  have hκ : 0 < η * c ^ (2 * k) := mul_pos hη (pow_pos hc _)
  obtain ⟨T, hT, hup⟩ := hk (η * c ^ (2 * k) / 2) (half_pos hκ) U₀
  have hlo := hlow T hT k
  rw [mul_pow] at hlo
  have hE : 0 < Real.exp (b * T) ^ (2 * k) := pow_pos (Real.exp_pos _) _
  have hle := hlo.trans hup
  have hpos := mul_pos hκ hE
  have e1 : η * (c ^ (2 * k) * Real.exp (b * T) ^ (2 * k)) =
      η * c ^ (2 * k) * Real.exp (b * T) ^ (2 * k) := by ring
  have e2 : η * c ^ (2 * k) / 2 * Real.exp (b * T) ^ (2 * k) =
      η * c ^ (2 * k) * Real.exp (b * T) ^ (2 * k) / 2 := by ring
  rw [e1, e2] at hle
  linarith only [hle, hpos]

end GaloisForLFunctions.FloorFreeArithmetic
