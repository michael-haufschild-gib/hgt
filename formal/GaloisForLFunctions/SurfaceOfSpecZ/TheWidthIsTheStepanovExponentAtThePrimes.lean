import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovCountAtThePrimeDegrees

/-!
# The width is the Stepanov exponent at the primes

`TheStepanovCountAtThePrimeDegrees` proves that a lower bound `2 Re S(log p) ≥ −K` at the primes is RH.
The same argument reads the zero width off the growth of the lower bound.

**Theorem** (`zetaZeroWidth_le_iff_bddBelow_primeDegrees`). For `0 ≤ a < ½`,

  `zetaZeroWidth ≤ a  ⟺  2 Re S(log p) ≥ −K p^a for every prime p`,

`S` the lag structure of the cubic spline. The exponent of a one-sided crude bound on the smoothed
point counts at the prime degrees is the width; `a = 0` is RH. Read negatively it is an oscillation
theorem sampled at the primes: if a zero has `Re ρ > ½ + a`, then `2 Re S(log p) < −K p^a` for
infinitely many primes, for every `K`.

**Proof.**
1. *The gap method with a growing bound* (`re_le_of_bddBelow_exp_of_powGaps`): degrees with gaps
   `x^θ` transfer `−K d^a` to `2 Re S(u) ≥ −M e^{bu}`, `b = max(a, θ − ½)`, and Landau's theorem for
   the spline exponents puts every zero in `Re ρ ≤ ½ + b`. At the primes `θ = 5/8`, `b = max(a, 1/8)`.
2. *The weighted von Mangoldt series.* The nonnegative series
   `Σ_q Λ(q)(2 Re S(log q) q^{−a} + K + 1) q^{−s}` equals `−Σ_z e_z ζ'/ζ(s + a − z) − (K + 1)ζ'/ζ(s)`
   right of `1 + b − a` (`gdSeries_widthCoeff_eq`). For `1 < Re s < 2 − a − b` the arguments
   `s + a − z` lie at distance `≥ ½ + a − 2b > 0` right of the zeros, so the sum continues off the
   poles `1 − a + z` (`differentiableAt_shiftLogDerivOf`). The higher prime powers contribute a
   series holomorphic on `Re s > ¾ + (b − a)/2`. Landau's theorem puts the abscissa at `1`, and a zero
   with `Re ρ > ½ + a` gives a pole `1 − a + z₀` right of it (`forall_re_le_of_gdSeries_eq_widthZeta`).
-/

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open GaloisForLFunctions.HTGeometry ArithmeticFunction

/-! ### The gap method with a growing bound -/

/-- **From `x^θ`-gap degrees to every large scale**, with the degree below the scale. -/
theorem exists_orbitCorr_sub_powGap_le' {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ} (hD : PowGaps θ D) :
    ∃ C T : ℝ, 0 ≤ C ∧ 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∃ d ∈ D, (d : ℝ) ≤ Real.exp t ∧
      |zetaScalingDatum.orbitCorr splineCycle t -
        zetaScalingDatum.orbitCorr splineCycle (Real.log d)| ≤ C * Real.exp ((θ - 1 / 2) * t) := by
  obtain ⟨hpos, M, X, hM0, hgapD⟩ := hD
  set x := splineCycle
  have hf : (x.2.2 : ℝ → ℝ) ∈ realTests := x.2.2.2
  obtain ⟨w, hw0, hw⟩ := SquareRootThreshold.exists_radius_of_hasCompactSupport
    (cx_hasCompactSupport hf.2)
  have hbs : ∀ u, cx x.2.2 u ≠ 0 → |u| ≤ w := fun u hu => by
    by_contra hc; exact hu (hw u (not_le.mp hc))
  set L := ∑' z : ℂ, ‖lagCoeff Zeta23.zetaZeroConfig (cx x.2.2) z‖ * ‖z‖
  have hL0 : 0 ≤ L := tsum_nonneg fun _ => by positivity
  set c := zetaScalingDatum.orbitCorr x with hc
  set T₀ : ℝ := max (max (Real.log (max X 1)) (Real.log (2 * M + 1) / (1 - θ))) 0 with hT₀
  refine ⟨2 * L * M, T₀, by positivity, le_max_right _ _, fun t ht => ?_⟩
  have hX : X ≤ Real.exp t := by
    have h1 : Real.log (max X 1) ≤ t := ((le_max_left _ _).trans (le_max_left _ _)).trans ht
    calc X ≤ max X 1 := le_max_left _ _
      _ = Real.exp (Real.log (max X 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr h1
  have hsmall : 2 * M * Real.exp (θ * t) ≤ Real.exp t := by
    have h1 : Real.log (2 * M + 1) ≤ (1 - θ) * t := by
      have := ((le_max_right _ _).trans (le_max_left _ _)).trans ht
      rw [div_le_iff₀ (by linarith)] at this
      linarith
    have h2 : 2 * M + 1 ≤ Real.exp ((1 - θ) * t) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 * M + 1)]
      exact Real.exp_le_exp.mpr h1
    have he : Real.exp ((1 - θ) * t) * Real.exp (θ * t) = Real.exp t := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (θ * t)]
  obtain ⟨d, hdD, hdle, hdgap⟩ := hgapD (Real.exp t) hX
  rw [← Real.exp_mul, mul_comm t θ] at hdgap
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hpos d hdD
  have hhalf : Real.exp t ≤ 2 * d := by linarith
  have hlogd : Real.log d ≤ t := by
    rw [← Real.log_exp t]; exact Real.log_le_log hd0 hdle
  have hs0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hpos d hdD)
  have hlip := norm_lagStructure_sub_le SquareRootThreshold.temperedConfig_zetaZeroConfig
    (cx_contDiff hf.1) hw0 hbs hs0 hlogd
  have hdiff : |c t - c (Real.log d)| ≤ L * (t - Real.log d) * Real.exp (t / 2) := by
    rw [hc, orbitCorr_eq_re_lagStructure, orbitCorr_eq_re_lagStructure, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans hlip
  have hg := log_gap_mul_le hM0 hd0 hdgap hhalf
  refine ⟨d, hdD, hdle, ?_⟩
  calc |c t - c (Real.log d)| ≤ L * ((t - Real.log d) * Real.exp (t / 2)) := by
        rw [← mul_assoc]; exact hdiff
    _ ≤ L * (2 * M * Real.exp ((θ - 1 / 2) * t)) := mul_le_mul_of_nonneg_left hg hL0
    _ = 2 * L * M * Real.exp ((θ - 1 / 2) * t) := by ring

/-- **The gap method with a growing bound.** A lower bound `−K d^a` at degrees with gaps `x^θ`
puts every zero in `Re ρ ≤ ½ + max(a, θ − ½)`. -/
theorem re_le_of_bddBelow_exp_of_powGaps {θ a : ℝ} (hθ1 : θ < 1) (ha0 : 0 ≤ a)
    (ha : a < 1 / 2) {D : Set ℕ} (hD : PowGaps θ D) {K : ℝ}
    (hK : ∀ d ∈ D, -(K * (d : ℝ) ^ a) ≤ zetaScalingDatum.orbitCorr splineCycle (Real.log d)) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + max a (θ - 1 / 2) := by
  obtain ⟨C, T, hC0, hT0, hCT⟩ := exists_orbitCorr_sub_powGap_le' hθ1 hD
  set b := max a (θ - 1 / 2) with hb
  have hb0 : 0 ≤ b := le_max_of_le_left ha0
  have hb1 : b < 1 / 2 := max_lt ha (by linarith)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_zetaOrbitCorr' splineCycle).continuousOn
  have hall : ∀ u : ℝ, 0 ≤ u →
      -((2 * (|K| + C + |B|)) * Real.exp (b * u)) ≤
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re := by
    intro u hu
    rw [← orbitCorr_eq_re_lagStructure_spline]
    have he1 : 1 ≤ Real.exp (b * u) := Real.one_le_exp (mul_nonneg hb0 hu)
    have hE0 : 0 ≤ Real.exp (b * u) := (Real.exp_pos _).le
    have hea : Real.exp (a * u) ≤ Real.exp (b * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)
    have heθ : Real.exp ((θ - 1 / 2) * u) ≤ Real.exp (b * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hu)
    rcases le_total u T with huT | hTu
    · have h := hB u ⟨hu, huT⟩
      rw [Real.norm_eq_abs] at h
      have h1 := (abs_le.mp (h.trans (le_abs_self B))).1
      have h2 := mul_le_mul_of_nonneg_left he1 (by positivity : (0 : ℝ) ≤ |K| + C + |B|)
      linarith [abs_nonneg K]
    · obtain ⟨d, hdD, hdle, hd⟩ := hCT u hTu
      have h1 := hK d hdD
      have h2 := (abs_le.mp hd).1
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hD.1 d hdD
      have hda : (d : ℝ) ^ a ≤ Real.exp (a * u) := by
        calc (d : ℝ) ^ a ≤ (Real.exp u) ^ a := Real.rpow_le_rpow hd0.le hdle ha0
          _ = Real.exp (a * u) := by rw [← Real.exp_mul, mul_comm]
      have hdpos : 0 ≤ (d : ℝ) ^ a := Real.rpow_nonneg hd0.le a
      have h3 : -(|K| * (d : ℝ) ^ a) ≤ -(K * (d : ℝ) ^ a) :=
        neg_le_neg (mul_le_mul_of_nonneg_right (le_abs_self K) hdpos)
      have h4 : |K| * (d : ℝ) ^ a ≤ |K| * Real.exp (b * u) :=
        mul_le_mul_of_nonneg_left (hda.trans hea) (abs_nonneg K)
      have h5 : C * Real.exp ((θ - 1 / 2) * u) ≤ C * Real.exp (b * u) :=
        mul_le_mul_of_nonneg_left heθ hC0
      have h6 := mul_nonneg (abs_nonneg B) hE0
      linarith
  intro ρ hρ
  by_contra hre
  push Not at hre
  exact evenCoeff_spline_sees hρ (by linarith)
    (evenCoeff_eq_zero_of_two_re_lagStructure_ge zetaZeroConfig
      SquareRootThreshold.temperedConfig_zetaZeroConfig (contDiff_boxSpline one_pos 2)
      (boxSpline_support one_pos 3) hb0 hb1
      (fun x hx him => absurd him (evenCoeff_spline_real hx)) hall
      (by simp; linarith))

/-! ### `ζ'/ζ` in a zero-free half-plane -/

theorem riemannZeta_ne_zero_of_re_gt {β₀ : ℝ} (hβ0 : 0 ≤ β₀)
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ β₀) {w : ℂ} (hw : β₀ < w.re) :
    riemannZeta w ≠ 0 := by
  intro h
  rcases le_or_gt 1 w.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1 h
  · have hmem : w ∈ zetaZeroConfig.carrier := ⟨h, by linarith, h1⟩
    linarith [hzf w hmem]

/-- If every zero has `Re ρ ≤ β₀`, then `|ζ'/ζ(w)| ≤ C |Im w|` for `β₀ + δ ≤ Re w ≤ 2`,
`|Im w| ≥ 4`. -/
theorem exists_norm_logDeriv_zeta_le_of_re_le' {β₀ δ : ℝ} (hβ : 1 / 2 ≤ β₀ + δ) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ β₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, β₀ + δ ≤ w.re → w.re ≤ 2 → 4 ≤ |w.im| →
      ‖logDeriv riemannZeta w‖ ≤ C * |w.im| := by
  have hC : 0 ≤ RHTower.logDerivZetaConstant := by
    unfold RHTower.logDerivZetaConstant; positivity
  have hup : ∀ v : ℂ, β₀ + δ ≤ v.re → v.re ≤ 2 → 4 ≤ v.im →
      ‖logDeriv riemannZeta v‖ ≤ RHTower.logDerivZetaConstant / δ * v.im := by
    intro v hv1 hv2 hv4
    have hall : ∀ q : RHTower.XiZeroCopy, δ ≤ ‖((v.re : ℂ) + v.im * I) - (q.1 : ℂ)‖ := by
      intro q
      have hq := hzf _ (RHTower.xiZeroCopy_mem_carrier q)
      calc δ ≤ (((v.re : ℂ) + v.im * I) - (q.1 : ℂ)).re := by simp; linarith
        _ ≤ ‖((v.re : ℂ) + v.im * I) - (q.1 : ℂ)‖ := Complex.re_le_norm _
    have h := RHTower.norm_logDeriv_zeta_le (by linarith) hv2 hv4 hδ0 hδ1 hall
    rw [Complex.re_add_im] at h
    have hlog : Real.log v.im ≤ v.im :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    calc ‖logDeriv riemannZeta v‖ ≤ RHTower.logDerivZetaConstant * Real.log v.im / δ := h
      _ = RHTower.logDerivZetaConstant / δ * Real.log v.im := by ring
      _ ≤ RHTower.logDerivZetaConstant / δ * v.im :=
          mul_le_mul_of_nonneg_left hlog (div_nonneg hC hδ0.le)
  refine ⟨RHTower.logDerivZetaConstant / δ, div_nonneg hC hδ0.le, fun w h1 h2 h4 => ?_⟩
  rcases le_or_gt 0 w.im with him | him
  · rw [abs_of_nonneg him] at h4 ⊢; exact hup w h1 h2 h4
  · rw [abs_of_neg him] at h4 ⊢
    have := hup (conj w) (by simpa using h1) (by simpa using h2) (by simpa using h4)
    rwa [logDeriv_riemannZeta_starRingEnd, Complex.norm_conj, Complex.conj_im] at this

/-! ### The shifted trace log-derivative -/

/-- `Σ_z c_z ζ'/ζ(s + a − z)`. -/
def shiftLogDerivOf (a : ℝ) (c : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑' z : ℂ, c z * logDeriv riemannZeta (s + a - z)

/-- **Continuation of `Σ_z c_z ζ'/ζ(s + a − z)`** to `1 < Re s < 2 − a − b` off the poles `1 − a + z`,
when every zero has `Re ρ ≤ ½ + b` with `2b < ½ + a`. -/
theorem differentiableAt_shiftLogDerivOf {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hδ : 2 * b < 1 / 2 + a) (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b)
    {c : ℂ → ℂ} (hc : ∀ z, ‖c z‖ ≤ ‖traceCoeff 3 z‖)
    {s₀ : ℂ} (hs1 : 1 < s₀.re) (hs2 : s₀.re < 2 - a - b)
    (hpole : ∀ z, c z ≠ 0 → s₀ ≠ 1 - a + z) :
    DifferentiableAt ℂ (shiftLogDerivOf a c) s₀ := by
  classical
  set δ₀ := min (1 / 2 + a - 2 * b) 1 with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by linarith) one_pos
  have hδ₀1 : δ₀ ≤ 1 := min_le_right _ _
  have hδ₀a : δ₀ ≤ 1 / 2 + a - 2 * b := min_le_left _ _
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_zeta_le_of_re_le' (β₀ := 1 / 2 + b)
    (by linarith) hδ₀0 hδ₀1 hzf
  have hsupp : ∀ z, c z ≠ 0 → traceCoeff 3 z ≠ 0 := fun z hz h =>
    hz (norm_eq_zero.mp (le_antisymm ((hc z).trans (by rw [h, norm_zero])) (norm_nonneg _)))
  have hre : ∀ z, c z ≠ 0 → |z.re| ≤ b := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf (hsupp z hz)
  -- the poles near the horizontal line of `s₀`
  set F : Set ℂ := {z | c z ≠ 0 ∧ |z.im - s₀.im| ≤ 5} with hFdef
  have hF : F.Finite := by
    refine (finite_traceCoeff_height 3 (|s₀.im| + 5)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hsupp z hz0, ?_⟩
    have h1 := abs_le.mp hzim
    rw [abs_le]; constructor <;> linarith [neg_abs_le s₀.im, le_abs_self s₀.im]
  obtain ⟨δ, hδ0, hδ1, hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ F, δ ≤ ‖s₀ - (1 - a + z)‖ := by
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · exact ⟨1, one_pos, le_rfl, by simp [hFe]⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hF.toFinset.exists_min_image (fun z => ‖s₀ - (1 - a + z)‖)
        (by simpa using hFne)
      have hz₁' := hF.mem_toFinset.mp hz₁
      refine ⟨min 1 ‖s₀ - (1 - a + z₁)‖,
        lt_min one_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hpole z₁ hz₁'.1))),
        min_le_left _ _, fun z hz => (min_le_right _ _).trans (hmin z (hF.mem_toFinset.mpr hz))⟩
  set ε := min (δ / 2) (min ((s₀.re - 1) / 2) ((2 - a - b - s₀.re) / 2)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hε1 : ε ≤ (s₀.re - 1) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ (2 - a - b - s₀.re) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  -- on the closed ball every argument `s + a − z` lies right of the zeros, left of `2`, off `1`
  have hstrip : ∀ z, c z ≠ 0 → ∀ s ∈ Metric.closedBall s₀ ε,
      1 / 2 + b + δ₀ ≤ (s + a - z).re ∧ (s + a - z).re ≤ 2 := by
    intro z hz s hs
    have hs' : ‖s - s₀‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs
    have hre' : |s.re - s₀.re| ≤ ε := (Complex.abs_re_le_norm (s - s₀)).trans (by simpa using hs')
    have h1 := abs_le.mp hre'
    have h2 := abs_le.mp (hre z hz)
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
    constructor <;> linarith
  have hfar : ∀ z, c z ≠ 0 → ∀ s ∈ Metric.closedBall s₀ ε, s + a - z ≠ 1 := by
    intro z hz s hs h
    have hs' : ‖s - s₀‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs
    by_cases hzF : z ∈ F
    · have h1 := hδF z hzF
      have h2 : s₀ - (1 - a + z) = s₀ - s := by linear_combination h
      rw [h2, norm_sub_rev] at h1
      linarith
    · have him : s.im = z.im := by
        have := congrArg Complex.im h
        simp at this; linarith
      have h3 : |s.im - s₀.im| ≤ ε := (Complex.abs_im_le_norm (s - s₀)).trans (by simpa using hs')
      apply hzF
      refine ⟨hz, ?_⟩
      rw [← him]
      linarith
  have hζne : ∀ z, c z ≠ 0 → ∀ s ∈ Metric.closedBall s₀ ε, riemannZeta (s + a - z) ≠ 0 :=
    fun z hz s hs => riemannZeta_ne_zero_of_re_gt (by linarith) hzf
      (by linarith [(hstrip z hz s hs).1])
  -- bounds for the finitely many nearby terms
  have hM : ∀ z ∈ F, ∃ M : ℝ, ∀ s ∈ Metric.closedBall s₀ ε,
      ‖logDeriv riemannZeta (s + a - z)‖ ≤ M := by
    intro z hz
    have hcont : ContinuousOn (fun s => logDeriv riemannZeta (s + a - z))
        (Metric.closedBall s₀ ε) := by
      intro s hs
      have hd : DifferentiableAt ℂ (fun s => logDeriv riemannZeta (s + a - z)) s :=
        (differentiableAt_logDeriv_riemannZeta (hfar z hz.1 s hs) (hζne z hz.1 s hs)).comp s
          ((differentiableAt_id.add_const _).sub_const _)
      exact hd.continuousAt.continuousWithinAt
    obtain ⟨M, hM⟩ := (isCompact_closedBall s₀ ε).exists_bound_of_continuousOn hcont
    exact ⟨M, hM⟩
  choose! M hMb using hM
  set K₀ : ℝ := |s₀.im| + 2 with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  set u : ℂ → ℝ := fun z => ‖c z‖ * (C * K₀ * (1 + |z.im|)) +
    (if z ∈ F then ‖c z‖ * |M z| else 0) with hu
  have hus : Summable u := by
    refine Summable.add ?_ ?_
    · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_)
        ((summable_traceCoeff_mul_pow (N := 1) (le_refl 3) (by norm_num)).mul_left (C * K₀))
      calc ‖c z‖ * (C * K₀ * (1 + |z.im|))
          ≤ ‖traceCoeff 3 z‖ * (C * K₀ * (1 + |z.im|)) :=
            mul_le_mul_of_nonneg_right (hc z) (by positivity)
        _ = C * K₀ * (‖traceCoeff 3 z‖ * (1 + |z.im|) ^ 1) := by ring
    · exact summable_of_ne_finset_zero (s := hF.toFinset) fun z hz => by
        rw [Set.Finite.mem_toFinset] at hz; simp [hz]
  have hdiff : DifferentiableOn ℂ (shiftLogDerivOf a c) (Metric.ball s₀ ε) := by
    unfold shiftLogDerivOf
    refine differentiableOn_tsum_of_summable_norm hus (fun z => ?_) Metric.isOpen_ball
      (fun z s hs => ?_)
    · by_cases hz : c z = 0
      · simp only [hz, zero_mul]; exact differentiableOn_const _
      · intro s hs
        have hs' := Metric.ball_subset_closedBall hs
        exact ((differentiableAt_logDeriv_riemannZeta (hfar z hz s hs') (hζne z hz s hs')).comp s
          ((differentiableAt_id.add_const _).sub (differentiableAt_const _))).const_mul _
          |>.differentiableWithinAt
    · have hs' := Metric.ball_subset_closedBall hs
      have hsn : ‖s - s₀‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs'
      by_cases hz : c z = 0
      · simp only [hz, zero_mul, norm_zero]
        exact add_nonneg (by positivity) (by split_ifs <;> positivity)
      by_cases hzF : z ∈ F
      · have h1 := hMb z hzF s hs'
        simp only [hu, if_pos hzF, norm_mul]
        have : ‖c z‖ * ‖logDeriv riemannZeta (s + a - z)‖ ≤ ‖c z‖ * |M z| :=
          mul_le_mul_of_nonneg_left (h1.trans (le_abs_self _)) (norm_nonneg _)
        have h0 : 0 ≤ ‖c z‖ * (C * K₀ * (1 + |z.im|)) := by positivity
        linarith
      · have hzF' : 5 < |z.im - s₀.im| := by
          by_contra h; exact hzF ⟨hz, not_lt.mp h⟩
        have hst := hstrip z hz s hs'
        set w := s + a - z with hw
        have hwim : w.im = s.im - z.im := by simp [hw]
        have him : |s.im - s₀.im| ≤ ε :=
          (Complex.abs_im_le_norm (s - s₀)).trans (by simpa using hsn)
        have ht : 4 ≤ |w.im| := by
          rw [hwim]
          have := abs_le.mp him
          rcases le_or_gt 0 (z.im - s₀.im) with h | h
          · rw [abs_of_nonneg h] at hzF'
            rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_neg h] at hzF'
            rw [abs_of_pos (by linarith)]; linarith
        have hbound := hC w hst.1 hst.2 ht
        have hwle : |w.im| ≤ K₀ * (1 + |z.im|) := by
          rw [hwim]
          have hs_im : |s.im| ≤ |s₀.im| + ε := by
            calc |s.im| = |(s.im - s₀.im) + s₀.im| := by ring_nf
              _ ≤ |s.im - s₀.im| + |s₀.im| := abs_add_le _ _
              _ ≤ |s₀.im| + ε := by linarith
          calc |s.im - z.im| ≤ |s.im| + |z.im| := abs_sub _ _
            _ ≤ K₀ * (1 + |z.im|) := by
                rw [hK₀]; nlinarith [abs_nonneg z.im, abs_nonneg s₀.im]
        simp only [hu, if_neg hzF, add_zero, norm_mul]
        calc ‖c z‖ * ‖logDeriv riemannZeta w‖ ≤ ‖c z‖ * (C * |w.im|) :=
              mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
          _ ≤ ‖c z‖ * (C * (K₀ * (1 + |z.im|))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwle hC0) (norm_nonneg _)
          _ = ‖c z‖ * (C * K₀ * (1 + |z.im|)) := by ring
  exact hdiff.differentiableAt (Metric.ball_mem_nhds _ hε0)

/-- **Pointwise convergence** of `Σ_z c_z ζ'/ζ(s + a − z)` for `1 < Re s < 2 − a − b`. -/
theorem summable_shiftLogDerivOf_terms {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hδ : 2 * b < 1 / 2 + a) (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b)
    {c : ℂ → ℂ} (hc : ∀ z, ‖c z‖ ≤ ‖traceCoeff 3 z‖)
    {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 2 - a - b) :
    Summable fun z => c z * logDeriv riemannZeta (s + a - z) := by
  classical
  set δ₀ := min (1 / 2 + a - 2 * b) 1 with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by linarith) one_pos
  have hδ₀a : δ₀ ≤ 1 / 2 + a - 2 * b := min_le_left _ _
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_zeta_le_of_re_le' (β₀ := 1 / 2 + b)
    (by linarith) hδ₀0 (min_le_right _ _) hzf
  have hsupp : ∀ z, c z ≠ 0 → traceCoeff 3 z ≠ 0 := fun z hz h =>
    hz (norm_eq_zero.mp (le_antisymm ((hc z).trans (by rw [h, norm_zero])) (norm_nonneg _)))
  set F : Set ℂ := {z | c z ≠ 0 ∧ |z.im - s.im| < 4} with hFdef
  have hF : F.Finite := by
    refine (finite_traceCoeff_height 3 (|s.im| + 4)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hsupp z hz0, ?_⟩
    have := abs_le.mp hzim.le
    rw [abs_le]; constructor <;> linarith [neg_abs_le s.im, le_abs_self s.im]
  set K₀ : ℝ := |s.im| + 1 with hK₀
  set u : ℂ → ℝ := fun z => ‖c z‖ * (C * K₀ * (1 + |z.im|)) +
    (if z ∈ F then ‖c z * logDeriv riemannZeta (s + a - z)‖ else 0) with hu
  have hus : Summable u := by
    refine Summable.add ?_ ?_
    · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_)
        ((summable_traceCoeff_mul_pow (N := 1) (le_refl 3) (by norm_num)).mul_left (C * K₀))
      calc ‖c z‖ * (C * K₀ * (1 + |z.im|))
          ≤ ‖traceCoeff 3 z‖ * (C * K₀ * (1 + |z.im|)) :=
            mul_le_mul_of_nonneg_right (hc z) (by positivity)
        _ = C * K₀ * (‖traceCoeff 3 z‖ * (1 + |z.im|) ^ 1) := by ring
    · exact summable_of_ne_finset_zero (s := hF.toFinset) fun z hz => by
        rw [Set.Finite.mem_toFinset] at hz; simp [hz]
  refine Summable.of_norm_bounded hus fun z => ?_
  by_cases hz : c z = 0
  · simp only [hz, zero_mul, norm_zero]
    exact add_nonneg (by positivity) (by split_ifs <;> positivity)
  by_cases hzF : z ∈ F
  · simp only [hu, if_pos hzF]
    have h0 : 0 ≤ ‖c z‖ * (C * K₀ * (1 + |z.im|)) := by positivity
    linarith
  have hzF' : 4 ≤ |z.im - s.im| := by
    by_contra h; exact hzF ⟨hz, not_le.mp h⟩
  have hre := abs_le.mp (abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf (hsupp z hz))
  set w := s + a - z with hw
  have hwim : w.im = s.im - z.im := by simp [hw]
  have hwre : w.re = s.re + a - z.re := by simp [hw]
  have ht : 4 ≤ |w.im| := by rw [hwim, abs_sub_comm]; exact hzF'
  have hbound := hC w (by rw [hwre]; linarith) (by rw [hwre]; linarith) ht
  have hwle : |w.im| ≤ K₀ * (1 + |z.im|) := by
    rw [hwim]
    calc |s.im - z.im| ≤ |s.im| + |z.im| := abs_sub _ _
      _ ≤ K₀ * (1 + |z.im|) := by rw [hK₀]; nlinarith [abs_nonneg z.im, abs_nonneg s.im]
  simp only [hu, if_neg hzF, add_zero, norm_mul]
  calc ‖c z‖ * ‖logDeriv riemannZeta w‖ ≤ ‖c z‖ * (C * |w.im|) :=
        mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ ≤ ‖c z‖ * (C * (K₀ * (1 + |z.im|))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwle hC0) (norm_nonneg _)
    _ = ‖c z‖ * (C * K₀ * (1 + |z.im|)) := by ring

/-! ### The weighted von Mangoldt series -/

/-- The coefficients `Λ(n)(2 Re S(log n) n^{−a} + K + 1)` at `n = j + 1`. -/
def widthCoeff (a K : ℝ) (j : ℕ) : ℝ :=
  Λ (j + 1) * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re *
    ((j : ℝ) + 1) ^ (-a) + K + 1)

/-- The candidate continuation `−Σ_z e_z ζ'/ζ(s + a − z) − (K + 1) ζ'/ζ(s)`. -/
def widthZeta (a K : ℝ) (s : ℂ) : ℂ :=
  -shiftLogDerivOf a (traceCoeff 3) s - ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s

theorem ofReal_add_one_rpow (j : ℕ) (a : ℝ) :
    ((((j : ℝ) + 1) ^ a : ℝ) : ℂ) = ((j : ℂ) + 1) ^ (a : ℂ) := by
  rw [Complex.ofReal_cpow (by positivity)]; push_cast; ring_nf

/-- **The weighted traces at the prime powers have the Dirichlet series
`−Σ_z e_z ζ'/ζ(s + a − z) − (K + 1)ζ'/ζ(s)`.** -/
theorem gdSeries_widthCoeff_eq {a b : ℝ} (hab : a ≤ b)
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b) (K : ℝ) {s : ℂ}
    (hs : 1 + (b - a) < s.re) :
    gdSeries (widthCoeff a K) powerFreq s = widthZeta a K s := by
  have hb := contDiff_boxSpline_two (le_refl 3)
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  set e := traceCoeff 3 with he
  have hE : Summable fun z => ‖e z‖ := by
    have h0 := (two_re_lagStructure_eq zetaZeroConfig hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hw : ∀ z, e z ≠ 0 → |z.re| ≤ b := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf hz
  set σ' := s.re + a - b with hσ'
  have hσ'1 : 1 < σ' := by rw [hσ']; linarith
  have hΛ : Summable fun j : ℕ => Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ') := by
    have h := (summable_tsum_vonMangoldt (w := (σ' : ℂ)) (by simpa using hσ'1)).1.norm
    refine h.congr fun j => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      norm_natCast_add_one_cpow]
    simp
  set f : ℕ → ℂ → ℂ := fun j z =>
    (Λ (j + 1) : ℂ) * (e z * ((j : ℂ) + 1) ^ (-(s + a - z))) with hf
  have hfn : ∀ j z, ‖f j z‖ ≤ Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ') * ‖e z‖ := by
    intro j z
    by_cases hz : e z = 0
    · simp [hf, hz]
    have hre := (abs_le.mp (hw z hz)).2
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      norm_natCast_add_one_cpow]
    have hexp : ((j : ℝ) + 1) ^ (-(s + a - z)).re ≤ ((j : ℝ) + 1) ^ (-σ') := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j])
      simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re]
      rw [hσ']; linarith
    have hΛ0 := vonMangoldt_nonneg (n := j + 1)
    calc Λ (j + 1) * (‖e z‖ * ((j : ℝ) + 1) ^ (-(s + a - z)).re)
        ≤ Λ (j + 1) * (‖e z‖ * ((j : ℝ) + 1) ^ (-σ')) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)) hΛ0
      _ = _ := by ring
  have hprod : Summable fun p : ℕ × ℂ => Λ (p.1 + 1) * ((p.1 : ℝ) + 1) ^ (-σ') * ‖e p.2‖ :=
    hΛ.mul_of_nonneg hE (fun j => mul_nonneg vonMangoldt_nonneg (by positivity))
      (fun _ => norm_nonneg _)
  have hF : Summable (Function.uncurry f) := Summable.of_norm_bounded hprod fun p => hfn p.1 p.2
  have hFp : Summable fun j => ∑' z, f j z := hF.prod
  -- the fibres over `j`
  have hj : ∀ j : ℕ, ∑' z, f j z = (Λ (j + 1) : ℂ) *
      (((2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re : ℝ) : ℂ) *
        (((j : ℂ) + 1) ^ (-(a : ℂ)) * ((j : ℂ) + 1) ^ (-s))) := by
    intro j
    simp only [hf]
    rw [tsum_mul_left]
    congr 1
    rw [(two_re_lagStructure_eq zetaZeroConfig hZ hb hbs (Real.log (j + 1))).2, ← tsum_mul_right]
    refine tsum_congr fun z => ?_
    rw [natCast_add_one_cpow_eq, natCast_add_one_cpow_eq, natCast_add_one_cpow_eq, mul_assoc,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    ring
  -- the fibres over `z`
  have hz : ∀ z : ℂ, ∑' j, f j z = e z * (-logDeriv riemannZeta (s + a - z)) := by
    intro z
    by_cases hz0 : e z = 0
    · simp [hf, hz0]
    have hre := (abs_le.mp (hw z hz0)).2
    have hres : 1 < (s + a - z).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]; linarith
    obtain ⟨-, hsum⟩ := summable_tsum_vonMangoldt hres
    rw [← hsum, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hf]; ring
  obtain ⟨hKs, hKe⟩ := summable_tsum_vonMangoldt (w := s) (by linarith)
  have hterm : ∀ j : ℕ, ((widthCoeff a K j : ℝ) : ℂ) * Complex.exp (-(s * (powerFreq j : ℂ))) =
      ∑' z, f j z + ((K + 1 : ℝ) : ℂ) * ((Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-s)) := by
    intro j
    rw [hj, cexp_neg_mul_powerFreq, widthCoeff]
    have hw' := ofReal_add_one_rpow j (-a)
    push_cast at hw' ⊢
    rw [hw']
    ring
  unfold gdSeries widthZeta shiftLogDerivOf
  calc ∑' j : ℕ, ((widthCoeff a K j : ℝ) : ℂ) * Complex.exp (-(s * (powerFreq j : ℂ)))
      = ∑' j : ℕ, (∑' z, f j z + ((K + 1 : ℝ) : ℂ) * ((Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-s))) :=
        tsum_congr hterm
    _ = ∑' j : ℕ, ∑' z, f j z +
          ((K + 1 : ℝ) : ℂ) * ∑' j : ℕ, (Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-s) := by
        rw [hFp.tsum_add (hKs.mul_left _), tsum_mul_left]
    _ = ∑' z, ∑' j, f j z + ((K + 1 : ℝ) : ℂ) * (-logDeriv riemannZeta s) := by
        rw [← hF.tsum_comm, hKe]
    _ = ∑' z, e z * (-logDeriv riemannZeta (s + a - z)) +
          ((K + 1 : ℝ) : ℂ) * (-logDeriv riemannZeta s) := by
        rw [tsum_congr hz]
    _ = -∑' z, e z * logDeriv riemannZeta (s + a - z) -
          ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s := by
        simp only [mul_neg, tsum_neg]; ring

/-- The candidate continuation is holomorphic on a ball around every non-pole `s₀`,
`1 < Re s₀ < 2 − a − b`. -/
theorem exists_ball_differentiableOn_widthZeta {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hδ : 2 * b < 1 / 2 + a) (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b) (K : ℝ)
    {s₀ : ℂ} (hs1 : 1 < s₀.re) (hs2 : s₀.re < 2 - a - b)
    (hpole : ∀ z, traceCoeff 3 z ≠ 0 → s₀ ≠ 1 - a + z) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (widthZeta a K) (ball s₀ ρ) := by
  classical
  set P : Set ℂ := {z | traceCoeff 3 z ≠ 0 ∧ |z.im - s₀.im| ≤ 1} with hPdef
  have hP : P.Finite := by
    refine (finite_traceCoeff_height 3 (|s₀.im| + 1)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hz0, ?_⟩
    have := abs_le.mp hzim
    rw [abs_le]; constructor <;> linarith [neg_abs_le s₀.im, le_abs_self s₀.im]
  obtain ⟨δ, hδ0, hδ1, hδP⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ P, δ ≤ ‖s₀ - (1 - a + z)‖ := by
    rcases P.eq_empty_or_nonempty with hPe | hPne
    · exact ⟨1, one_pos, le_rfl, by simp [hPe]⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hP.toFinset.exists_min_image (fun z => ‖s₀ - (1 - a + z)‖)
        (by simpa using hPne)
      have hz₁' := hP.mem_toFinset.mp hz₁
      refine ⟨min 1 ‖s₀ - (1 - a + z₁)‖,
        lt_min one_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hpole z₁ hz₁'.1))),
        min_le_left _ _, fun z hz => (min_le_right _ _).trans (hmin z (hP.mem_toFinset.mpr hz))⟩
  set ρ := min δ (min (s₀.re - 1) (2 - a - b - s₀.re)) / 2 with hρdef
  have hρ0 : 0 < ρ := by
    rw [hρdef]; exact half_pos (lt_min hδ0 (lt_min (by linarith) (by linarith)))
  have hρδ : ρ < δ := by
    rw [hρdef]; have := min_le_left δ (min (s₀.re - 1) (2 - a - b - s₀.re)); linarith
  have hρ1 : ρ < s₀.re - 1 := by
    rw [hρdef]
    have := (min_le_right δ (min (s₀.re - 1) (2 - a - b - s₀.re))).trans (min_le_left _ _)
    linarith
  have hρ2 : ρ < 2 - a - b - s₀.re := by
    rw [hρdef]
    have := (min_le_right δ (min (s₀.re - 1) (2 - a - b - s₀.re))).trans (min_le_right _ _)
    linarith
  refine ⟨ρ, hρ0, fun s hs => ?_⟩
  rw [mem_ball, dist_eq_norm] at hs
  have hre : |s.re - s₀.re| < ρ :=
    lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀)) hs
  have him : |s.im - s₀.im| < ρ :=
    lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (s - s₀)) hs
  have hs1' : 1 < s.re := by linarith [(abs_lt.mp hre).1]
  have hs2' : s.re < 2 - a - b := by linarith [(abs_lt.mp hre).2]
  have hnp : ∀ z, traceCoeff 3 z ≠ 0 → s ≠ 1 - a + z := by
    intro z hz h
    have hzim : s.im = z.im := by have := congrArg Complex.im h; simp at this; linarith
    have hzP : z ∈ P := ⟨hz, by rw [← hzim]; linarith [abs_lt.mp him, hδ1, hρδ]⟩
    have h1 := hδP z hzP
    rw [← h, norm_sub_rev] at h1
    linarith
  have h1 := differentiableAt_shiftLogDerivOf ha0 hab hδ hzf (c := traceCoeff 3) (fun _ => le_rfl)
    hs1' hs2' hnp
  have hs1ne : s ≠ 1 := fun h => by rw [h] at hs1'; simp at hs1'
  have h2 := differentiableAt_logDeriv_riemannZeta hs1ne
    (riemannZeta_ne_zero_of_one_le_re hs1'.le)
  exact (h1.neg.sub (h2.const_mul _)).differentiableWithinAt

/-! ### The prime series and the higher prime powers -/

/-- The weighted coefficients at the primes. -/
def primeWidthCoeff (a K : ℝ) (j : ℕ) : ℝ :=
  primeWeight j * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re *
    ((j : ℝ) + 1) ^ (-a) + K + 1)

/-- The weighted coefficients at the higher prime powers. -/
def higherWidthCoeff (a K : ℝ) (j : ℕ) : ℝ :=
  higherWeight j * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re *
    ((j : ℝ) + 1) ^ (-a) + K + 1)

theorem primeWidthCoeff_add_higherWidthCoeff (a K : ℝ) (j : ℕ) :
    primeWidthCoeff a K j + higherWidthCoeff a K j = widthCoeff a K j := by
  unfold primeWidthCoeff higherWidthCoeff widthCoeff
  rw [← primeWeight_add_higherWeight]; ring

/-- `|2 Re S(log n) n^{−a} + K + 1| ≤ (E + |K| + 1) n^{b−a}` once every exponent has `|Re z| ≤ b`. -/
theorem abs_widthTrace_add_le {a b : ℝ} (hab : a ≤ b)
    (hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ b) (K : ℝ) (j : ℕ) :
    |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re *
        ((j : ℝ) + 1) ^ (-a) + K + 1| ≤
      ((∑' z : ℂ, ‖traceCoeff 3 z‖) + |K| + 1) * ((j : ℝ) + 1) ^ (b - a) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have habs := abs_two_re_lagStructure_le_of_width hw (Real.log_nonneg hj1)
  have hexp : Real.exp (b * Real.log ((j : ℝ) + 1)) = ((j : ℝ) + 1) ^ b := by
    rw [Real.rpow_def_of_pos hj0]; ring_nf
  rw [hexp] at habs
  have hpow : ((j : ℝ) + 1) ^ b * ((j : ℝ) + 1) ^ (-a) = ((j : ℝ) + 1) ^ (b - a) := by
    rw [← Real.rpow_add hj0]; ring_nf
  have hpa : 0 < ((j : ℝ) + 1) ^ (-a) := by positivity
  have hp1 : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ (b - a) := Real.one_le_rpow hj1 (by linarith)
  have hE0 : 0 ≤ ∑' z : ℂ, ‖traceCoeff 3 z‖ := tsum_nonneg fun _ => norm_nonneg _
  have h1 : |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re *
      ((j : ℝ) + 1) ^ (-a)| ≤ (∑' z : ℂ, ‖traceCoeff 3 z‖) * ((j : ℝ) + 1) ^ (b - a) := by
    rw [abs_mul, abs_of_pos hpa, ← hpow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right habs hpa.le
  have h2 := mul_le_mul_of_nonneg_left hp1 (by linarith [abs_nonneg K] : (0 : ℝ) ≤ |K| + 1)
  have h3 := abs_add_le (2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
    (Real.log ((j : ℝ) + 1))).re * ((j : ℝ) + 1) ^ (-a) + K) 1
  have h4 := abs_add_le (2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
    (Real.log ((j : ℝ) + 1))).re * ((j : ℝ) + 1) ^ (-a)) K
  rw [abs_one] at h3
  nlinarith

/-- A Dirichlet series with `|a_j| ≤ C Λ(j + 1)(j + 1)^e` converges absolutely for `Re s > 1 + e`. -/
theorem summable_gdTerm_of_abs_le' {a : ℕ → ℝ} {C e : ℝ}
    (ha : ∀ j, |a j| ≤ C * (Λ (j + 1) * ((j : ℝ) + 1) ^ e)) {s : ℂ} (hs : 1 + e < s.re) :
    Summable fun j : ℕ => ((a j : ℝ) : ℂ) * cexp (-(s * (powerFreq j : ℂ))) := by
  have hσ : 1 < s.re - e := by linarith
  have hΛ : Summable fun j : ℕ => Λ (j + 1) * ((j : ℝ) + 1) ^ (-(s.re - e)) := by
    have h := (summable_tsum_vonMangoldt (w := ((s.re - e : ℝ) : ℂ)) (by simpa using hσ)).1.norm
    refine h.congr fun j => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      norm_natCast_add_one_cpow]
    simp
  refine Summable.of_norm_bounded (hΛ.mul_left C) fun j => ?_
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, cexp_neg_mul_powerFreq,
    norm_natCast_add_one_cpow]
  have hre : (-s).re = -s.re := by simp
  rw [hre]
  have hp : 0 ≤ ((j : ℝ) + 1) ^ (-s.re) := by positivity
  calc |a j| * ((j : ℝ) + 1) ^ (-s.re)
      ≤ C * (Λ (j + 1) * ((j : ℝ) + 1) ^ e) * ((j : ℝ) + 1) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (ha j) hp
    _ = C * (Λ (j + 1) * (((j : ℝ) + 1) ^ e * ((j : ℝ) + 1) ^ (-s.re))) := by ring
    _ = C * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(s.re - e))) := by
        rw [← Real.rpow_add hj0]; congr 3; ring

/-- **The correction is holomorphic** on `Re s > ¾ + (b − a)/2`. -/
theorem differentiableOn_gdSeries_higherWidthCoeff {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hb : b < 1 / 2)
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b) (K : ℝ) :
    DifferentiableOn ℂ (gdSeries (higherWidthCoeff a K) powerFreq)
      {s | 3 / 4 + (b - a) / 2 < s.re} := by
  have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ b := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf hz
  set E := ∑' z : ℂ, ‖traceCoeff 3 z‖ with hE
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  set σ₀ := 3 / 4 - (b - a) / 2 with hσ₀
  have hsum := (summable_higherWeight (σ := σ₀) (by rw [hσ₀]; linarith)).mul_left (E + |K| + 1)
  unfold gdSeries
  refine differentiableOn_tsum_of_summable_norm hsum (fun j => ?_)
    (isOpen_lt continuous_const Complex.continuous_re) (fun j s hs => ?_)
  · exact ((differentiable_id.mul_const _).neg.cexp.const_mul _).differentiableOn
  · have hs' : 3 / 4 + (b - a) / 2 < s.re := hs
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, cexp_neg_mul_powerFreq,
      norm_natCast_add_one_cpow]
    have hre : (-s).re = -s.re := by simp
    rw [hre]
    have h1 : |higherWidthCoeff a K j| ≤
        higherWeight j * ((E + |K| + 1) * ((j : ℝ) + 1) ^ (b - a)) := by
      unfold higherWidthCoeff
      rw [abs_mul, abs_of_nonneg (higherWeight_nonneg j)]
      exact mul_le_mul_of_nonneg_left (abs_widthTrace_add_le hab hw K j) (higherWeight_nonneg j)
    have h2 : ((j : ℝ) + 1) ^ (-s.re) ≤ ((j : ℝ) + 1) ^ (-(3 / 4 + (b - a) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
    have hc0 : 0 ≤ higherWeight j * ((E + |K| + 1) * ((j : ℝ) + 1) ^ (b - a)) :=
      mul_nonneg (higherWeight_nonneg j) (mul_nonneg (by linarith [abs_nonneg K]) (by positivity))
    calc |higherWidthCoeff a K j| * ((j : ℝ) + 1) ^ (-s.re)
        ≤ higherWeight j * ((E + |K| + 1) * ((j : ℝ) + 1) ^ (b - a)) *
            ((j : ℝ) + 1) ^ (-(3 / 4 + (b - a) / 2)) :=
          mul_le_mul h1 h2 (by positivity) hc0
      _ = (E + |K| + 1) * (higherWeight j *
            (((j : ℝ) + 1) ^ (b - a) * ((j : ℝ) + 1) ^ (-(3 / 4 + (b - a) / 2)))) := by ring
      _ = (E + |K| + 1) * (higherWeight j * ((j : ℝ) + 1) ^ (-σ₀)) := by
          rw [← Real.rpow_add hj0, hσ₀]; congr 3; ring

/-! ### Landau with a holomorphic correction -/

/-- **The Landau argument for the weighted series.** Let every zero have `Re ρ ≤ ½ + b`,
`0 ≤ a ≤ b`, `2b < ½ + a`. Let `B ≥ 0`, `Σ B_j/(j + 1) = ∞`, convergent right of `1 + b − a`, have
Dirichlet series `widthZeta a K − N` there, with `N` holomorphic on `Re s > ¾ + (b − a)/2`. Then
every zero has `Re ρ ≤ ½ + a`. -/
theorem forall_re_le_of_gdSeries_eq_widthZeta {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hδ : 2 * b < 1 / 2 + a) (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b)
    {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j)
    (hdiv1 : ¬ Summable fun j : ℕ => B j * ((j : ℝ) + 1) ^ (-1 : ℝ))
    (hconv : ∀ σ : ℝ, 1 + (b - a) < σ → Summable fun j : ℕ => B j * ((j : ℝ) + 1) ^ (-σ))
    {N : ℂ → ℂ} (hN : DifferentiableOn ℂ N {s | 3 / 4 + (b - a) / 2 < s.re}) (K : ℝ)
    (heq : ∀ s : ℂ, 1 + (b - a) < s.re → gdSeries B powerFreq s = widthZeta a K s - N s) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + a := by
  classical
  intro ρ₁ hρ₁
  by_contra hρ₁re
  push Not at hρ₁re
  have hb1 : b < 1 / 2 := by linarith
  have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ b := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf hz
  set U : ℝ := 2 - a - b with hU
  set A₀ : ℝ := 1 + (b - a) with hA₀
  have hA₀U : A₀ < U := by rw [hA₀, hU]; linarith
  have hr₀ : 3 / 4 + (b - a) / 2 < 1 := by linarith
  have hlam : ∀ j, 0 ≤ powerFreq j := powerFreq_nonneg
  have htw : ∀ σ j, gdTwistTerm B powerFreq σ 0 j = B j * ((j : ℝ) + 1) ^ (-σ) := by
    intro σ j; rw [gdTwistTerm, pow_zero, mul_one, real_exp_neg_mul_powerFreq]
  have hsumHigh : ∀ σ : ℝ, A₀ < σ → Summable (gdTwistTerm B powerFreq σ 0) := fun σ hσ =>
    (hconv σ hσ).congr fun j => (htw σ j).symm
  have hdivLow : ∀ σ : ℝ, σ ≤ 1 → ¬ Summable (gdTwistTerm B powerFreq σ 0) := by
    intro σ hσ hs
    apply hdiv1
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hB j) (by positivity)) (fun j => ?_) hs
    rw [htw]
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)) (hB j)
  -- the abscissa
  set S : Set ℝ := {σ | Summable (gdTwistTerm B powerFreq σ 0)} with hSdef
  set S2 : ℝ := (A₀ + U) / 2 with hS2def
  have hS2 : S2 ∈ S := hsumHigh _ (by rw [hS2def]; linarith)
  have hSne : S.Nonempty := ⟨_, hS2⟩
  have hSbdd : BddBelow S := ⟨1, fun σ hσ => by
    by_contra h; exact hdivLow σ (le_of_lt (not_le.mp h)) hσ⟩
  set σc := sInf S with hσcdef
  have hsum : ∀ σ, σc < σ → Summable (gdTwistTerm B powerFreq σ 0) := by
    intro σ hσ
    obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hSne hσ
    exact summable_gdTwistTerm_of_le hB hlam hσ'S hlt.le
  have hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm B powerFreq σ 0) := fun σ hσ hs =>
    absurd (csInf_le hSbdd hs) (not_le.mpr hσ)
  have hσc2 : σc ≤ S2 := csInf_le hSbdd hS2
  -- analyticity
  have hgdAn : ∀ s : ℂ, σc < s.re → AnalyticAt ℂ (gdSeries B powerFreq) s := by
    intro s hs
    have hopen : IsOpen {w : ℂ | σc < w.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticAt (s := {w : ℂ | σc < w.re}) (fun w hw => ?_)
      (hopen.mem_nhds hs)
    have hw' : σc < w.re := hw
    exact (RHTower.differentiableAt_gdSeries hB hlam (hsum ((σc + w.re) / 2) (by linarith))
      (by linarith)).differentiableWithinAt
  have hNAn : ∀ s : ℂ, 3 / 4 + (b - a) / 2 < s.re → AnalyticAt ℂ N s := fun s hs =>
    hN.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  set G : ℂ → ℂ := fun s => widthZeta a K s - N s with hGdef
  have hGball : ∀ s₀ : ℂ, 1 < s₀.re → s₀.re < U →
      (∀ z, traceCoeff 3 z ≠ 0 → s₀ ≠ 1 - a + z) →
        ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ G (ball s₀ ρ) := by
    intro s₀ h1 h2 hp
    obtain ⟨ρ, hρ, hd⟩ := exists_ball_differentiableOn_widthZeta ha0 hab hδ hzf K h1 h2 hp
    refine ⟨min ρ (s₀.re - 1), lt_min hρ (by linarith), ?_⟩
    refine (hd.mono (ball_subset_ball (min_le_left _ _))).sub (hN.mono fun s hs => ?_)
    rw [mem_ball, dist_eq_norm] at hs
    have hre : |s.re - s₀.re| < s₀.re - 1 :=
      lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀))
        (hs.trans_le (min_le_right _ _))
    show 3 / 4 + (b - a) / 2 < s.re
    linarith [(abs_lt.mp hre).1]
  have hGAn : ∀ s : ℂ, 1 < s.re → s.re < U →
      (∀ z, traceCoeff 3 z ≠ 0 → s ≠ 1 - a + z) → AnalyticAt ℂ G s := by
    intro s h1 h2 hp
    obtain ⟨ρ, hρ, hd⟩ := hGball s h1 h2 hp
    exact hd.analyticAt (ball_mem_nhds s hρ)
  have hrealNoPole : ∀ t : ℝ, ∀ z, traceCoeff 3 z ≠ 0 → (t : ℂ) ≠ 1 - a + z := by
    intro t z hz h
    have him := congrArg Complex.im h
    simp only [Complex.ofReal_im, Complex.add_im, Complex.sub_im, Complex.one_im, zero_sub,
      neg_zero, zero_add] at him
    exact traceCoeff_im_ne_zero hz him.symm
  have hagreeHigh : ∀ s : ℂ, A₀ < s.re → gdSeries B powerFreq s = G s := heq
  -- Landau: the abscissa is at most `1`
  have hσc : σc ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have h2 : σc < U := by linarith
    obtain ⟨ρ, hρ, hG⟩ := hGball (σc : ℂ) (by simpa using hgt) (by simpa using h2)
      (fun z hz => hrealNoPole σc z hz)
    have hreal : ∀ t ∈ Ioo σc U,
        gdSeries B powerFreq ((0 : ℂ) + t) = G ((0 : ℂ) + t) := by
      refine eqOn_ray_of_eventually (a := σc) (c := (S2 + U) / 2) (b := U)
        (by linarith) (by linarith) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
      · rw [zero_add]; exact hgdAn _ (by simpa using ht.1)
      · rw [zero_add]
        exact hGAn _ (by simpa using hgt.trans ht.1) (by simpa using ht.2)
          (fun z hz => hrealNoPole t z hz)
      · rw [zero_add]; exact hagreeHigh _ (by simp; linarith [ht.1])
    have hhalf := eqOn_halfBall (f := G) (g := gdSeries B powerFreq) hρ
      (fun s hs _ => hG.analyticAt (isOpen_ball.mem_nhds hs))
      (fun s _ hs => hgdAn s hs)
      (fun t ht1 _ => by
        rcases lt_or_ge t U with htb | htb
        · have := hreal t ⟨ht1, htb⟩; rw [zero_add] at this; exact this.symm
        · exact (hagreeHigh _ (by simp; linarith)).symm)
    exact RHTower.gdSeries_no_continuation_at_abscissa hB hlam hsum hdiv hρ hG
      (fun s hs hre => hhalf s hs hre)
  -- the zero right of `½ + a`, rightmost on its line
  set z₁ := ρ₁ - 1 / 2 with hz₁def
  have hz₁ : traceCoeff 3 z₁ ≠ 0 := traceCoeff_sees (le_refl 3) hρ₁ (by linarith)
  set Lset := (finite_evenCoeff_line zetaZeroConfig (boxSpline 1 3) z₁.im).toFinset with hLset
  obtain ⟨z₀, hz₀L, hmax⟩ := Lset.exists_max_image Complex.re
    ⟨z₁, (Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩⟩
  obtain ⟨hz₀, him₀⟩ := (Set.Finite.mem_toFinset _).mp hz₀L
  have hre₀ : z₁.re ≤ z₀.re := hmax z₁ ((Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩)
  have hz₁re : a < z₁.re := by simp [hz₁def]; linarith
  have hz₀re : z₀.re ≤ b := (abs_le.mp (hw z₀ hz₀)).2
  set s₀ : ℂ := 1 - a + z₀ with hs₀def
  have hs₀re : s₀.re = 1 - a + z₀.re := by simp [hs₀def]
  have hs₀1 : 1 < s₀.re := by rw [hs₀re]; linarith
  have hs₀2 : s₀.re ≤ A₀ := by rw [hs₀re, hA₀]; linarith
  set T : ℝ := U - s₀.re with hTdef
  have hT : 0 < T := by rw [hTdef]; linarith
  have hqre : ∀ t : ℝ, (s₀ + t).re = s₀.re + t := fun t => by simp
  have hray : ∀ t : ℝ, 0 < t → ∀ z, traceCoeff 3 z ≠ 0 → s₀ + t ≠ 1 - a + z := by
    intro t ht z hz h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [hs₀def] at him hre
    have hle := hmax z ((Set.Finite.mem_toFinset _).mpr ⟨hz, him.symm.trans him₀⟩)
    linarith
  have hGray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ G (s₀ + t) := fun t ht =>
    hGAn _ (by rw [hqre]; linarith [ht.1]) (by rw [hqre]; linarith [ht.2]) (hray t ht.1)
  have hgdray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ (gdSeries B powerFreq) (s₀ + t) := fun t ht =>
    hgdAn _ (by rw [hqre]; linarith [ht.1])
  have hagreeRay : ∀ t ∈ Ioo 0 T, gdSeries B powerFreq (s₀ + t) = G (s₀ + t) :=
    eqOn_ray_of_eventually (c := (A₀ - s₀.re + T) / 2) (by linarith) (by linarith)
      hgdray hGray (fun t ht => hagreeHigh _ (by rw [hqre]; linarith [ht.1]))
  -- split off the pole
  set c' : ℂ → ℂ := fun z => if z = z₀ then 0 else traceCoeff 3 z with hc'def
  have hc' : ∀ z, ‖c' z‖ ≤ ‖traceCoeff 3 z‖ := fun z => by
    simp only [hc'def]; split_ifs <;> simp
  set R : ℂ → ℂ := fun s => -shiftLogDerivOf a c' s -
    ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s - N s with hRdef
  have hsplit : ∀ t ∈ Ioo 0 T,
      G (s₀ + t) = -(traceCoeff 3 z₀ * logDeriv riemannZeta (1 + t)) + R (s₀ + t) := by
    intro t ht
    have hsm := summable_shiftLogDerivOf_terms ha0 hab hδ hzf (c := traceCoeff 3)
      (fun _ => le_rfl) (s := s₀ + t) (by rw [hqre]; linarith [ht.1])
      (by rw [hqre]; linarith [ht.2])
    simp only [hGdef, hRdef]
    unfold widthZeta shiftLogDerivOf
    rw [hsm.tsum_eq_add_tsum_ite z₀]
    have h1 : (s₀ + t) + a - z₀ = 1 + t := by rw [hs₀def]; ring
    have h2 : ∑' z, (if z = z₀ then 0 else
          traceCoeff 3 z * logDeriv riemannZeta (s₀ + t + a - z)) =
        ∑' z, c' z * logDeriv riemannZeta (s₀ + t + a - z) :=
      tsum_congr fun z => by simp only [hc'def]; split_ifs <;> simp
    rw [h1, h2]
    ring
  have hs₀ne : s₀ ≠ 1 := fun h => by rw [h] at hs₀1; simp at hs₀1
  have hRcont : ContinuousAt R s₀ := by
    have hp : ∀ z, c' z ≠ 0 → s₀ ≠ 1 - a + z := by
      intro z hz h
      have hzz : z ≠ z₀ := fun e => hz (by simp [hc'def, e])
      exact hzz (by rw [hs₀def] at h; linear_combination -h)
    have h1 := differentiableAt_shiftLogDerivOf ha0 hab hδ hzf hc' hs₀1 (by linarith) hp
    have h2 := differentiableAt_logDeriv_riemannZeta hs₀ne
      (riemannZeta_ne_zero_of_one_le_re hs₀1.le)
    exact ((h1.neg.sub (h2.const_mul _)).continuousAt).sub
      (hNAn s₀ (by linarith)).continuousAt
  have hgdcont : ContinuousAt (gdSeries B powerFreq) s₀ := (hgdAn s₀ (by linarith)).continuousAt
  set H : ℂ → ℂ := fun s => gdSeries B powerFreq s - R s with hHdef
  have hHcont : ContinuousAt H s₀ := hgdcont.sub hRcont
  have hHray : ∀ t ∈ Ioo 0 T, H (s₀ + t) = -(traceCoeff 3 z₀ * logDeriv riemannZeta (1 + t)) := by
    intro t ht
    simp only [hHdef]
    rw [hagreeRay t ht, hsplit t ht]
    ring
  -- the pole of `ζ'/ζ` at `1` against continuity
  obtain ⟨δ₁, hδ₁, hδ₁H⟩ := Metric.continuousAt_iff.mp hHcont 1 one_pos
  set A := ‖traceCoeff 3 z₀‖ with hAdef
  have hA : 0 < A := norm_pos_iff.mpr hz₀
  obtain ⟨t, ht0, htδ, htB⟩ := exists_norm_logDeriv_zeta_one_add_gt ((‖H s₀‖ + 1) / A)
    (lt_min hδ₁ hT)
  have htδ₁ : t < δ₁ := htδ.trans_le (min_le_left _ _)
  have htT : t < T := htδ.trans_le (min_le_right _ _)
  have h1 := hHray t ⟨ht0, htT⟩
  have h2 : dist (H (s₀ + t)) (H s₀) < 1 := hδ₁H (by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact htδ₁)
  have h4 : ‖H s₀‖ + 1 < ‖H (s₀ + t)‖ := by
    rw [h1, norm_neg, norm_mul]
    rw [div_lt_iff₀ hA] at htB
    linarith
  have h5 : ‖H (s₀ + t)‖ < ‖H s₀‖ + 1 := by
    have := norm_sub_norm_le (H (s₀ + t)) (H s₀)
    rw [dist_eq_norm] at h2
    linarith
  linarith

/-! ### The theorem -/

/-- **The width is the Stepanov exponent at the primes.** For `0 ≤ a < ½`, every zero lies within
`a` of the critical line iff `2 Re S(log p) ≥ −K p^a` at every prime `p`. -/
theorem zetaZeroWidth_le_iff_bddBelow_primeDegrees {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    zetaZeroWidth ≤ a ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
      -(K * (p : ℝ) ^ a) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
  rw [zetaZeroWidth_le_iff_re_le ha0]
  constructor
  · intro hzf
    have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ a := fun z hz =>
      abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf hz
    refine ⟨∑' z : ℂ, ‖traceCoeff 3 z‖, fun p hp => ?_⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have habs := abs_two_re_lagStructure_le_of_width hw
      (Real.log_nonneg (by exact_mod_cast hp.one_lt.le : (1 : ℝ) ≤ p))
    have hexp : Real.exp (a * Real.log p) = (p : ℝ) ^ a := by
      rw [Real.rpow_def_of_pos hp0]; ring_nf
    rw [hexp] at habs
    linarith [(abs_le.mp habs).1]
  · rintro ⟨K, hK⟩
    set b := max a (1 / 8) with hbdef
    have hab : a ≤ b := le_max_left _ _
    have hb8 : 1 / 8 ≤ b := le_max_right _ _
    have hδ : 2 * b < 1 / 2 + a := by
      rcases le_total a (1 / 8) with h | h
      · rw [hbdef, max_eq_right h]; linarith
      · rw [hbdef, max_eq_left h]; linarith
    have hb1 : b < 1 / 2 := by linarith
    -- step 1: the zeros lie in `Re ρ ≤ ½ + b`
    have hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b := by
      have h := re_le_of_bddBelow_exp_of_powGaps (θ := 5 / 8) (by norm_num) ha0 ha
        (powGaps_primes (by norm_num) (by norm_num)) (K := K / 2) fun p hp => by
          have := hK p hp
          rw [orbitCorr_eq_re_lagStructure_spline]; linarith
      intro ρ hρ
      have := h ρ hρ
      rw [show (5 / 8 : ℝ) - 1 / 2 = 1 / 8 by norm_num] at this
      exact this
    have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ b := fun z hz =>
      abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf hz
    set E := ∑' z : ℂ, ‖traceCoeff 3 z‖ with hE
    -- step 2: the weighted prime series
    have hinner : ∀ j : ℕ, (j + 1).Prime → 1 ≤
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re *
          ((j : ℝ) + 1) ^ (-a) + K + 1 := by
      intro j hj
      have h1 := hK (j + 1) hj
      push_cast at h1
      have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hpa : 0 < ((j : ℝ) + 1) ^ (-a) := by positivity
      have hprod : ((j : ℝ) + 1) ^ a * ((j : ℝ) + 1) ^ (-a) = 1 := by
        rw [← Real.rpow_add hj0]; simp
      have h2 : -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
          (Real.log ((j : ℝ) + 1))).re * ((j : ℝ) + 1) ^ (-a) := by
        calc -K = -(K * ((j : ℝ) + 1) ^ a) * ((j : ℝ) + 1) ^ (-a) := by
              rw [neg_mul, mul_assoc, hprod, mul_one]
          _ ≤ _ := mul_le_mul_of_nonneg_right h1 hpa.le
      linarith
    have hge : ∀ j, primeWeight j ≤ primeWidthCoeff a K j := by
      intro j
      unfold primeWidthCoeff
      by_cases hj : (j + 1).Prime
      · have h0 : 0 ≤ primeWeight j := primeWeight_nonneg j
        have := mul_le_mul_of_nonneg_left (hinner j hj) h0
        linarith
      · simp [primeWeight, hj]
    have hBn : ∀ j, 0 ≤ primeWidthCoeff a K j := fun j => (primeWeight_nonneg j).trans (hge j)
    have hbound : ∀ (w : ℕ → ℝ), (∀ j, 0 ≤ w j) → (∀ j, w j ≤ Λ (j + 1)) → ∀ j,
        |w j * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re *
          ((j : ℝ) + 1) ^ (-a) + K + 1)| ≤
            (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (b - a)) := by
      intro w hw0 hwΛ j
      rw [abs_mul, abs_of_nonneg (hw0 j)]
      have h1 := abs_widthTrace_add_le hab hw K j
      calc w j * |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re *
            ((j : ℝ) + 1) ^ (-a) + K + 1| ≤
            Λ (j + 1) * ((E + |K| + 1) * ((j : ℝ) + 1) ^ (b - a)) :=
            mul_le_mul (hwΛ j) h1 (abs_nonneg _) vonMangoldt_nonneg
        _ = _ := by ring
    have hbP : ∀ j, |primeWidthCoeff a K j| ≤
        (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (b - a)) :=
      hbound primeWeight primeWeight_nonneg primeWeight_le
    have hbH : ∀ j, |higherWidthCoeff a K j| ≤
        (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (b - a)) :=
      hbound higherWeight higherWeight_nonneg higherWeight_le
    have hbA : ∀ j, |widthCoeff a K j| ≤
        (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (b - a)) :=
      hbound (fun j => Λ (j + 1)) (fun _ => vonMangoldt_nonneg) (fun _ => le_rfl)
    refine forall_re_le_of_gdSeries_eq_widthZeta ha0 hab hδ hzf hBn ?_ ?_
      (differentiableOn_gdSeries_higherWidthCoeff ha0 hab hb1 hzf K) K ?_
    · -- divergence at `σ = 1`
      intro hs
      apply not_summable_primeWeight_div
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (primeWeight_nonneg j) (by positivity))
        (fun j => mul_le_mul_of_nonneg_right (hge j) (by positivity)) hs
    · -- convergence right of `1 + b − a`
      intro σ hσ
      have h := summable_gdTerm_of_abs_le' hbP (s := (σ : ℂ)) (by simpa using hσ)
      refine h.norm.congr fun j => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hBn j),
        cexp_neg_mul_powerFreq, norm_natCast_add_one_cpow]
      simp
    · -- the prime series is the prime-power series minus the correction
      intro s hs
      have hA := summable_gdTerm_of_abs_le' hbA hs
      have hH := summable_gdTerm_of_abs_le' hbH hs
      rw [← gdSeries_widthCoeff_eq hab hzf K hs]
      unfold gdSeries
      rw [← hA.tsum_sub hH]
      refine tsum_congr fun j => ?_
      rw [← primeWidthCoeff_add_higherWidthCoeff a K j]
      push_cast
      ring

end GaloisForLFunctions.SurfaceOfSpecZ
