import GaloisForLFunctions.SurfaceOfSpecZ.CrudeHasseWeilAtTheIntegerDegrees
import GaloisForLFunctions.SquareRootThreshold.EveryWidthDecidesTheCriticalLine
import GaloisForLFunctions.SquareRootThreshold.DifferenceTwoBumpTestsDecideTheCriticalLine
import GaloisForLFunctions.RHTower.XiRealAnchorPositive
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# One side of Hasse–Weil at the integer degrees is RH

On `C × C` the defect `δ(Δ, Γ_{Fⁿ}) = a_n = qⁿ + 1 − N_n` is the trace, and Bombieri–Stepanov bound
only one side of it: `N_n ≤ qⁿ + O(q^{n/2})`, i.e. `a_n ≥ −C q^{n/2}`. Pringsheim's theorem for the
power series `Σ (C q^{n/2} + a_n) Tⁿ`, whose coefficients are nonnegative, then places every
Frobenius eigenvalue on `|α| = √q`.

For the smoothed Frobenius graphs of `Spec ℤ` the trace at degree `n` is `c_B(log n) = δ(Γ_1, Γ_n)`,
and either side of a crude bound suffices:

* `riemannHypothesis_iff_bddBelow_integerDegrees`: RH iff `c_B(log n) ≥ −K` for all `n ≥ 1`. This is
  the Bombieri–Stepanov side: an upper bound on the smoothed point counts.
* `riemannHypothesis_iff_bddAbove_integerDegrees`: RH iff `c_B(log n) ≤ K` for all `n ≥ 1`, a lower
  bound on the point counts.

**Mechanism.** The orbit correlation moves by at most `2L` between `log ⌊eᵗ⌋` and `t`
(`exists_orbitCorr_sub_floor_le`), so the bound holds at every scale. Pringsheim's theorem becomes
Landau's: `K ± c_B` is a nonnegative density whose Laplace transform continues past every real
point, since `ζ` has no real zeros in the strip (`evenCoeff_eq_zero_of_two_re_lagStructure_ge`, the
mirror of `evenCoeff_eq_zero_of_two_re_lagStructure_le_exp`). The upper side is the rate law
`re_le_iff_lag_twoBump_ge_neg_exp_of_pos` for the spline `U_1^{⋆4}`, whose transform vanishes at
no off-line spectral point.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-! ### The Landau core for a lower bound -/

/-- **No top pole from below.** If `2 Re S(u) ≥ −M e^{au}` for `u ≥ 0`, `0 ≤ a < ½`, and the real
exponents of `2 Re S` lie at most at `a`, then every exponent with `Re z > a` has coefficient zero. -/
theorem evenCoeff_eq_zero_of_two_re_lagStructure_ge (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hreal : ∀ x : ℂ, evenCoeff Z b x ≠ 0 → x.im = 0 → x.re ≤ a) {M : ℝ}
    (hMa : ∀ u : ℝ, 0 ≤ u → -(M * Real.exp (a * u)) ≤ 2 * (lagStructure Z b u).re)
    {z : ℂ} (hz : a < z.re) : evenCoeff Z b z = 0 := by
  classical
  by_contra hne
  set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
  haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
  -- the rightmost exponent on the line of `z`
  set L := (finite_evenCoeff_line Z b z.im).toFinset with hL
  obtain ⟨z₀, hz₀L, hmax⟩ := L.exists_max_image Complex.re
    ⟨z, (Set.Finite.mem_toFinset _).mpr ⟨hne, rfl⟩⟩
  obtain ⟨hz₀, him₀⟩ := (Set.Finite.mem_toFinset _).mp hz₀L
  have hre₀ : z.re ≤ z₀.re := hmax z ((Set.Finite.mem_toFinset _).mpr ⟨hne, rfl⟩)
  -- separation of the line of `z₀`
  obtain ⟨η₁, hη₁, hsep₁⟩ := exists_sep_height Z z₀.im
  obtain ⟨η₂, hη₂, hsep₂⟩ := exists_sep_height Z (-z₀.im)
  have hsep : ∀ t : ι, |(t : ℂ).im - z₀.im| < min η₁ η₂ → (t : ℂ).im = z₀.im := fun t ht => by
    rcases mem_of_evenCoeff_ne_zero t.2 with h | h
    · have := hsep₁ _ h (by simpa using ht.trans_le (min_le_left _ _))
      simpa using this
    · have := hsep₂ _ h (by
        rw [show (1 / 2 + conj (t : ℂ)).im - -z₀.im = -((t : ℂ).im - z₀.im) by simp; ring,
          abs_neg]
        exact ht.trans_le (min_le_right _ _))
      simp at this; linarith
  have hD0 : Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
    have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hD : Summable fun t : ι => ‖-evenCoeff Z b t‖ :=
    (hD0.subtype ι).congr fun t => by simp
  -- `φ = −2 Re S` as an exponential sum over `ι`
  set φ : ℝ → ℝ := fun u => -(2 * (lagStructure Z b u).re) with hφ
  have hφm : Measurable φ :=
    ((continuous_const.mul (Complex.continuous_re.comp
      (continuous_lagStructure Z hZ hb hbs))).neg).measurable
  have hφrep : ∀ u : ℝ, ((φ u : ℝ) : ℂ) = ∑' t : ι, -evenCoeff Z b t * cexp ((t : ℂ) * u) := by
    intro u
    have hsub : Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * u)) ⊆ ι :=
      fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * u) = 0 by rw [h0, zero_mul])
    simp_rw [neg_mul]
    rw [tsum_neg, tsum_subtype_eq_of_support_subset hsub,
      ← (two_re_lagStructure_eq Z hZ hb hbs u).2, hφ]
    push_cast
    ring
  -- the inputs of Landau's theorem
  set K := 2 * ∑' z : ℂ, ‖lagCoeff Z b z‖ with hK
  have hKb : ∀ u, 0 < u → |φ u| ≤ K * Real.exp (u / 2) := by
    intro u hu
    obtain ⟨hs, he⟩ := lagStructure_eq_tsum_lagCoeff Z hZ hb hbs u
    have hle : ‖lagStructure Z b u‖ ≤ (∑' z : ℂ, ‖lagCoeff Z b z‖) * Real.exp (u / 2) := by
      rw [he, ← tsum_mul_right]
      refine (norm_tsum_le_tsum_norm hs.norm).trans (Summable.tsum_le_tsum
        (fun z => norm_lagCoeff_mul_exp_le z (le_of_eq (abs_of_pos hu))) hs.norm
        ((summable_norm_lagCoeff Z hZ hb hbs).mul_right _))
    have := Complex.abs_re_le_norm (lagStructure Z b u)
    simp only [hφ, abs_neg, abs_mul, abs_two, hK]
    nlinarith
  have hMa' : ∀ u : ℝ, 0 ≤ u → φ u ≤ M * Real.exp (a * u) := fun u hu => by
    simp only [hφ]; linarith [hMa u hu]
  obtain ⟨η₀, hη₀, hnear⟩ := exists_im_eq_zero_of_evenCoeff Z b
  set Λ := resolventSum (fun t : ι => (t : ℂ)) fun t => -evenCoeff Z b t with hΛ
  have hΛan : ∀ t : ℝ, a < t → AnalyticAt ℂ Λ t := by
    intro t hat
    set r := min η₀ (t - a) / 2 with hr
    have hr0 : 0 < r := by rw [hr]; exact half_pos (lt_min hη₀ (by linarith))
    have hr1 : 2 * r ≤ η₀ := by rw [hr]; linarith [min_le_left η₀ (t - a)]
    have hr2 : 2 * r ≤ t - a := by rw [hr]; linarith [min_le_right η₀ (t - a)]
    have hgap : ∀ (x : ι) (s : ℂ), s ∈ Metric.ball (t : ℂ) r → r ≤ ‖s - (x : ℂ)‖ := by
      intro x s hs
      rw [Metric.mem_ball, Complex.dist_eq] at hs
      have h2 : |s.im| ≤ ‖s - t‖ := by
        have := Complex.abs_im_le_norm (s - t); simpa using this
      have h2' : |s.re - t| ≤ ‖s - t‖ := by
        have := Complex.abs_re_le_norm (s - t); simpa using this
      by_cases hx : |(x : ℂ).im| < η₀
      · have him := hnear _ x.2 hx
        have hre := hreal _ x.2 him
        have h3 : (s - (x : ℂ)).re ≤ ‖s - (x : ℂ)‖ := Complex.re_le_norm _
        rw [Complex.sub_re] at h3
        linarith [(abs_le.mp h2').1]
      · push Not at hx
        have h3 : |(s - (x : ℂ)).im| ≤ ‖s - (x : ℂ)‖ := Complex.abs_im_le_norm _
        have h4 : |(x : ℂ).im| ≤ |(s - (x : ℂ)).im| + |s.im| := by
          rw [Complex.sub_im]
          calc |(x : ℂ).im| = |-(s.im - (x : ℂ).im) + s.im| := by ring_nf
            _ ≤ |-(s.im - (x : ℂ).im)| + |s.im| := abs_add_le _ _
            _ = |s.im - (x : ℂ).im| + |s.im| := by rw [abs_neg]
        linarith
    have hdiff : DifferentiableOn ℂ Λ (Metric.ball (t : ℂ) r) := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun x => ‖-evenCoeff Z b x‖ / r) (hD.div_const _) (fun x => ?_)
        Metric.isOpen_ball (fun x s hs => ?_)
      · refine (differentiableOn_const _).div (differentiableOn_id.sub_const _) fun s hs h0 => ?_
        have := hgap x s hs
        rw [h0, norm_zero] at this
        linarith
      · rw [norm_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) hr0 (hgap x s hs)
    exact hdiff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0))
  have hΛφ : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ u in Ioi (0 : ℝ), ((φ u : ℝ) : ℂ) * cexp (-s * u) = Λ s := fun s hs => by
    simp_rw [hφrep]
    exact integral_tsum_exp_mul_exp_neg hD (fun t => re_le_of_evenCoeff_ne_zero t.2) hs
  obtain ⟨F, hF, hFG⟩ := _root_.RHTower.exists_differentiable_extension_of_le_exp hφm hKb ha0 ha
    hMa' hΛan hΛφ
  have h0 := eq_zero_of_resolventSum_eq_differentiable (lam := fun t : ι => (t : ℂ))
    (q := fun t => -evenCoeff Z b t) hD (A := 1 / 2) ⟨z₀, hz₀⟩
    (fun t ht => hmax t ((Set.Finite.mem_toFinset _).mpr ⟨t.2, ht.trans him₀⟩))
    (fun t ht => Subtype.ext ht) (lt_min hη₁ hη₂) hsep (c := a) (by simp; linarith) hF hFG
  exact hz₀ (neg_eq_zero.mp h0)

/-! ### The spline `U_1^{⋆4}` -/

theorem cx_cubicSpline : cx BiScaleUncertainty.ChebyshevGauge.cubicSpline = boxSpline 1 3 := rfl

/-- `ζ` has no zero on the real segment of the strip. -/
theorem not_mem_carrier_of_im_eq_zero {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) : ρ.im ≠ 0 := by
  intro him
  obtain ⟨hz, h0, h1⟩ := hρ
  have hxi : _root_.RHTower.xi ρ = 0 :=
    _root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr ⟨hz, fun n hn => by
      have h := congrArg Complex.re hn
      simp at h
      linarith [(Nat.cast_nonneg (α := ℝ) n)]⟩
  have hρr : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simp [him])
  have hpos := _root_.RHTower.xi_pos_on_real_anchor h0 h1
  rw [← hρr, hxi] at hpos
  simp at hpos

theorem evenCoeff_spline_real {x : ℂ} (hx : evenCoeff zetaZeroConfig (boxSpline 1 3) x ≠ 0) :
    x.im ≠ 0 := by
  intro him
  rcases mem_of_evenCoeff_ne_zero hx with h | h
  · exact not_mem_carrier_of_im_eq_zero h (by simp [him])
  · exact not_mem_carrier_of_im_eq_zero h (by simp [him])

theorem evenCoeff_spline_sees {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hre : 1 / 2 < ρ.re) :
    evenCoeff zetaZeroConfig (boxSpline 1 3) (ρ - 1 / 2) ≠ 0 :=
  evenCoeff_sub_half_ne_zero_of_conj_symm zetaZeroConfig (contDiff_boxSpline one_pos 2).continuous
    (hasCompactSupport_of_support_subset_abs (boxSpline_support one_pos 3))
    (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ
    (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))

/-- RH from the absence of zeros right of the line. -/
theorem riemannHypothesis_of_forall_re_le
    (h : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_zetaZeroConfig_onLine]
  intro ρ hρ
  have h1 := h ρ hρ
  have h2 := h (Zeta23.reflect ρ) (zetaZeroConfig.reflect_mem ρ hρ)
  have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
  linarith

/-! ### From the integer degrees to every scale -/

/-- Between `log ⌊eᵗ⌋` and `t` the orbit correlation moves by at most `2L`. -/
theorem exists_orbitCorr_sub_floor_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t : ℝ, 0 ≤ t →
      |zetaScalingDatum.orbitCorr splineCycle t -
        zetaScalingDatum.orbitCorr splineCycle (Real.log ⌊Real.exp t⌋₊)| ≤ 2 * L := by
  set x := splineCycle
  have hf : (x.2.2 : ℝ → ℝ) ∈ realTests := x.2.2.2
  obtain ⟨w, hw0, hw⟩ := SquareRootThreshold.exists_radius_of_hasCompactSupport
    (cx_hasCompactSupport hf.2)
  have hbs : ∀ u, cx x.2.2 u ≠ 0 → |u| ≤ w := fun u hu => by
    by_contra hc; exact hu (hw u (not_le.mp hc))
  set L := ∑' z : ℂ, ‖lagCoeff Zeta23.zetaZeroConfig (cx x.2.2) z‖ * ‖z‖
  have hL0 : 0 ≤ L := tsum_nonneg fun _ => by positivity
  refine ⟨L, hL0, fun t ht => ?_⟩
  obtain ⟨hn1, hlog, hgap⟩ := floor_log_gap ht
  set n := ⌊Real.exp t⌋₊
  have hs0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hlip := norm_lagStructure_sub_le SquareRootThreshold.temperedConfig_zetaZeroConfig
    (cx_contDiff hf.1) hw0 hbs hs0 hlog
  have hdiff : |zetaScalingDatum.orbitCorr x t - zetaScalingDatum.orbitCorr x (Real.log n)| ≤
      L * (t - Real.log n) * Real.exp (t / 2) := by
    rw [orbitCorr_eq_re_lagStructure, orbitCorr_eq_re_lagStructure, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans hlip
  have hexp : (t - Real.log n) * Real.exp (t / 2) ≤ 2 := by
    have h1 : Real.exp (-t) * Real.exp (t / 2) ≤ 1 := by
      rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
    calc (t - Real.log n) * Real.exp (t / 2) ≤ 2 * Real.exp (-t) * Real.exp (t / 2) :=
          mul_le_mul_of_nonneg_right hgap (Real.exp_pos (t / 2)).le
      _ ≤ 2 := by nlinarith
  calc _ ≤ L * ((t - Real.log n) * Real.exp (t / 2)) := by rw [← mul_assoc]; exact hdiff
    _ ≤ L * 2 := mul_le_mul_of_nonneg_left hexp hL0
    _ = 2 * L := by ring

theorem orbitCorr_eq_re_lagStructure_spline (v : ℝ) :
    zetaScalingDatum.orbitCorr splineCycle v =
      (lagStructure zetaZeroConfig (boxSpline 1 3) v).re :=
  orbitCorr_eq_re_lagStructure splineCycle v

/-! ### The two one-sided criteria -/

/-- **The Bombieri–Stepanov side.** RH holds iff the traces of the smoothed Frobenius graphs at the
integer degrees are bounded below: an upper bound on the smoothed point counts. -/
theorem riemannHypothesis_iff_bddBelow_integerDegrees :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ n : ℕ, 0 < n →
      -K ≤ zetaScalingDatum.orbitCorr splineCycle (Real.log n) := by
  constructor
  · intro hRH
    refine ⟨zetaScalingDatum.orbitCorr splineCycle 0, fun n hn => ?_⟩
    have h := (riemannHypothesis_iff_hasseWeil_integerDegrees.mp hRH) n hn
    rw [ScalingDatum.HasseWeilAt] at h
    linarith [neg_abs_le (zetaScalingDatum.orbitCorr splineCycle (Real.log n))]
  · rintro ⟨K, hK⟩
    obtain ⟨L, hL0, hL⟩ := exists_orbitCorr_sub_floor_le
    -- `c_B ≥ −(K + 2L)` at every scale `t ≥ 0`
    have hall : ∀ u : ℝ, 0 ≤ u →
        -((2 * |K| + 4 * L) * Real.exp (0 * u)) ≤
          2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re := by
      intro u hu
      obtain ⟨hn1, -, -⟩ := floor_log_gap hu
      have h1 := hK _ (by omega : 0 < ⌊Real.exp u⌋₊)
      have h2 := hL u hu
      rw [← orbitCorr_eq_re_lagStructure_spline]
      rw [zero_mul, Real.exp_zero, mul_one]
      have := (abs_le.mp h2).1
      linarith [le_abs_self K]
    apply riemannHypothesis_of_forall_re_le
    intro ρ hρ
    by_contra hre
    push Not at hre
    exact evenCoeff_spline_sees hρ hre
      (evenCoeff_eq_zero_of_two_re_lagStructure_ge zetaZeroConfig
        SquareRootThreshold.temperedConfig_zetaZeroConfig (contDiff_boxSpline one_pos 2)
        (boxSpline_support one_pos 3) le_rfl (by norm_num)
        (fun x hx him => absurd him (evenCoeff_spline_real hx)) hall
        (by simp; linarith))

/-- **The other side.** RH holds iff the traces at the integer degrees are bounded above. -/
theorem riemannHypothesis_iff_bddAbove_integerDegrees :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ n : ℕ, 0 < n →
      zetaScalingDatum.orbitCorr splineCycle (Real.log n) ≤ K := by
  constructor
  · intro hRH
    refine ⟨zetaScalingDatum.orbitCorr splineCycle 0, fun n hn => ?_⟩
    have h := (riemannHypothesis_iff_hasseWeil_integerDegrees.mp hRH) n hn
    rw [ScalingDatum.HasseWeilAt] at h
    exact (le_abs_self _).trans h
  · rintro ⟨K, hK⟩
    obtain ⟨L, hL0, hL⟩ := exists_orbitCorr_sub_floor_le
    set c0 := zetaScalingDatum.orbitCorr splineCycle 0
    have hrate : ∃ C V : ℝ, ∀ v : ℝ, V ≤ v → -(C * Real.exp (0 * v)) ≤
        (zetaZeroConfig.W (twoBump (boxSpline 1 3) v (-1)) (twoBump (boxSpline 1 3) v (-1))).re := by
      refine ⟨2 * |K| + 4 * L + 2 * |c0|, 0, fun v hv => ?_⟩
      obtain ⟨hn1, -, -⟩ := floor_log_gap hv
      have h1 := hK _ (by omega : 0 < ⌊Real.exp v⌋₊)
      have h2 := hL v hv
      rw [re_W_lag_eq zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig
        (contDiff_boxSpline one_pos 2) (boxSpline_support one_pos 3) v,
        ← orbitCorr_eq_re_lagStructure_spline, ← orbitCorr_eq_re_lagStructure_spline,
        zero_mul, Real.exp_zero, mul_one]
      have := (abs_le.mp h2).2
      linarith [le_abs_self K, neg_abs_le c0]
    have hre := (re_le_iff_lag_twoBump_ge_neg_exp_of_pos zetaZeroConfig
      SquareRootThreshold.temperedConfig_zetaZeroConfig
      (fun ρ hρ => hρ.2.2) (contDiff_boxSpline one_pos 2)
      (boxSpline_support one_pos 3)
      (fun x hx _ him => absurd (by simp [him] : (1 / 2 + x).im = 0) (not_mem_carrier_of_im_eq_zero hx))
      (fun ρ hρ h => evenCoeff_spline_sees hρ h) le_rfl).mpr hrate
    exact riemannHypothesis_of_forall_re_le fun ρ hρ => by simpa using hre ρ hρ

end GaloisForLFunctions.SurfaceOfSpecZ
