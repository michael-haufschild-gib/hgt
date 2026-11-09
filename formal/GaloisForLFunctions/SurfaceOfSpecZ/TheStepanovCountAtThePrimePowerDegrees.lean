import GaloisForLFunctions.SurfaceOfSpecZ.BaseChangeAtThePowerDegrees
import GaloisForLFunctions.SurfaceOfSpecZ.HasseWeilAtThePrimeDegreesBoundsTheWidth
import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion

/-!
# The Stepanov count at the prime-power degrees

The gap method reads the width of the zeros off the gaps of a set of degrees. At the prime degrees,
through Huxley's gaps `x^{7/12+ε}`, Hasse–Weil gives only `|Re ρ − ½| ≤ 1/12`
(`HasseWeilAtThePrimeDegreesBoundsTheWidth`). The multiplicative structure of the degrees gives
everything, from one side.

**Theorem** (`riemannHypothesis_iff_bddBelow_primePowerDegrees`). RH holds iff the traces of the
smoothed Frobenius graphs of prime-power degree are bounded below, `2 Re S(log q) ≥ −K` for every
prime power `q` (`S` the lag structure of the cubic spline): an upper bound on the smoothed point
counts of the planes `⟨Γ_1, Γ_{pᵏ}⟩` of the powers of the prime Frobenii only.

**Proof.**
1. *The gap method from one side* (`re_le_of_bddBelow_primeDegrees`). Between a prime `p` and `eᵗ`
   with `eᵗ − p ≤ e^{5t/8}` the trace moves by `O(e^{t/8})`, so `2 Re S(t) ≥ −M e^{t/8}`, and Landau's
   theorem for the spline exponents (`evenCoeff_eq_zero_of_two_re_lagStructure_ge`) puts every zero
   in `Re ρ ≤ 5/8`.
2. *The von Mangoldt series.* The nonnegative series `Σ_q Λ(q)(2 Re S(log q) + K + 1) q^{−s}` equals
   `−Σ_z e_z ζ'/ζ(s − z) − (K + 1) ζ'/ζ(s)` (`gdSeries_primePowerCoeff_eq`). By step 1, `|Re z| ≤ 1/8`,
   so for `1 < Re s < 15/8` every argument `s − z` has distance `≥ 1/4` from the zeros, where
   `|ζ'/ζ| ≪ log t` (`RHTower.norm_logDeriv_zeta_le`): the sum continues off the poles `1 + z`, none
   of them real. Landau's theorem puts the abscissa at `1`. An off-line zero `½ + z₀`, rightmost on its
   line, gives a pole `1 + z₀` with `Re > 1`; along its ray `−e_{z₀} ζ'/ζ(1 + t)` blows up
   (`exists_norm_logDeriv_zeta_one_add_gt`, from `Σ_p 1/p = ∞`) while the series stays bounded.

Over all integers the abscissa of the trace zeta function is decided by `ζ` alone
(`BaseChangeAtThePowerDegrees`). With the weight `Λ`, the arguments `s − z` must stay right of the
zeros of `ζ`, which needs `Re ρ < ¾`; the prime gaps supply it.
-/

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open GaloisForLFunctions.HTGeometry ArithmeticFunction

/-! ### One side at the primes bounds the width -/

/-- **From `x^θ`-gap degrees to every large scale.** Between `log d` and `t` the orbit correlation
moves by at most `C e^{(θ−½)t}`. -/
theorem exists_orbitCorr_sub_powGap_le {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ} (hD : PowGaps θ D) :
    ∃ C T : ℝ, 0 ≤ C ∧ 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∃ d ∈ D,
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
  refine ⟨d, hdD, ?_⟩
  calc |c t - c (Real.log d)| ≤ L * ((t - Real.log d) * Real.exp (t / 2)) := by
        rw [← mul_assoc]; exact hdiff
    _ ≤ L * (2 * M * Real.exp ((θ - 1 / 2) * t)) := mul_le_mul_of_nonneg_left hg hL0
    _ = 2 * L * M * Real.exp ((θ - 1 / 2) * t) := by ring

/-- **One side at `x^θ`-gap degrees bounds the zeros by `Re ρ ≤ θ`.** -/
theorem re_le_of_bddBelow_of_powGaps {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) {D : Set ℕ}
    (hD : PowGaps θ D) {K : ℝ}
    (hK : ∀ d ∈ D, -K ≤ zetaScalingDatum.orbitCorr splineCycle (Real.log d)) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ θ := by
  obtain ⟨C, T, hC0, hT0, hCT⟩ := exists_orbitCorr_sub_powGap_le hθ1 hD
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_zetaOrbitCorr' splineCycle).continuousOn
  have hall : ∀ u : ℝ, 0 ≤ u →
      -((2 * (|K| + C + |B|)) * Real.exp ((θ - 1 / 2) * u)) ≤
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re := by
    intro u hu
    rw [← orbitCorr_eq_re_lagStructure_spline]
    have he1 : 1 ≤ Real.exp ((θ - 1 / 2) * u) := Real.one_le_exp (mul_nonneg (by linarith) hu)
    have hE0 : 0 ≤ Real.exp ((θ - 1 / 2) * u) := (Real.exp_pos _).le
    rcases le_total u T with huT | hTu
    · have h := hB u ⟨hu, huT⟩
      rw [Real.norm_eq_abs] at h
      have h1 := (abs_le.mp (h.trans (le_abs_self B))).1
      have h2 := mul_le_mul_of_nonneg_left he1 (by positivity : (0 : ℝ) ≤ |K| + C + |B|)
      linarith [abs_nonneg K]
    · obtain ⟨d, hdD, hd⟩ := hCT u hTu
      have h1 := hK d hdD
      have h2 := (abs_le.mp hd).1
      have h3 := mul_le_mul_of_nonneg_left he1 (abs_nonneg K)
      have h4 := mul_nonneg (abs_nonneg B) hE0
      linarith [le_abs_self K]
  intro ρ hρ
  by_contra hre
  push Not at hre
  exact evenCoeff_spline_sees hρ (by linarith)
    (evenCoeff_eq_zero_of_two_re_lagStructure_ge zetaZeroConfig
      SquareRootThreshold.temperedConfig_zetaZeroConfig (contDiff_boxSpline one_pos 2)
      (boxSpline_support one_pos 3) (by linarith : (0 : ℝ) ≤ θ - 1 / 2) (by linarith)
      (fun x hx him => absurd him (evenCoeff_spline_real hx)) hall
      (by simp; linarith))

/-- **One side at the primes puts every zero in `Re ρ ≤ 5/8`.** -/
theorem re_le_of_bddBelow_primeDegrees {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → -K ≤ zetaScalingDatum.orbitCorr splineCycle (Real.log p)) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 5 / 8 :=
  re_le_of_bddBelow_of_powGaps (by norm_num) (by norm_num)
    (powGaps_primes (by norm_num) (by norm_num)) fun p hp => hK p hp

/-! ### The exponents and the traces in a zero-free strip -/

/-- If every zero has `Re ρ ≤ ½ + b`, the exponents satisfy `|Re z| ≤ b` (functional equation). -/
theorem abs_re_le_of_traceCoeff_ne_zero_of_re_le {b : ℝ}
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b) {r : ℕ} {z : ℂ}
    (hz : traceCoeff r z ≠ 0) : |z.re| ≤ b := by
  have key : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re - 1 / 2| ≤ b := by
    intro ρ hρ
    have h1 := hzf ρ hρ
    have h2 := hzf _ (zetaZeroConfig.reflect_mem ρ hρ)
    have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
    rw [hrefl] at h2
    rw [abs_le]; constructor <;> linarith
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · simpa using key _ h
  · simpa using key _ h

/-- `|2 Re S(v)| ≤ E e^{bv}`, `E = Σ |e_z|`, when every exponent has `|Re z| ≤ b`. -/
theorem abs_two_re_lagStructure_le_of_width {b : ℝ}
    (hb : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ b) {v : ℝ} (hv : 0 ≤ v) :
    |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) v).re| ≤
      (∑' z : ℂ, ‖traceCoeff 3 z‖) * Real.exp (b * v) := by
  have hb2 := contDiff_boxSpline_two (le_refl 3)
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  obtain ⟨hs, he⟩ := two_re_lagStructure_eq zetaZeroConfig hZ hb2 hbs v
  have hE : Summable fun z => ‖traceCoeff 3 z‖ := by
    have h0 := (two_re_lagStructure_eq zetaZeroConfig hZ hb2 hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hterm : ∀ z, ‖traceCoeff 3 z * cexp (z * v)‖ ≤ ‖traceCoeff 3 z‖ * Real.exp (b * v) := by
    intro z
    by_cases hz : traceCoeff 3 z = 0
    · simp [hz]
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h1 := (abs_le.mp (hb z hz)).2
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  have h := congrArg norm he
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  rw [h]
  calc ‖∑' z, traceCoeff 3 z * cexp (z * v)‖ ≤ ∑' z, ‖traceCoeff 3 z * cexp (z * v)‖ :=
        norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' z, ‖traceCoeff 3 z‖ * Real.exp (b * v) :=
        Summable.tsum_le_tsum hterm hs.norm (hE.mul_right _)
    _ = _ := tsum_mul_right

/-! ### The logarithmic derivative of `ζ` right of the zeros -/

/-- No zero of `ζ` with `Re ≥ 7/8` once every zero has `Re ρ ≤ 5/8`. -/
theorem riemannZeta_ne_zero_of_re_ge (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 5 / 8)
    {w : ℂ} (hw : 7 / 8 ≤ w.re) : riemannZeta w ≠ 0 := by
  intro h
  rcases le_or_gt 1 w.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1 h
  · have hmem : w ∈ zetaZeroConfig.carrier := ⟨h, by linarith, h1⟩
    linarith [hzf w hmem]

theorem differentiableAt_logDeriv_riemannZeta {w : ℂ} (hw : w ≠ 1) (hz : riemannZeta w ≠ 0) :
    DifferentiableAt ℂ (logDeriv riemannZeta) w := by
  have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun x hx =>
    (differentiableAt_riemannZeta hx).differentiableWithinAt
  have han : AnalyticAt ℂ riemannZeta w := hd.analyticAt (isOpen_compl_singleton.mem_nhds hw)
  have hlog : logDeriv riemannZeta = fun x => deriv riemannZeta x / riemannZeta x := by
    funext x; rw [logDeriv_apply]
  rw [hlog]
  exact han.deriv.differentiableAt.div (differentiableAt_riemannZeta hw) hz

theorem logDeriv_riemannZeta_starRingEnd (w : ℂ) :
    logDeriv riemannZeta (conj w) = conj (logDeriv riemannZeta w) := by
  have hfun : ((starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ)) = riemannZeta := by
    funext v; simp [Function.comp_def, _root_.riemannZeta_conj]
  have hderiv := deriv_conj_conj (f := riemannZeta)
  rw [hfun] at hderiv
  have hd : deriv riemannZeta (conj w) = conj (deriv riemannZeta w) := by
    have := congrFun hderiv (conj w)
    simpa [Function.comp_def] using this
  rw [logDeriv_apply, logDeriv_apply, hd, _root_.riemannZeta_conj, map_div₀]

/-- **`ζ'/ζ` right of the zeros.** If every zero has `Re ρ ≤ 5/8`, then `|ζ'/ζ(w)| ≤ C |Im w|` for
`7/8 ≤ Re w ≤ 2`, `|Im w| ≥ 4`. -/
theorem exists_norm_logDeriv_zeta_le_of_re_le
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 5 / 8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 7 / 8 ≤ w.re → w.re ≤ 2 → 4 ≤ |w.im| →
      ‖logDeriv riemannZeta w‖ ≤ C * |w.im| := by
  have hC : 0 ≤ RHTower.logDerivZetaConstant := by
    unfold RHTower.logDerivZetaConstant; positivity
  have hup : ∀ v : ℂ, 7 / 8 ≤ v.re → v.re ≤ 2 → 4 ≤ v.im →
      ‖logDeriv riemannZeta v‖ ≤ 4 * RHTower.logDerivZetaConstant * v.im := by
    intro v hv1 hv2 hv4
    have hall : ∀ q : RHTower.XiZeroCopy,
        (1 / 4 : ℝ) ≤ ‖((v.re : ℂ) + v.im * I) - (q.1 : ℂ)‖ := by
      intro q
      have hq := hzf _ (RHTower.xiZeroCopy_mem_carrier q)
      calc (1 / 4 : ℝ) ≤ (((v.re : ℂ) + v.im * I) - (q.1 : ℂ)).re := by simp; linarith
        _ ≤ ‖((v.re : ℂ) + v.im * I) - (q.1 : ℂ)‖ := Complex.re_le_norm _
    have h := RHTower.norm_logDeriv_zeta_le (by linarith) hv2 hv4 (by norm_num) (by norm_num) hall
    rw [Complex.re_add_im] at h
    have hlog : Real.log v.im ≤ v.im :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    calc ‖logDeriv riemannZeta v‖ ≤ RHTower.logDerivZetaConstant * Real.log v.im / (1 / 4) := h
      _ = 4 * RHTower.logDerivZetaConstant * Real.log v.im := by ring
      _ ≤ 4 * RHTower.logDerivZetaConstant * v.im := mul_le_mul_of_nonneg_left hlog (by positivity)
  refine ⟨4 * RHTower.logDerivZetaConstant, by positivity, fun w h1 h2 h4 => ?_⟩
  rcases le_or_gt 0 w.im with him | him
  · rw [abs_of_nonneg him] at h4 ⊢; exact hup w h1 h2 h4
  · rw [abs_of_neg him] at h4 ⊢
    have := hup (conj w) (by simpa using h1) (by simpa using h2) (by simpa using h4)
    rwa [logDeriv_riemannZeta_starRingEnd, Complex.norm_conj, Complex.conj_im] at this

/-! ### The von Mangoldt series -/

/-- `Σ_{n ≥ 1} Λ(n) n^{−w} = −ζ'/ζ(w)` for `Re w > 1`, indexed from `n = j + 1`. -/
theorem summable_tsum_vonMangoldt {w : ℂ} (hw : 1 < w.re) :
    Summable (fun j : ℕ => (Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-w)) ∧
      ∑' j : ℕ, (Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-w) = -logDeriv riemannZeta w := by
  have hL := ArithmeticFunction.LSeriesSummable_vonMangoldt hw
  have hterm : ∀ j : ℕ, LSeries.term (fun n => (Λ n : ℂ)) w (j + 1) =
      (Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-w) := by
    intro j
    rw [LSeries.term_def, if_neg (Nat.succ_ne_zero j)]
    push_cast
    rw [Complex.cpow_neg, div_eq_mul_inv]
  have hs : Summable (fun j : ℕ => LSeries.term (fun n => (Λ n : ℂ)) w (j + 1)) :=
    (summable_nat_add_iff 1).mpr hL
  refine ⟨hs.congr hterm, ?_⟩
  have h1 := hL.tsum_eq_zero_add
  rw [LSeries.term_zero, zero_add] at h1
  have h2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw
  rw [LSeries, h1] at h2
  rw [← tsum_congr hterm, h2, logDeriv_apply, neg_div]

/-- **`Σ Λ(n)/n` diverges**: it dominates `log 2 · Σ_p 1/p`. -/
theorem not_summable_vonMangoldt_div :
    ¬ Summable fun j : ℕ => Λ (j + 1) * ((j : ℝ) + 1) ^ (-1 : ℝ) := by
  intro h
  apply Nat.Primes.not_summable_one_div
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 1) := by
    intro p q hpq
    have hp := p.2.one_lt
    have hq := q.2.one_lt
    exact Subtype.ext (by simp only at hpq; omega)
  have h2 := h.comp_injective hinj
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (h2.div_const (Real.log 2))
  have hp1 : 1 ≤ (p : ℕ) := p.2.one_lt.le
  have hpp : (p : ℕ) - 1 + 1 = p := Nat.sub_add_cancel hp1
  have hcast : (((p : ℕ) - 1 : ℕ) : ℝ) + 1 = ((p : ℕ) : ℝ) := by
    rw [← Nat.cast_add_one, hpp]
  simp only [Function.comp_def]
  rw [hpp, hcast, vonMangoldt_apply_prime p.2, Real.rpow_neg_one]
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hlogp : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
  rw [le_div_iff₀ hlog2, one_div]
  calc ((p : ℕ) : ℝ)⁻¹ * Real.log 2 ≤ ((p : ℕ) : ℝ)⁻¹ * Real.log ((p : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlogp (by positivity)
    _ = Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ)⁻¹ := by ring

/-- **The pole of `ζ'/ζ` at `1`.** `|ζ'/ζ(1 + t)|` is unbounded as `t ↓ 0`. -/
theorem exists_norm_logDeriv_zeta_one_add_gt (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧ B < ‖logDeriv riemannZeta (1 + t)‖ := by
  by_contra hcon
  push Not at hcon
  apply not_summable_vonMangoldt_div
  refine summable_of_sum_range_le (c := Real.exp 1 * B)
    (fun j => by have := vonMangoldt_nonneg (n := j + 1); positivity) (fun N => ?_)
  have hlogN : 0 ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  set t := min (δ / 2) (1 / (Real.log ((N : ℝ) + 1) + 1)) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by positivity)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have htlog : t * Real.log ((N : ℝ) + 1) ≤ 1 := by
    have h1 : t ≤ 1 / (Real.log ((N : ℝ) + 1) + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  -- the real series at `1 + t`
  obtain ⟨hs, he⟩ := summable_tsum_vonMangoldt (w := ((1 + t : ℝ) : ℂ)) (by simp; linarith)
  have hreal : ∀ j : ℕ, (Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-((1 + t : ℝ) : ℂ)) =
      ((Λ (j + 1) * ((j : ℝ) + 1) ^ (-(1 + t)) : ℝ) : ℂ) := by
    intro j
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have hg : Summable fun j : ℕ => Λ (j + 1) * ((j : ℝ) + 1) ^ (-(1 + t)) :=
    Complex.summable_ofReal.mp (hs.congr hreal)
  have hcast : ((1 + t : ℝ) : ℂ) = 1 + (t : ℂ) := by push_cast; ring
  have hsum : ((∑' j : ℕ, Λ (j + 1) * ((j : ℝ) + 1) ^ (-(1 + t)) : ℝ) : ℂ) =
      -logDeriv riemannZeta (1 + t) := by
    rw [Complex.ofReal_tsum, ← tsum_congr hreal, he, hcast]
  have hle : ∑' j : ℕ, Λ (j + 1) * ((j : ℝ) + 1) ^ (-(1 + t)) ≤ B := by
    have h1 := hcon t ht0 htδ
    have h2 := congrArg norm hsum
    rw [Complex.norm_real, Real.norm_eq_abs, norm_neg] at h2
    linarith [le_abs_self (∑' j : ℕ, Λ (j + 1) * ((j : ℝ) + 1) ^ (-(1 + t)))]
  calc ∑ j ∈ Finset.range N, Λ (j + 1) * ((j : ℝ) + 1) ^ (-1 : ℝ)
      ≤ ∑ j ∈ Finset.range N, Real.exp 1 * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(1 + t))) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjN : (j : ℝ) + 1 ≤ N + 1 := by
          have : (j : ℝ) < N := by exact_mod_cast Finset.mem_range.mp hj
          linarith
        have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have hsplit : ((j : ℝ) + 1) ^ (-1 : ℝ) =
            ((j : ℝ) + 1) ^ (-(1 + t)) * ((j : ℝ) + 1) ^ t := by
          rw [← Real.rpow_add hj0]; ring_nf
        have hpow : ((j : ℝ) + 1) ^ t ≤ Real.exp 1 := by
          rw [Real.rpow_def_of_pos hj0]
          apply Real.exp_le_exp.mpr
          have h1 : Real.log ((j : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hj0 hjN
          nlinarith
        rw [hsplit]
        have hΛ := vonMangoldt_nonneg (n := j + 1)
        have hp : 0 ≤ ((j : ℝ) + 1) ^ (-(1 + t)) := by positivity
        calc Λ (j + 1) * (((j : ℝ) + 1) ^ (-(1 + t)) * ((j : ℝ) + 1) ^ t)
            = (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(1 + t))) * ((j : ℝ) + 1) ^ t := by ring
          _ ≤ (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(1 + t))) * Real.exp 1 :=
              mul_le_mul_of_nonneg_left hpow (mul_nonneg hΛ hp)
          _ = _ := by ring
    _ = Real.exp 1 * ∑ j ∈ Finset.range N, Λ (j + 1) * ((j : ℝ) + 1) ^ (-(1 + t)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp 1 * B := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
        exact (Summable.sum_le_tsum (Finset.range N)
          (fun j _ => by have := vonMangoldt_nonneg (n := j + 1); positivity) hg).trans hle

/-- The coefficients `Λ(n)(2 Re S(log n) + K + 1)` at `n = j + 1`. -/
def primePowerCoeff (K : ℝ) (j : ℕ) : ℝ :=
  Λ (j + 1) * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re + K + 1)

/-- `Σ_z c_z ζ'/ζ(s − z)`. -/
def traceLogDerivOf (c : ℂ → ℂ) (s : ℂ) : ℂ := ∑' z : ℂ, c z * logDeriv riemannZeta (s - z)

/-- The candidate continuation `−Σ_z e_z ζ'/ζ(s − z) − (K + 1) ζ'/ζ(s)`. -/
def primePowerZeta (K : ℝ) (s : ℂ) : ℂ :=
  -traceLogDerivOf (traceCoeff 3) s - ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s

/-- **The traces at the prime powers have the Dirichlet series `−Σ_z e_z ζ'/ζ(s − z)`.** -/
theorem gdSeries_primePowerCoeff_eq (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 5 / 8) (K : ℝ)
    {s : ℂ} (hs : 9 / 8 < s.re) :
    gdSeries (primePowerCoeff K) powerFreq s = primePowerZeta K s := by
  have hb := contDiff_boxSpline_two (le_refl 3)
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  set e := traceCoeff 3 with he
  have hE : Summable fun z => ‖e z‖ := by
    have h0 := (two_re_lagStructure_eq zetaZeroConfig hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hw : ∀ z, e z ≠ 0 → |z.re| ≤ 1 / 8 := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le (fun ρ hρ => by linarith [hzf ρ hρ]) hz
  set σ' := s.re - 1 / 8 with hσ'
  have hσ'1 : 1 < σ' := by rw [hσ']; linarith
  have hΛ : Summable fun j : ℕ => Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ') := by
    have h := (summable_tsum_vonMangoldt (w := (σ' : ℂ)) (by simpa using hσ'1)).1.norm
    refine h.congr fun j => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      norm_natCast_add_one_cpow]
    simp
  set f : ℕ → ℂ → ℂ := fun j z => (Λ (j + 1) : ℂ) * (e z * ((j : ℂ) + 1) ^ (-(s - z))) with hf
  have hfn : ∀ j z, ‖f j z‖ ≤ Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ') * ‖e z‖ := by
    intro j z
    by_cases hz : e z = 0
    · simp [hf, hz]
    have hre := (abs_le.mp (hw z hz)).2
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      norm_natCast_add_one_cpow]
    have hexp : ((j : ℝ) + 1) ^ (-(s - z)).re ≤ ((j : ℝ) + 1) ^ (-σ') := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j])
      simp only [Complex.neg_re, Complex.sub_re]; rw [hσ']; linarith
    have hΛ0 := vonMangoldt_nonneg (n := j + 1)
    calc Λ (j + 1) * (‖e z‖ * ((j : ℝ) + 1) ^ (-(s - z)).re)
        ≤ Λ (j + 1) * (‖e z‖ * ((j : ℝ) + 1) ^ (-σ')) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)) hΛ0
      _ = _ := by ring
  have hprod : Summable fun p : ℕ × ℂ => Λ (p.1 + 1) * ((p.1 : ℝ) + 1) ^ (-σ') * ‖e p.2‖ :=
    hΛ.mul_of_nonneg hE (fun j => mul_nonneg vonMangoldt_nonneg (by positivity))
      (fun _ => norm_nonneg _)
  have hF : Summable (Function.uncurry f) := Summable.of_norm_bounded hprod fun p => hfn p.1 p.2
  -- the fibres over `j`
  have hj : ∀ j : ℕ, ∑' z, f j z = (Λ (j + 1) : ℂ) *
      (((2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re : ℝ) : ℂ) *
        ((j : ℂ) + 1) ^ (-s)) := by
    intro j
    simp only [hf]
    rw [tsum_mul_left]
    congr 1
    rw [(two_re_lagStructure_eq zetaZeroConfig hZ hb hbs (Real.log (j + 1))).2, ← tsum_mul_right]
    refine tsum_congr fun z => ?_
    rw [natCast_add_one_cpow_eq, natCast_add_one_cpow_eq, mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  -- the fibres over `z`
  have hz : ∀ z : ℂ, ∑' j, f j z = e z * (-logDeriv riemannZeta (s - z)) := by
    intro z
    by_cases hz0 : e z = 0
    · simp [hf, hz0]
    have hre := (abs_le.mp (hw z hz0)).2
    have hres : 1 < (s - z).re := by simp only [Complex.sub_re]; linarith
    obtain ⟨-, hsum⟩ := summable_tsum_vonMangoldt hres
    rw [← hsum, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hf]; ring
  obtain ⟨hKs, hKe⟩ := summable_tsum_vonMangoldt (w := s) (by linarith)
  have hFp : Summable fun j => ∑' z, f j z := hF.prod
  have hterm : ∀ j : ℕ, ((primePowerCoeff K j : ℝ) : ℂ) * Complex.exp (-(s * (powerFreq j : ℂ))) =
      ∑' z, f j z + ((K + 1 : ℝ) : ℂ) * ((Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-s)) := by
    intro j
    rw [hj, cexp_neg_mul_powerFreq, primePowerCoeff]
    push_cast
    ring
  unfold gdSeries primePowerZeta traceLogDerivOf
  calc ∑' j : ℕ, ((primePowerCoeff K j : ℝ) : ℂ) * Complex.exp (-(s * (powerFreq j : ℂ)))
      = ∑' j : ℕ, (∑' z, f j z + ((K + 1 : ℝ) : ℂ) * ((Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-s))) :=
        tsum_congr hterm
    _ = ∑' j : ℕ, ∑' z, f j z +
          ((K + 1 : ℝ) : ℂ) * ∑' j : ℕ, (Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-s) := by
        rw [hFp.tsum_add (hKs.mul_left _), tsum_mul_left]
    _ = ∑' z, ∑' j, f j z + ((K + 1 : ℝ) : ℂ) * (-logDeriv riemannZeta s) := by
        rw [← hF.tsum_comm, hKe]
    _ = ∑' z, e z * (-logDeriv riemannZeta (s - z)) +
          ((K + 1 : ℝ) : ℂ) * (-logDeriv riemannZeta s) := by
        rw [tsum_congr hz]
    _ = -∑' z, e z * logDeriv riemannZeta (s - z) -
          ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s := by
        simp only [mul_neg, tsum_neg]; ring

/-! ### Continuation off the poles -/

/-- **Continuation of `Σ_z c_z ζ'/ζ(s − z)`** to `1 < Re s < 15/8` off the poles `1 + z`, once every
zero has `Re ρ ≤ 5/8`, for coefficients dominated by the spline coefficients. -/
theorem differentiableAt_traceLogDerivOf (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 5 / 8)
    {c : ℂ → ℂ} (hc : ∀ z, ‖c z‖ ≤ ‖traceCoeff 3 z‖)
    {s₀ : ℂ} (hs1 : 1 < s₀.re) (hs2 : s₀.re < 15 / 8)
    (hpole : ∀ z, c z ≠ 0 → s₀ ≠ 1 + z) :
    DifferentiableAt ℂ (traceLogDerivOf c) s₀ := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_zeta_le_of_re_le hzf
  have hsupp : ∀ z, c z ≠ 0 → traceCoeff 3 z ≠ 0 := fun z hz h =>
    hz (norm_eq_zero.mp (le_antisymm ((hc z).trans (by rw [h, norm_zero])) (norm_nonneg _)))
  have hre : ∀ z, c z ≠ 0 → |z.re| ≤ 1 / 8 := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le (fun ρ hρ => by linarith [hzf ρ hρ]) (hsupp z hz)
  -- the poles near the horizontal line of `s₀`
  set F : Set ℂ := {z | c z ≠ 0 ∧ |z.im - s₀.im| ≤ 5} with hFdef
  have hF : F.Finite := by
    refine (finite_traceCoeff_height 3 (|s₀.im| + 5)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hsupp z hz0, ?_⟩
    have h1 := abs_le.mp hzim
    rw [abs_le]; constructor <;> linarith [neg_abs_le s₀.im, le_abs_self s₀.im]
  obtain ⟨δ, hδ0, hδ1, hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ F, δ ≤ ‖s₀ - (1 + z)‖ := by
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · exact ⟨1, one_pos, le_rfl, by simp [hFe]⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hF.toFinset.exists_min_image (fun z => ‖s₀ - (1 + z)‖)
        (by simpa using hFne)
      have hz₁' := hF.mem_toFinset.mp hz₁
      refine ⟨min 1 ‖s₀ - (1 + z₁)‖,
        lt_min one_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hpole z₁ hz₁'.1))),
        min_le_left _ _, fun z hz => (min_le_right _ _).trans (hmin z (hF.mem_toFinset.mpr hz))⟩
  set ε := min (δ / 2) (min ((s₀.re - 1) / 2) ((15 / 8 - s₀.re) / 2)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hε1 : ε ≤ (s₀.re - 1) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ (15 / 8 - s₀.re) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  -- on the closed ball every argument `s − z` lies in `7/8 ≤ Re ≤ 2` and avoids `1`
  have hstrip : ∀ z, c z ≠ 0 → ∀ s ∈ Metric.closedBall s₀ ε,
      7 / 8 ≤ (s - z).re ∧ (s - z).re ≤ 2 := by
    intro z hz s hs
    have hs' : ‖s - s₀‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs
    have hre' : |s.re - s₀.re| ≤ ε := (Complex.abs_re_le_norm (s - s₀)).trans (by simpa using hs')
    have h1 := abs_le.mp hre'
    have h2 := abs_le.mp (hre z hz)
    simp only [Complex.sub_re]
    constructor <;> linarith
  have hfar : ∀ z, c z ≠ 0 → ∀ s ∈ Metric.closedBall s₀ ε, s - z ≠ 1 := by
    intro z hz s hs h
    have hs' : ‖s - s₀‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs
    by_cases hzF : z ∈ F
    · have h1 := hδF z hzF
      have h2 : s₀ - (1 + z) = s₀ - s := by rw [← h]; ring
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
  have hζne : ∀ z, c z ≠ 0 → ∀ s ∈ Metric.closedBall s₀ ε, riemannZeta (s - z) ≠ 0 :=
    fun z hz s hs => riemannZeta_ne_zero_of_re_ge hzf (hstrip z hz s hs).1
  -- bounds for the finitely many nearby terms
  have hM : ∀ z ∈ F, ∃ M : ℝ, ∀ s ∈ Metric.closedBall s₀ ε,
      ‖logDeriv riemannZeta (s - z)‖ ≤ M := by
    intro z hz
    have hcont : ContinuousOn (fun s => logDeriv riemannZeta (s - z)) (Metric.closedBall s₀ ε) := by
      intro s hs
      have hd : DifferentiableAt ℂ (fun s => logDeriv riemannZeta (s - z)) s :=
        (differentiableAt_logDeriv_riemannZeta (hfar z hz.1 s hs) (hζne z hz.1 s hs)).comp s
          (differentiableAt_id.sub_const _)
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
  have hdiff : DifferentiableOn ℂ (traceLogDerivOf c) (Metric.ball s₀ ε) := by
    unfold traceLogDerivOf
    refine differentiableOn_tsum_of_summable_norm hus (fun z => ?_) Metric.isOpen_ball
      (fun z s hs => ?_)
    · by_cases hz : c z = 0
      · simp only [hz, zero_mul]; exact differentiableOn_const _
      · intro s hs
        have hs' := Metric.ball_subset_closedBall hs
        exact ((differentiableAt_logDeriv_riemannZeta (hfar z hz s hs') (hζne z hz s hs')).comp s
          (differentiableAt_id.sub (differentiableAt_const _))).const_mul _ |>.differentiableWithinAt
    · have hs' := Metric.ball_subset_closedBall hs
      have hsn : ‖s - s₀‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs'
      by_cases hz : c z = 0
      · simp only [hz, zero_mul, norm_zero]
        exact add_nonneg (by positivity) (by split_ifs <;> positivity)
      by_cases hzF : z ∈ F
      · have h1 := hMb z hzF s hs'
        simp only [hu, if_pos hzF, norm_mul]
        have : ‖c z‖ * ‖logDeriv riemannZeta (s - z)‖ ≤ ‖c z‖ * |M z| :=
          mul_le_mul_of_nonneg_left (h1.trans (le_abs_self _)) (norm_nonneg _)
        have h0 : 0 ≤ ‖c z‖ * (C * K₀ * (1 + |z.im|)) := by positivity
        linarith
      · -- far from the line of `s₀`: the bound right of the zeros
        have hzF' : 5 < |z.im - s₀.im| := by
          by_contra h; exact hzF ⟨hz, not_lt.mp h⟩
        have hst := hstrip z hz s hs'
        set w := s - z with hw
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

/-- **Pointwise convergence** of `Σ_z c_z ζ'/ζ(s − z)` for `1 < Re s < 15/8`. -/
theorem summable_traceLogDerivOf_terms (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 5 / 8)
    {c : ℂ → ℂ} (hc : ∀ z, ‖c z‖ ≤ ‖traceCoeff 3 z‖)
    {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 15 / 8) :
    Summable fun z => c z * logDeriv riemannZeta (s - z) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_zeta_le_of_re_le hzf
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
    (if z ∈ F then ‖c z * logDeriv riemannZeta (s - z)‖ else 0) with hu
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
  have hre := abs_le.mp (abs_re_le_of_traceCoeff_ne_zero_of_re_le (b := 1 / 8)
    (fun ρ hρ => by linarith [hzf ρ hρ]) (hsupp z hz))
  set w := s - z with hw
  have hwim : w.im = s.im - z.im := by simp [hw]
  have hwre : w.re = s.re - z.re := by simp [hw]
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

/-- The candidate continuation is holomorphic on a ball around every non-pole `s₀`,
`1 < Re s₀ < 15/8`. -/
theorem exists_ball_differentiableOn_primePowerZeta
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 5 / 8) (K : ℝ)
    {s₀ : ℂ} (hs1 : 1 < s₀.re) (hs2 : s₀.re < 15 / 8)
    (hpole : ∀ z, traceCoeff 3 z ≠ 0 → s₀ ≠ 1 + z) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (primePowerZeta K) (ball s₀ ρ) := by
  classical
  set P : Set ℂ := {z | traceCoeff 3 z ≠ 0 ∧ |z.im - s₀.im| ≤ 1} with hPdef
  have hP : P.Finite := by
    refine (finite_traceCoeff_height 3 (|s₀.im| + 1)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hz0, ?_⟩
    have := abs_le.mp hzim
    rw [abs_le]; constructor <;> linarith [neg_abs_le s₀.im, le_abs_self s₀.im]
  obtain ⟨δ, hδ0, hδ1, hδP⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ P, δ ≤ ‖s₀ - (1 + z)‖ := by
    rcases P.eq_empty_or_nonempty with hPe | hPne
    · exact ⟨1, one_pos, le_rfl, by simp [hPe]⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hP.toFinset.exists_min_image (fun z => ‖s₀ - (1 + z)‖)
        (by simpa using hPne)
      have hz₁' := hP.mem_toFinset.mp hz₁
      refine ⟨min 1 ‖s₀ - (1 + z₁)‖,
        lt_min one_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hpole z₁ hz₁'.1))),
        min_le_left _ _, fun z hz => (min_le_right _ _).trans (hmin z (hP.mem_toFinset.mpr hz))⟩
  set ρ := min δ (min (s₀.re - 1) (15 / 8 - s₀.re)) / 2 with hρdef
  have hρ0 : 0 < ρ := by
    rw [hρdef]; exact half_pos (lt_min hδ0 (lt_min (by linarith) (by linarith)))
  have hρδ : ρ < δ := by
    rw [hρdef]; have := min_le_left δ (min (s₀.re - 1) (15 / 8 - s₀.re)); linarith
  have hρ1 : ρ < s₀.re - 1 := by
    rw [hρdef]
    have := (min_le_right δ (min (s₀.re - 1) (15 / 8 - s₀.re))).trans (min_le_left _ _)
    linarith
  have hρ2 : ρ < 15 / 8 - s₀.re := by
    rw [hρdef]
    have := (min_le_right δ (min (s₀.re - 1) (15 / 8 - s₀.re))).trans (min_le_right _ _)
    linarith
  refine ⟨ρ, hρ0, fun s hs => ?_⟩
  rw [mem_ball, dist_eq_norm] at hs
  have hre : |s.re - s₀.re| < ρ :=
    lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀)) hs
  have him : |s.im - s₀.im| < ρ :=
    lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (s - s₀)) hs
  have hs1' : 1 < s.re := by linarith [(abs_lt.mp hre).1]
  have hs2' : s.re < 15 / 8 := by linarith [(abs_lt.mp hre).2]
  have hnp : ∀ z, traceCoeff 3 z ≠ 0 → s ≠ 1 + z := by
    intro z hz h
    have hzim : s.im = z.im := by have := congrArg Complex.im h; simp at this; linarith
    have hzP : z ∈ P := ⟨hz, by rw [← hzim]; linarith [abs_lt.mp him, hδ1, hρδ]⟩
    have h1 := hδP z hzP
    rw [← h, norm_sub_rev] at h1
    linarith
  have h1 := differentiableAt_traceLogDerivOf hzf (c := traceCoeff 3) (fun _ => le_rfl)
    hs1' hs2' hnp
  have hs1ne : s ≠ 1 := fun h => by rw [h] at hs1'; simp at hs1'
  have h2 := differentiableAt_logDeriv_riemannZeta hs1ne
    (riemannZeta_ne_zero_of_one_le_re hs1'.le)
  exact (h1.neg.sub (h2.const_mul _)).differentiableWithinAt

/-! ### The theorem -/

/-- **The Stepanov count at the prime-power degrees.** RH holds iff the traces `2 Re S(log q)` of the
smoothed Frobenius graphs of prime-power degree `q` are bounded below. -/
theorem riemannHypothesis_iff_bddBelow_primePowerDegrees :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ n : ℕ, IsPrimePow n →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log n)).re := by
  classical
  have hb := contDiff_boxSpline_two (le_refl 3)
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  constructor
  · -- under RH the lag structure is bounded
    intro hRH
    have hon := riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH
    set L₀ := ∑' z : ℂ, ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z‖ with hL₀
    refine ⟨2 * L₀, fun n _ => ?_⟩
    set v : ℝ := Real.log n
    obtain ⟨hs, he⟩ := lagStructure_eq_tsum_lagCoeff zetaZeroConfig hZ hb hbs v
    have hterm : ∀ z, ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z * cexp (z * v)‖ =
        ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z‖ := by
      intro z
      by_cases hz : lagCoeff zetaZeroConfig (boxSpline 1 3) z = 0
      · simp [hz]
      have hmem : (1 / 2 + z) ∈ zetaZeroConfig.carrier := by
        by_contra h; exact hz (by rw [lagCoeff, Set.indicator_of_notMem h])
      have hre : z.re = 0 := by have := hon _ hmem; simp at this; linarith
      rw [norm_mul, Complex.norm_exp]
      simp [hre]
    have hle : ‖lagStructure zetaZeroConfig (boxSpline 1 3) v‖ ≤ L₀ := by
      rw [he]
      calc ‖∑' z, lagCoeff zetaZeroConfig (boxSpline 1 3) z * cexp (z * v)‖
          ≤ ∑' z, ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z * cexp (z * v)‖ :=
            norm_tsum_le_tsum_norm hs.norm
        _ = L₀ := tsum_congr hterm
    have h1 := (Complex.abs_re_le_norm (lagStructure zetaZeroConfig (boxSpline 1 3) v)).trans hle
    linarith [(abs_le.mp h1).1]
  · rintro ⟨K, hK⟩
    -- step 1: the zeros lie in `Re ρ ≤ 5/8`
    have hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 5 / 8 :=
      re_le_of_bddBelow_primeDegrees (K := K / 2) fun p hp => by
        have := hK p hp.isPrimePow
        rw [orbitCorr_eq_re_lagStructure_spline]; linarith
    by_contra hRH
    have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ 1 / 8 := fun z hz =>
      abs_re_le_of_traceCoeff_ne_zero_of_re_le (fun ρ hρ => by linarith [hzf ρ hρ]) hz
    -- step 2: the nonnegative von Mangoldt series
    set a := primePowerCoeff K with ha_def
    have haΛ : ∀ j, Λ (j + 1) ≤ a j := by
      intro j
      simp only [ha_def, primePowerCoeff]
      by_cases hΛ : Λ (j + 1) = 0
      · rw [hΛ]; simp
      · have hpp : IsPrimePow (j + 1) := vonMangoldt_ne_zero_iff.mp hΛ
        have := hK (j + 1) hpp
        push_cast at this
        have h0 := vonMangoldt_nonneg (n := j + 1)
        nlinarith
    have ha : ∀ j, 0 ≤ a j := fun j => vonMangoldt_nonneg.trans (haΛ j)
    have hlam : ∀ j, 0 ≤ powerFreq j := powerFreq_nonneg
    have htw : ∀ σ j, gdTwistTerm a powerFreq σ 0 j = a j * ((j : ℝ) + 1) ^ (-σ) := by
      intro σ j; rw [gdTwistTerm, pow_zero, mul_one, real_exp_neg_mul_powerFreq]
    set E := ∑' z : ℂ, ‖traceCoeff 3 z‖ with hE
    have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
    -- convergence right of `9/8`, divergence left of `1`
    have hsumHigh : ∀ σ : ℝ, 9 / 8 < σ → Summable (gdTwistTerm a powerFreq σ 0) := by
      intro σ hσ
      set ε := (σ - 9 / 8) / 2 with hε
      have hε0 : 0 < ε := by rw [hε]; linarith
      have hg := summable_add_one_rpow_neg (p := σ - 1 / 8 - ε) (by rw [hε]; linarith)
      refine Summable.of_nonneg_of_le (fun j => gdTwistTerm_nonneg ha hlam σ 0 j) (fun j => ?_)
        (hg.mul_left ((E + |K| + 1) / ε))
      rw [htw]
      have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
      have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
      have hlog : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg hj1
      have habs := abs_two_re_lagStructure_le_of_width hw hlog
      have hexp : Real.exp (1 / 8 * Real.log ((j : ℝ) + 1)) = ((j : ℝ) + 1) ^ ((1 : ℝ) / 8) := by
        rw [Real.rpow_def_of_pos hj0]; ring_nf
      rw [hexp] at habs
      have hp8 : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hj1 (by norm_num)
      have hΛle : Λ (j + 1) ≤ ((j : ℝ) + 1) ^ ε / ε := by
        have := vonMangoldt_le_log (n := j + 1)
        push_cast at this
        exact this.trans (Real.log_le_rpow_div hj0.le hε0)
      have hinner : 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re +
          K + 1 ≤ (E + |K| + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8) := by
        have h1 := (abs_le.mp habs).2
        have h2 := mul_le_mul_of_nonneg_left hp8 (by linarith [abs_nonneg K] : (0 : ℝ) ≤ |K| + 1)
        nlinarith [le_abs_self K]
      have hR : 0 ≤ ((j : ℝ) + 1) ^ ε / ε * ((E + |K| + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) :=
        mul_nonneg (div_nonneg (by positivity) hε0.le)
          (mul_nonneg (by linarith [abs_nonneg K]) (by positivity))
      have haj : a j ≤ ((j : ℝ) + 1) ^ ε / ε * ((E + |K| + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) := by
        by_cases hΛ : Λ (j + 1) = 0
        · simp only [ha_def, primePowerCoeff, hΛ, zero_mul]; exact hR
        · have hpp : IsPrimePow (j + 1) := vonMangoldt_ne_zero_iff.mp hΛ
          have h1 := hK (j + 1) hpp
          push_cast at h1
          have hin0 : 0 ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
              (Real.log ((j : ℝ) + 1))).re + K + 1 := by linarith
          simp only [ha_def, primePowerCoeff]
          exact mul_le_mul hΛle hinner hin0 (by positivity)
      have hpos : 0 ≤ ((j : ℝ) + 1) ^ (-σ) := by positivity
      calc a j * ((j : ℝ) + 1) ^ (-σ)
          ≤ ((j : ℝ) + 1) ^ ε / ε * ((E + |K| + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) *
              ((j : ℝ) + 1) ^ (-σ) := mul_le_mul_of_nonneg_right haj hpos
        _ = (E + |K| + 1) / ε * (((j : ℝ) + 1) ^ ε * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8) *
              ((j : ℝ) + 1) ^ (-σ)) := by ring
        _ = (E + |K| + 1) / ε * ((j : ℝ) + 1) ^ (-(σ - 1 / 8 - ε)) := by
            rw [← Real.rpow_add hj0, ← Real.rpow_add hj0]; congr 2; ring
    have hdivLow : ∀ σ : ℝ, σ ≤ 1 → ¬ Summable (gdTwistTerm a powerFreq σ 0) := by
      intro σ hσ hs
      apply not_summable_vonMangoldt_div
      refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hs
      · have := vonMangoldt_nonneg (n := j + 1); positivity
      · rw [htw]
        have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
        have h1 : ((j : ℝ) + 1) ^ (-1 : ℝ) ≤ ((j : ℝ) + 1) ^ (-σ) :=
          Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
        exact mul_le_mul (haΛ j) h1 (by positivity) (ha j)
    -- the abscissa
    set S : Set ℝ := {σ | Summable (gdTwistTerm a powerFreq σ 0)} with hSdef
    have hS2 : (5 / 4 : ℝ) ∈ S := hsumHigh _ (by norm_num)
    have hSne : S.Nonempty := ⟨_, hS2⟩
    have hSbdd : BddBelow S := ⟨1, fun σ hσ => by
      by_contra h; exact hdivLow σ (le_of_lt (not_le.mp h)) hσ⟩
    set σc := sInf S with hσcdef
    have hsum : ∀ σ, σc < σ → Summable (gdTwistTerm a powerFreq σ 0) := by
      intro σ hσ
      obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hSne hσ
      exact summable_gdTwistTerm_of_le ha hlam hσ'S hlt.le
    have hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm a powerFreq σ 0) := fun σ hσ hs =>
      absurd (csInf_le hSbdd hs) (not_le.mpr hσ)
    have hσc2 : σc ≤ 5 / 4 := csInf_le hSbdd hS2
    -- analyticity
    have hgdAn : ∀ s : ℂ, σc < s.re → AnalyticAt ℂ (gdSeries a powerFreq) s := by
      intro s hs
      have hopen : IsOpen {w : ℂ | σc < w.re} := isOpen_lt continuous_const Complex.continuous_re
      refine DifferentiableOn.analyticAt (s := {w : ℂ | σc < w.re}) (fun w hw => ?_)
        (hopen.mem_nhds hs)
      have hw' : σc < w.re := hw
      exact (RHTower.differentiableAt_gdSeries ha hlam (hsum ((σc + w.re) / 2) (by linarith))
        (by linarith)).differentiableWithinAt
    have hGAn : ∀ s : ℂ, 1 < s.re → s.re < 15 / 8 →
        (∀ z, traceCoeff 3 z ≠ 0 → s ≠ 1 + z) → AnalyticAt ℂ (primePowerZeta K) s := by
      intro s h1 h2 hp
      obtain ⟨ρ, hρ, hd⟩ := exists_ball_differentiableOn_primePowerZeta hzf K h1 h2 hp
      exact hd.analyticAt (ball_mem_nhds s hρ)
    have hrealNoPole : ∀ t : ℝ, ∀ z, traceCoeff 3 z ≠ 0 → (t : ℂ) ≠ 1 + z := by
      intro t z hz h
      have him := congrArg Complex.im h
      simp only [Complex.ofReal_im, Complex.add_im, Complex.one_im, zero_add] at him
      exact traceCoeff_im_ne_zero hz him.symm
    have hagreeHigh : ∀ s : ℂ, 9 / 8 < s.re →
        gdSeries a powerFreq s = primePowerZeta K s := fun s hs =>
      gdSeries_primePowerCoeff_eq hzf K hs
    -- Landau: the abscissa is at most `1`
    have hσc : σc ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have h2 : σc < 15 / 8 := by linarith
      obtain ⟨ρ, hρ, hG⟩ := exists_ball_differentiableOn_primePowerZeta hzf K
        (s₀ := (σc : ℂ)) (by simpa using hgt) (by simpa using h2)
        (fun z hz => hrealNoPole σc z hz)
      have hreal : ∀ t ∈ Ioo σc (15 / 8),
          gdSeries a powerFreq ((0 : ℂ) + t) = primePowerZeta K ((0 : ℂ) + t) := by
        refine eqOn_ray_of_eventually (a := σc) (c := 3 / 2) (b := 15 / 8)
          (by linarith) (by norm_num) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
        · rw [zero_add]; exact hgdAn _ (by simpa using ht.1)
        · rw [zero_add]
          exact hGAn _ (by simpa using hgt.trans ht.1) (by simpa using ht.2)
            (fun z hz => hrealNoPole t z hz)
        · rw [zero_add]; exact hagreeHigh _ (by simp; linarith [ht.1])
      have hhalf := eqOn_halfBall (f := primePowerZeta K) (g := gdSeries a powerFreq) hρ
        (fun s hs _ => hG.analyticAt (isOpen_ball.mem_nhds hs))
        (fun s _ hs => hgdAn s hs)
        (fun t ht1 _ => by
          rcases lt_or_ge t (15 / 8) with htb | htb
          · have := hreal t ⟨ht1, htb⟩; rw [zero_add] at this; exact this.symm
          · exact (hagreeHigh _ (by simp; linarith)).symm)
      exact RHTower.gdSeries_no_continuation_at_abscissa ha hlam hsum hdiv hρ hG
        (fun s hs hre => hhalf s hs hre)
    -- an off-line zero, rightmost on its line
    have hoff : ∃ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re := by
      by_contra h; push Not at h; exact hRH (riemannHypothesis_of_forall_re_le h)
    obtain ⟨ρ₁, hρ₁, hρ₁re⟩ := hoff
    set z₁ := ρ₁ - 1 / 2 with hz₁def
    have hz₁ : traceCoeff 3 z₁ ≠ 0 := traceCoeff_sees (le_refl 3) hρ₁ hρ₁re
    set Lset := (finite_evenCoeff_line zetaZeroConfig (boxSpline 1 3) z₁.im).toFinset with hLset
    obtain ⟨z₀, hz₀L, hmax⟩ := Lset.exists_max_image Complex.re
      ⟨z₁, (Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩⟩
    obtain ⟨hz₀, him₀⟩ := (Set.Finite.mem_toFinset _).mp hz₀L
    have hre₀ : z₁.re ≤ z₀.re := hmax z₁ ((Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩)
    have hz₁re : 0 < z₁.re := by simp [hz₁def]; linarith
    have hz₀re : z₀.re ≤ 1 / 8 := (abs_le.mp (hw z₀ hz₀)).2
    set s₀ : ℂ := 1 + z₀ with hs₀def
    have hs₀re : s₀.re = 1 + z₀.re := by simp [hs₀def]
    have hs₀1 : 1 < s₀.re := by rw [hs₀re]; linarith
    have hs₀2 : s₀.re ≤ 9 / 8 := by rw [hs₀re]; linarith
    set T : ℝ := 15 / 8 - s₀.re with hTdef
    have hT : 3 / 4 ≤ T := by rw [hTdef]; linarith
    have hqre : ∀ t : ℝ, (s₀ + t).re = s₀.re + t := fun t => by simp
    -- no pole to the right of `1 + z₀` on its line
    have hray : ∀ t : ℝ, 0 < t → ∀ z, traceCoeff 3 z ≠ 0 → s₀ + t ≠ 1 + z := by
      intro t ht z hz h
      have him := congrArg Complex.im h
      have hre := congrArg Complex.re h
      simp [hs₀def] at him hre
      have hle := hmax z ((Set.Finite.mem_toFinset _).mpr ⟨hz, him.symm.trans him₀⟩)
      linarith
    have hGray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ (primePowerZeta K) (s₀ + t) := fun t ht =>
      hGAn _ (by rw [hqre]; linarith [ht.1]) (by rw [hqre]; linarith [ht.2]) (hray t ht.1)
    have hgdray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ (gdSeries a powerFreq) (s₀ + t) := fun t ht =>
      hgdAn _ (by rw [hqre]; linarith [ht.1])
    have hagreeRay : ∀ t ∈ Ioo 0 T,
        gdSeries a powerFreq (s₀ + t) = primePowerZeta K (s₀ + t) :=
      eqOn_ray_of_eventually (c := 9 / 8 - s₀.re + 1 / 2) (by linarith) (by linarith)
        hgdray hGray (fun t ht => hagreeHigh _ (by rw [hqre]; linarith [ht.1]))
    -- split off the pole
    set c' : ℂ → ℂ := fun z => if z = z₀ then 0 else traceCoeff 3 z with hc'def
    have hc' : ∀ z, ‖c' z‖ ≤ ‖traceCoeff 3 z‖ := fun z => by
      simp only [hc'def]; split_ifs <;> simp
    have hsplit : ∀ t ∈ Ioo 0 T, primePowerZeta K (s₀ + t) =
        -(traceCoeff 3 z₀ * logDeriv riemannZeta (1 + t)) +
          (-traceLogDerivOf c' (s₀ + t) - ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta (s₀ + t)) := by
      intro t ht
      have hsm := summable_traceLogDerivOf_terms hzf (c := traceCoeff 3) (fun _ => le_rfl)
        (s := s₀ + t) (by rw [hqre]; linarith [ht.1]) (by rw [hqre]; linarith [ht.2])
      unfold primePowerZeta traceLogDerivOf
      rw [hsm.tsum_eq_add_tsum_ite z₀]
      have h1 : (s₀ + t) - z₀ = 1 + t := by rw [hs₀def]; ring
      have h2 : ∑' z, (if z = z₀ then 0 else traceCoeff 3 z * logDeriv riemannZeta (s₀ + t - z)) =
          ∑' z, c' z * logDeriv riemannZeta (s₀ + t - z) :=
        tsum_congr fun z => by simp only [hc'def]; split_ifs <;> simp
      rw [h1, h2]
      ring
    set R : ℂ → ℂ := fun s => -traceLogDerivOf c' s - ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s
      with hRdef
    have hs₀ne : s₀ ≠ 1 := fun h => by rw [h] at hs₀1; simp at hs₀1
    have hRcont : ContinuousAt R s₀ := by
      have hp : ∀ z, c' z ≠ 0 → s₀ ≠ 1 + z := by
        intro z hz h
        have hzz : z ≠ z₀ := fun e => hz (by simp [hc'def, e])
        exact hzz (by rw [hs₀def] at h; linear_combination -h)
      have h1 := differentiableAt_traceLogDerivOf hzf hc' hs₀1 (by linarith) hp
      have h2 := differentiableAt_logDeriv_riemannZeta hs₀ne
        (riemannZeta_ne_zero_of_one_le_re hs₀1.le)
      exact (h1.neg.sub (h2.const_mul _)).continuousAt
    have hgdcont : ContinuousAt (gdSeries a powerFreq) s₀ := (hgdAn s₀ (by linarith)).continuousAt
    set H : ℂ → ℂ := fun s => gdSeries a powerFreq s - R s with hHdef
    have hHcont : ContinuousAt H s₀ := hgdcont.sub hRcont
    have hHray : ∀ t ∈ Ioo 0 T, H (s₀ + t) = -(traceCoeff 3 z₀ * logDeriv riemannZeta (1 + t)) := by
      intro t ht
      simp only [hHdef, hRdef]
      rw [hagreeRay t ht, hsplit t ht]
      ring
    -- the pole of `ζ'/ζ` at `1` against continuity
    obtain ⟨δ₁, hδ₁, hδ₁H⟩ := Metric.continuousAt_iff.mp hHcont 1 one_pos
    set A := ‖traceCoeff 3 z₀‖ with hAdef
    have hA : 0 < A := norm_pos_iff.mpr hz₀
    obtain ⟨t, ht0, htδ, htB⟩ := exists_norm_logDeriv_zeta_one_add_gt ((‖H s₀‖ + 1) / A)
      (lt_min hδ₁ (by linarith : (0 : ℝ) < T))
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

/-- The same statement for the orbit correlation `c_B = Re S` of the cubic spline. -/
theorem riemannHypothesis_iff_bddBelow_primePowerDegrees' :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ n : ℕ, IsPrimePow n →
      -K ≤ zetaScalingDatum.orbitCorr splineCycle (Real.log n) := by
  rw [riemannHypothesis_iff_bddBelow_primePowerDegrees]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K / 2, fun n hn => by rw [orbitCorr_eq_re_lagStructure_spline]; linarith [hK n hn]⟩
  · rintro ⟨K, hK⟩
    exact ⟨2 * K, fun n hn => by
      have := hK n hn; rw [orbitCorr_eq_re_lagStructure_spline] at this; linarith⟩

end GaloisForLFunctions.SurfaceOfSpecZ
