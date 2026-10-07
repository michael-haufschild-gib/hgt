import GaloisForLFunctions.RHTower.WeilZetaSquareMoments

/-!
# The averaged `|ζ|²`-weighted boundary inequality

Let `lam = Λ ⋆ a + μ ⋆ f + v` be full-cone Weil-positive (`a`, `f` absolutely convergent past `½`,
`f(1) = 0`, `v` regular with continuation `E` bounded on the critical line). Write
`A(t) = A(½+it)`, `Z(t) = |ζ(½+it)|²`, `θ′ = gammaHardyPhaseRate` and, for `m ≥ 1`, `|c| ≤ 1`,
`W(t) = 1 + c² + 2c cos(t log m) ≥ 0`.

**Theorem** (`exists_averaged_ge`). There are `C, L₀` with
`∫ ω_L W (1 − Re A) Z ≥ −C L` for all `L ≥ L₀`.

**Proof.** The boundary inequality reads, pointwise,
`θ′ (1 − Re A) Z + ½ Im A · Z′ ≥ Re E · Z + Re(F ζ̄)` (`pointwise_ge`).
Multiply by `ω_L W ≥ 0` and integrate over `[L/2, 5L/2]`. The `Z′` term is integrated by parts against
`u = ω_L W Im A`, which vanishes at both ends, so it contributes `−½ ∫ u′ Z` with
`|u′| ≤ U` uniformly (`Im A′` by Cauchy's estimate on discs of radius `δ/2`). Replacing `θ′` by
`½ log L` costs `|θ′ − ½ log L| ≤ 3` on the window. The bounds `∫ ω_L Z = O(L log L)` and
`∫_{L/2}^{5L/2} Z = O(L log L)` then give `½ log L · ∫ ω_L W (1 − Re A) Z ≥ −K L log L`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation

namespace RHTower.WeilZetaSquare

variable {a f v : ℕ → ℝ} {E : ℂ → ℂ} {δ : ℝ}

/-! ## Calculus on the critical line -/

theorem hasDerivAt_linePt (t : ℝ) : HasDerivAt (fun τ : ℝ => linePt τ) I t := by
  have h0 : HasDerivAt (fun τ : ℝ => (τ : ℂ) * I) (1 * I) t :=
    (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I
  have h1 := h0.const_add (1 / 2 : ℂ)
  simpa [linePt] using h1

theorem continuous_linePt : Continuous fun τ : ℝ => linePt τ :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_linePt t).continuousAt

theorem linePt_re (t : ℝ) : (linePt t).re = 1 / 2 := by simp [linePt]

theorem linePt_ne_one (t : ℝ) : linePt t ≠ 1 := by
  intro h; have := congrArg Complex.re h; rw [linePt_re] at this; norm_num at this

/-- `t ↦ ζ′(½+it)` is continuous. -/
theorem continuous_deriv_zeta_line : Continuous fun t : ℝ => deriv riemannZeta (linePt t) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have han : AnalyticAt ℂ riemannZeta (linePt t) :=
    (DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      isOpen_compl_singleton) _ (linePt_ne_one t)
  exact han.deriv.continuousAt.comp continuous_linePt.continuousAt

theorem dilSeries_analyticAt_line (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (t : ℝ) :
    AnalyticAt ℂ (dilSeries a) (linePt t) :=
  (differentiableOn_dilSeries ha).analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by show 1 / 2 - δ < (linePt t).re; rw [linePt_re]; linarith))

theorem hasDerivAt_dilSeries_line (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => dilSeries a (linePt τ)) (deriv (dilSeries a) (linePt t) * I) t :=
  (dilSeries_analyticAt_line hδ ha t).differentiableAt.hasDerivAt.comp t (hasDerivAt_linePt t)

theorem continuous_dilSeries_line (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) :
    Continuous fun t : ℝ => dilSeries a (linePt t) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_dilSeries_line hδ ha t).continuousAt

theorem continuous_deriv_dilSeries_line (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) :
    Continuous fun t : ℝ => deriv (dilSeries a) (linePt t) :=
  continuous_iff_continuousAt.mpr fun t =>
    (dilSeries_analyticAt_line hδ ha t).deriv.continuousAt.comp continuous_linePt.continuousAt

/-- `‖A(s)‖ ≤ Σ ‖term a σ₀ n‖` for `σ₀ ≤ Re s`, `σ₀ ≥ ½ − δ`. -/
theorem norm_dilSeries_le_of_re (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    {σ₀ : ℝ} (hσ₀ : 1 / 2 - δ ≤ σ₀) {s : ℂ} (hs : σ₀ ≤ s.re) :
    ‖dilSeries a s‖ ≤ ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (σ₀ : ℂ) n‖ := by
  have hsum : Summable fun n => ‖LSeries.term (fun n => (a n : ℂ)) (σ₀ : ℂ) n‖ :=
    summable_norm_iff.mpr (summable_of_le_re ha (by simpa using hσ₀))
  have hle : ∀ n, ‖LSeries.term (fun n => (a n : ℂ)) s n‖ ≤
      ‖LSeries.term (fun n => (a n : ℂ)) (σ₀ : ℂ) n‖ :=
    LSeries.norm_term_le_of_re_le_re _ (by simpa using hs)
  exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hsum)).trans
    (Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hsum) hsum)

/-- **Cauchy's estimate on the line**: `‖A′(½+it)‖ ≤ 2 S_δ / δ`. -/
theorem norm_deriv_dilSeries_line_le (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (t : ℝ) :
    ‖deriv (dilSeries a) (linePt t)‖ ≤
      (∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) n‖) / (δ / 2) := by
  have hR : 0 < δ / 2 := by positivity
  have hdiff : DiffContOnCl ℂ (dilSeries a) (Metric.ball (linePt t) (δ / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    intro z hz
    refine ((differentiableOn_dilSeries ha).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_)).differentiableWithinAt
    show 1 / 2 - δ < z.re
    have hz' : ‖z - linePt t‖ ≤ δ / 2 := by rw [← dist_eq_norm]; exact hz
    have hre := abs_re_le_norm (z - linePt t)
    rw [Complex.sub_re, linePt_re] at hre
    have := (abs_le.mp (hre.trans hz')).1
    linarith
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdiff fun z hz => ?_
  refine norm_dilSeries_le_of_re ha le_rfl ?_
  have hz' : ‖z - linePt t‖ = δ / 2 := by rw [← dist_eq_norm]; exact hz
  have hre := abs_re_le_norm (z - linePt t)
  rw [Complex.sub_re, linePt_re, hz'] at hre
  have := (abs_le.mp hre).1
  linarith

/-! ## The pointwise inequality -/

/-- **Pointwise form**: `θ′(1 − Re A)Z − Im A · Im(ζ′ζ̄) ≥ Re E · Z + Re(F ζ̄)`. -/
theorem pointwise_ge (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v)) (t : ℝ) :
    (E (linePt t)).re * zsq t + (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re ≤
      gammaHardyPhaseRate t * (1 - (dilSeries a (linePt t)).re) * zsq t -
        (dilSeries a (linePt t)).im *
          (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).im := by
  have h := re_boundary_ge hδ ha hf hf1 hv hW t
  have hP := re_deriv_mul_conj_line t
  set P := deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t)) with hPdef
  have e : ((dilSeries a (linePt t) - 1) * deriv riemannZeta (linePt t) *
      conj (riemannZeta (linePt t))).re =
      ((dilSeries a (linePt t)).re - 1) * P.re - (dilSeries a (linePt t)).im * P.im := by
    rw [mul_assoc, ← hPdef, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero]
  rw [e, hP] at h
  unfold zsq
  nlinarith [h]

/-! ## The weight and its derivative -/

/-- `W(t) = 1 + c² + 2c cos(t log m)`. -/
def twoPointWeight (c : ℝ) (m : ℕ) (t : ℝ) : ℝ := 1 + c ^ 2 + 2 * c * Real.cos (t * Real.log m)

theorem twoPointWeight_nonneg {c : ℝ} (hc : |c| ≤ 1) (m : ℕ) (t : ℝ) :
    0 ≤ twoPointWeight c m t := by
  unfold twoPointWeight
  have h1 := Real.neg_one_le_cos (t * Real.log m)
  have h2 := Real.cos_le_one (t * Real.log m)
  have hc' := abs_le.mp hc
  nlinarith [sq_nonneg (c + Real.cos (t * Real.log m)), Real.cos_sq_le_one (t * Real.log m)]

theorem twoPointWeight_le {c : ℝ} (hc : |c| ≤ 1) (m : ℕ) (t : ℝ) : twoPointWeight c m t ≤ 4 := by
  unfold twoPointWeight
  have h1 := Real.neg_one_le_cos (t * Real.log m)
  have h2 := Real.cos_le_one (t * Real.log m)
  have hc' := abs_le.mp hc
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 + c),
    mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - c)]

theorem hasDerivAt_twoPointWeight (c : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (twoPointWeight c m)
      (-(2 * c * Real.log m * Real.sin (t * Real.log m))) t := by
  unfold twoPointWeight
  have h : HasDerivAt (fun x : ℝ => Real.cos (x * Real.log m))
      (-Real.sin (t * Real.log m) * Real.log m) t := by
    have h0 : HasDerivAt (fun x : ℝ => x * Real.log m) (Real.log m) t := by
      simpa using (hasDerivAt_id t).mul_const (Real.log m)
    exact (Real.hasDerivAt_cos (t * Real.log m)).comp t h0
  exact ((h.const_mul (2 * c)).const_add (1 + c ^ 2)).congr_deriv (by ring)

theorem hasDerivAt_win (L t : ℝ) : HasDerivAt (win L) (deriv (win L) t) t :=
  ((contDiff_blockWindow L (2 * L) (L / 2)).differentiable (by simp) t).hasDerivAt

theorem continuous_deriv_win (L : ℝ) : Continuous (deriv (win L)) :=
  (contDiff_blockWindow L (2 * L) (L / 2)).continuous_deriv (by simp)

theorem abs_deriv_win_le {L : ℝ} (hL : 0 < L) (t : ℝ) :
    |deriv (win L) t| ≤ 2 * blockWindowConst 1 / L := by
  have h := abs_iteratedDeriv_blockWindow_le 1 L (2 * L) (η := L / 2) (by linarith) t
  rw [iteratedDeriv_one] at h
  calc |deriv (win L) t| ≤ blockWindowConst 1 / (L / 2) ^ 1 := h
    _ = 2 * blockWindowConst 1 / L := by rw [pow_one]; field_simp

theorem win_left {L : ℝ} (hL : 0 < L) : win L (L / 2) = 0 :=
  blockWindow_eq_zero_of_le (by linarith) (by linarith)

theorem win_right {L : ℝ} (hL : 0 < L) : win L (5 * L / 2) = 0 :=
  blockWindow_eq_zero_of_ge (by linarith) (by linarith)

/-! ## The phase rate on the window -/

theorem abs_gammaHardyPhaseRate_sub_half_log_le {L t : ℝ} (hL : 16 ≤ L)
    (ht : t ∈ Icc (L / 2) (5 * L / 2)) : |gammaHardyPhaseRate t - Real.log L / 2| ≤ 3 := by
  have ht8 : 8 ≤ t := by linarith [ht.1]
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have hb := gammaHardyPhaseRate_sub_log_conductor_bound ht0
  have herr : 33 / (16 * t ^ 2) + Real.pi / (2 * t) ≤ 1 := by
    have h1 : 33 / (16 * t ^ 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : Real.pi / (2 * t) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four]
    linarith
  have hlog : |Real.log (t / (2 * Real.pi)) / 2 - Real.log L / 2| ≤ 2 := by
    have e : Real.log (t / (2 * Real.pi)) = Real.log (t / L) + Real.log L - Real.log (2 * Real.pi) := by
      rw [Real.log_div ht0.ne' (by positivity), Real.log_div ht0.ne' hL0.ne']
      ring
    have htL1 : Real.log (t / L) ≤ 1 := by
      rw [← Real.log_exp 1]
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hL0]
      nlinarith [ht.2, Real.exp_one_gt_d9]
    have htL2 : -1 ≤ Real.log (t / L) := by
      have : Real.log (1 / 2) ≤ Real.log (t / L) :=
        Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hL0]; linarith [ht.1])
      have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
      have h3 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith
    have hpi1 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    have hpi2 : Real.log (2 * Real.pi) ≤ 2 := by
      have he : (7 : ℝ) ≤ Real.exp 2 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_gt_d9]
      have hle : Real.log (2 * Real.pi) ≤ Real.log (Real.exp 2) :=
        Real.log_le_log (by positivity) (by nlinarith [Real.pi_lt_d2])
      rwa [Real.log_exp] at hle
    rw [e, abs_le]
    constructor <;> linarith
  calc |gammaHardyPhaseRate t - Real.log L / 2|
      ≤ |gammaHardyPhaseRate t - Real.log (t / (2 * Real.pi)) / 2| +
          |Real.log (t / (2 * Real.pi)) / 2 - Real.log L / 2| := abs_sub_le _ _ _
    _ ≤ 1 + 2 := add_le_add (hb.trans herr) hlog
    _ = 3 := by norm_num

/-! ## Integration by parts -/

/-- `u = ω_L W Im A`. -/
def uFun (a : ℕ → ℝ) (L c : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  win L t * twoPointWeight c m t * (dilSeries a (linePt t)).im

/-- The derivative of `u`. -/
def uDeriv (a : ℕ → ℝ) (L c : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  deriv (win L) t * twoPointWeight c m t * (dilSeries a (linePt t)).im +
    win L t * (-(2 * c * Real.log m * Real.sin (t * Real.log m))) * (dilSeries a (linePt t)).im +
    win L t * twoPointWeight c m t * (deriv (dilSeries a) (linePt t)).re

theorem hasDerivAt_im_dilSeries_line (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => (dilSeries a (linePt τ)).im)
      (deriv (dilSeries a) (linePt t)).re t := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_dilSeries_line hδ ha t)
  simpa [Function.comp_def, Complex.mul_I_im] using h

theorem continuous_twoPointWeight (c : ℝ) (m : ℕ) : Continuous (twoPointWeight c m) := by
  unfold twoPointWeight; fun_prop

theorem hasDerivAt_uFun (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (L c : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (uFun a L c m) (uDeriv a L c m t) t := by
  have h := ((hasDerivAt_win L t).mul (hasDerivAt_twoPointWeight c m t)).mul
    (hasDerivAt_im_dilSeries_line hδ ha t)
  unfold uFun uDeriv
  exact h.congr_deriv (by simp only [Pi.mul_apply]; ring)

theorem continuous_uDeriv (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (L c : ℝ) (m : ℕ) :
    Continuous (uDeriv a L c m) := by
  have hw : Continuous (win L) := (contDiff_blockWindow L (2 * L) (L / 2)).continuous
  have hW := continuous_twoPointWeight c m
  have hA : Continuous fun t : ℝ => (dilSeries a (linePt t)).im :=
    Complex.continuous_im.comp (continuous_dilSeries_line hδ ha)
  have hA' : Continuous fun t : ℝ => (deriv (dilSeries a) (linePt t)).re :=
    Complex.continuous_re.comp (continuous_deriv_dilSeries_line hδ ha)
  have hs : Continuous fun t : ℝ => -(2 * c * Real.log m * Real.sin (t * Real.log m)) := by
    fun_prop
  unfold uDeriv
  exact (((continuous_deriv_win L).mul hW).mul hA).add ((hw.mul hs).mul hA) |>.add
    ((hw.mul hW).mul hA')

theorem continuous_zsq_deriv :
    Continuous fun t : ℝ =>
      -(2 * (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).im) := by
  have h : Continuous fun t : ℝ => deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t)) :=
    continuous_deriv_zeta_line.mul (Complex.continuous_conj.comp continuous_zeta_line)
  exact (continuous_const.mul (Complex.continuous_im.comp h)).neg

/-- **Integration by parts**: `∫ u Z′ = −∫ u′ Z` over `[L/2, 5L/2]`. -/
theorem integral_uFun_mul_deriv (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) {L : ℝ} (hL : 0 < L)
    (c : ℝ) (m : ℕ) :
    ∫ t in (L / 2)..(5 * L / 2), uFun a L c m t *
        -(2 * (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).im) =
      -∫ t in (L / 2)..(5 * L / 2), uDeriv a L c m t * zsq t := by
  have hv : ∀ t, HasDerivAt zsq
      (-(2 * (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).im)) t := by
    intro t
    exact hasDerivAt_normSq_zeta_line t
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ => hasDerivAt_uFun hδ ha L c m t)
    (fun t _ => hv t) ((continuous_uDeriv hδ ha L c m).intervalIntegrable _ _)
    (continuous_zsq_deriv.intervalIntegrable _ _)]
  have h1 : uFun a L c m (5 * L / 2) = 0 := by unfold uFun; rw [win_right hL]; ring
  have h2 : uFun a L c m (L / 2) = 0 := by unfold uFun; rw [win_left hL]; ring
  rw [h1, h2]
  ring

/-! ## Uniform bounds -/

/-- `S_A = Σ ‖term a (1/2) n‖` bounds `A` on the line. -/
theorem norm_dilSeries_line_le (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hδ : 0 < δ) (t : ℝ) :
    ‖dilSeries a (linePt t)‖ ≤ ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖ :=
  norm_dilSeries_le_of_re ha (by linarith) (by rw [linePt_re])

theorem abs_uDeriv_le (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) {L : ℝ} (hL : 16 ≤ L)
    {c : ℝ} (hc : |c| ≤ 1) (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    |uDeriv a L c m t| ≤
      blockWindowConst 1 / 8 * 4 * (∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖) +
        2 * Real.log m * (∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖) +
        4 * ((∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) n‖) / (δ / 2)) := by
  set SA := ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖
  set DA := (∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) n‖) / (δ / 2)
  have hL0 : 0 < L := by linarith
  have hImA : |(dilSeries a (linePt t)).im| ≤ SA :=
    (abs_im_le_norm _).trans (norm_dilSeries_line_le ha hδ t)
  have hDA : |(deriv (dilSeries a) (linePt t)).re| ≤ DA :=
    (abs_re_le_norm _).trans (norm_deriv_dilSeries_line_le hδ ha t)
  have hw0 := blockWindow_nonneg L (2 * L) (L / 2) t
  have hw1 := blockWindow_le_one L (2 * L) (L / 2) t
  have hW0 := twoPointWeight_nonneg hc m t
  have hW1 := twoPointWeight_le hc m t
  have hdw : |deriv (win L) t| ≤ blockWindowConst 1 / 8 := by
    refine (abs_deriv_win_le hL0 t).trans ?_
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    have := blockWindowConst_nonneg 1
    nlinarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hsin : |-(2 * c * Real.log m * Real.sin (t * Real.log m))| ≤ 2 * Real.log m := by
    rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlogm, abs_two]
    have := Real.abs_sin_le_one (t * Real.log m)
    have hc' : |c| * |Real.sin (t * Real.log m)| ≤ 1 :=
      mul_le_one₀ hc (abs_nonneg _) this
    nlinarith [abs_nonneg c, abs_nonneg (Real.sin (t * Real.log m))]
  have hSA0 : 0 ≤ SA := tsum_nonneg fun n => norm_nonneg _
  unfold uDeriv
  have e1 : |deriv (win L) t * twoPointWeight c m t * (dilSeries a (linePt t)).im| ≤
      blockWindowConst 1 / 8 * 4 * SA := by
    rw [abs_mul, abs_mul, abs_of_nonneg hW0]
    have := blockWindowConst_nonneg 1
    gcongr
  have e2 : |win L t * (-(2 * c * Real.log m * Real.sin (t * Real.log m))) *
      (dilSeries a (linePt t)).im| ≤ 2 * Real.log m * SA := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw0]
    calc win L t * |-(2 * c * Real.log m * Real.sin (t * Real.log m))| *
          |(dilSeries a (linePt t)).im| ≤ 1 * (2 * Real.log m) * SA := by gcongr
      _ = 2 * Real.log m * SA := by ring
  have e3 : |win L t * twoPointWeight c m t * (deriv (dilSeries a) (linePt t)).re| ≤ 4 * DA := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hW0]
    calc win L t * twoPointWeight c m t * |(deriv (dilSeries a) (linePt t)).re| ≤ 1 * 4 * DA := by
          gcongr
      _ = 4 * DA := by ring
  calc _ ≤ |deriv (win L) t * twoPointWeight c m t * (dilSeries a (linePt t)).im| +
        |win L t * (-(2 * c * Real.log m * Real.sin (t * Real.log m))) *
          (dilSeries a (linePt t)).im| +
        |win L t * twoPointWeight c m t * (deriv (dilSeries a) (linePt t)).re| := by
        refine (abs_add_le _ _).trans ?_
        exact add_le_add_left (abs_add_le _ _) _ |>.trans_eq (by ring)
    _ ≤ _ := by linarith

/-- `∫ ω_L g = ∫_{L/2}^{5L/2} ω_L g`. -/
theorem integral_win_mul_eq {L : ℝ} (hL : 0 < L) (g : ℝ → ℝ) :
    ∫ t, win L t * g t = ∫ t in (L / 2)..(5 * L / 2), win L t * g t := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
  rw [win_eq_zero hL ht, zero_mul]

/-! ## The averaged inequality -/

/-- `Z′(t) = −2 Im(ζ′ζ̄)`. -/
def zsqDeriv (t : ℝ) : ℝ :=
  -(2 * (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).im)

theorem norm_zeta_line_le (t : ℝ) : ‖riemannZeta (linePt t)‖ ≤ (1 + zsq t) / 2 := by
  have h : zsq t = ‖riemannZeta (linePt t)‖ ^ 2 := by
    unfold zsq; rw [Complex.normSq_eq_norm_sq]
  rw [h]
  nlinarith [sq_nonneg (‖riemannZeta (linePt t)‖ - 1)]

/-- **Pointwise lower bound on the window.** With `R = 1 − Re A`,
`ω W (log L/2) R Z + ½ u Z′ ≥ −ω (K_B Z + 2 S_F)`. -/
theorem pointwise_window_ge (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v))
    {SE : ℝ} (hEb : ∀ t, ‖E (linePt t)‖ ≤ SE) {c : ℝ} (hc : |c| ≤ 1) (m : ℕ)
    {L : ℝ} (hL : 16 ≤ L) {t : ℝ} (ht : t ∈ Icc (L / 2) (5 * L / 2)) :
    -(win L t * ((4 * SE + 2 * (∑' n, ‖LSeries.term (fun n => (f n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖) +
        12 * (1 + ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖)) * zsq t +
        2 * (∑' n, ‖LSeries.term (fun n => (f n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖))) ≤
      win L t * twoPointWeight c m t * (Real.log L / 2) * (1 - (dilSeries a (linePt t)).re) *
          zsq t + 1 / 2 * (uFun a L c m t * zsqDeriv t) := by
  set SA := ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖ with hSA
  set SF := ∑' n, ‖LSeries.term (fun n => (f n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖ with hSF
  have hp := pointwise_ge hδ ha hf hf1 hv hW t
  have hg := abs_gammaHardyPhaseRate_sub_half_log_le hL ht
  have hw0 := blockWindow_nonneg L (2 * L) (L / 2) t
  have hw1 := blockWindow_le_one L (2 * L) (L / 2) t
  have hW0 := twoPointWeight_nonneg hc m t
  have hW1 := twoPointWeight_le hc m t
  have hZ := zsq_nonneg t
  have hReA : |(dilSeries a (linePt t)).re| ≤ SA :=
    (abs_re_le_norm _).trans (norm_dilSeries_line_le ha hδ t)
  have hF : ‖dilSeries f (linePt t)‖ ≤ SF := norm_dilSeries_line_le hf hδ t
  have hE : |(E (linePt t)).re| ≤ SE := (abs_re_le_norm _).trans (hEb t)
  have hFz : |(dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re| ≤
      SF * ((1 + zsq t) / 2) := by
    refine (abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hF (norm_zeta_line_le t) (norm_nonneg _) ((norm_nonneg _).trans hF)
  set g := gammaHardyPhaseRate t
  set R := 1 - (dilSeries a (linePt t)).re with hR
  set φ := win L t * twoPointWeight c m t with hφ
  have hφ0 : 0 ≤ φ := mul_nonneg hw0 hW0
  have hφ4 : φ ≤ 4 * win L t := by
    calc φ ≤ win L t * 4 := mul_le_mul_of_nonneg_left hW1 hw0
      _ = 4 * win L t := by ring
  have hRabs : |R| ≤ 1 + SA := by
    rw [hR]
    calc |1 - (dilSeries a (linePt t)).re| ≤ |1| + |(dilSeries a (linePt t)).re| := abs_sub _ _
      _ ≤ 1 + SA := by rw [abs_one]; linarith
  -- multiply the pointwise inequality by `φ`
  have hmul := mul_le_mul_of_nonneg_left hp hφ0
  -- the `θ′` correction
  have hcorr : φ * ((g - Real.log L / 2) * R * zsq t) ≤ 4 * win L t * (3 * (1 + SA) * zsq t) := by
    have hX : (g - Real.log L / 2) * R ≤ 3 * (1 + SA) := by
      have : |(g - Real.log L / 2) * R| ≤ 3 * (1 + SA) := by
        rw [abs_mul]; exact mul_le_mul hg hRabs (abs_nonneg _) (by norm_num)
      exact (le_abs_self _).trans this
    have hSA0 : 0 ≤ SA := tsum_nonneg fun n => norm_nonneg _
    have h1 : (g - Real.log L / 2) * R * zsq t ≤ 3 * (1 + SA) * zsq t :=
      mul_le_mul_of_nonneg_right hX hZ
    have h2 : φ * ((g - Real.log L / 2) * R * zsq t) ≤ φ * (3 * (1 + SA) * zsq t) :=
      mul_le_mul_of_nonneg_left h1 hφ0
    have h3 : φ * (3 * (1 + SA) * zsq t) ≤ 4 * win L t * (3 * (1 + SA) * zsq t) :=
      mul_le_mul_of_nonneg_right hφ4 (by positivity)
    linarith
  -- the source terms
  have hsrc : -(4 * win L t * (SE * zsq t + SF * ((1 + zsq t) / 2))) ≤
      φ * ((E (linePt t)).re * zsq t +
        (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re) := by
    have h1 : -(SE * zsq t + SF * ((1 + zsq t) / 2)) ≤ (E (linePt t)).re * zsq t +
        (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re := by
      have e1 : -(SE * zsq t) ≤ (E (linePt t)).re * zsq t := by
        have := (abs_le.mp hE).1
        nlinarith
      have e2 := (abs_le.mp hFz).1
      linarith
    have hSE0 : 0 ≤ SE := (norm_nonneg _).trans (hEb t)
    have hSF0 : 0 ≤ SF := tsum_nonneg fun n => norm_nonneg _
    have h2 : 0 ≤ SE * zsq t + SF * ((1 + zsq t) / 2) := by positivity
    have h3 : φ * (-(SE * zsq t + SF * ((1 + zsq t) / 2))) ≥
        -(4 * win L t * (SE * zsq t + SF * ((1 + zsq t) / 2))) := by
      nlinarith [mul_le_mul_of_nonneg_right hφ4 h2]
    linarith [mul_le_mul_of_nonneg_left h1 hφ0]
  -- assemble
  have hu : uFun a L c m t * zsqDeriv t =
      -(2 * (φ * ((dilSeries a (linePt t)).im *
        (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).im))) := by
    unfold uFun zsqDeriv; rw [hφ]; ring
  have hsplit : φ * (g * R * zsq t) =
      φ * (Real.log L / 2) * R * zsq t + φ * ((g - Real.log L / 2) * R * zsq t) := by ring
  rw [hu]
  have hmul' : φ * ((E (linePt t)).re * zsq t +
      (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re) ≤
      φ * (g * R * zsq t) - φ * ((dilSeries a (linePt t)).im *
        (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).im) := by
    rw [← mul_sub]; exact hmul
  nlinarith [hmul', hsplit, hcorr, hsrc]

theorem continuous_uFun (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (L c : ℝ) (m : ℕ) :
    Continuous (uFun a L c m) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_uFun hδ ha L c m t).continuousAt

/-- **The averaged `|ζ|²`-weighted inequality**: `∫ ω_L W (1 − Re A) Z ≥ −K L` for `L ≥ 32`. -/
theorem exists_averaged_ge (hδ : 0 < δ)
    (ha : LSeriesSummable (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ))
    (hf : LSeriesSummable (fun n => (f n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ)) (hf1 : f 1 = 0)
    (hv : RegularPart v E) (hW : WeilPositiveFull (finiteTypeSeq a f v))
    {SE : ℝ} (hEb : ∀ t, ‖E (linePt t)‖ ≤ SE) {c : ℝ} (hc : |c| ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, ∀ {L : ℝ}, 32 ≤ L →
      -(K * L) ≤ ∫ t, win L t * (twoPointWeight c m t * (1 - (dilSeries a (linePt t)).re) *
        zsq t) := by
  obtain ⟨K₀, hK₀, hmom⟩ := exists_momentRe_zero_le
  obtain ⟨K₂, hK₂, hzint⟩ := exists_intervalIntegral_zsq_le
  set SA := ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖ with hSA
  set SF := ∑' n, ‖LSeries.term (fun n => (f n : ℂ)) ((1 / 2 : ℝ) : ℂ) n‖ with hSF
  set KB := 4 * SE + 2 * SF + 12 * (1 + SA) with hKB
  set U := blockWindowConst 1 / 8 * 4 * SA + 2 * Real.log m * SA +
    4 * ((∑' n, ‖LSeries.term (fun n => (a n : ℂ)) ((1 / 2 - δ : ℝ) : ℂ) n‖) / (δ / 2)) with hU
  have hSA0 : 0 ≤ SA := tsum_nonneg fun n => norm_nonneg _
  have hSF0 : 0 ≤ SF := tsum_nonneg fun n => norm_nonneg _
  have hSE0 : 0 ≤ SE := (norm_nonneg _).trans (hEb 0)
  have hKB0 : 0 ≤ KB := by positivity
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (abs_uDeriv_le hδ ha (L := 16) le_rfl hc m hm 0)
  refine ⟨2 * (KB * K₀ + U * K₂ / 2 + 4 * SF), fun {L} hL => ?_⟩
  have hL0 : 0 < L := by linarith
  have hL16 : 16 ≤ L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  rw [integral_win_mul_eq hL0]
  -- continuity
  have cw : Continuous (win L) := (contDiff_blockWindow L (2 * L) (L / 2)).continuous
  have cW := continuous_twoPointWeight c m
  have cR : Continuous fun t : ℝ => 1 - (dilSeries a (linePt t)).re :=
    continuous_const.sub (Complex.continuous_re.comp (continuous_dilSeries_line hδ ha))
  have cZ := continuous_zsq
  have cu := continuous_uFun hδ ha L c m
  have cZ' : Continuous zsqDeriv := continuous_zsq_deriv
  have cud := continuous_uDeriv hδ ha L c m
  set a' := L / 2
  set b' := 5 * L / 2
  have hab : a' ≤ b' := by simp only [a', b']; linarith
  -- integrate the pointwise inequality
  have cB : Continuous fun t => -(win L t * (KB * zsq t + 2 * SF)) :=
    (cw.mul ((continuous_const.mul cZ).add continuous_const)).neg
  have cX : Continuous fun t => win L t * twoPointWeight c m t * (Real.log L / 2) *
      (1 - (dilSeries a (linePt t)).re) * zsq t + 1 / 2 * (uFun a L c m t * zsqDeriv t) :=
    ((((cw.mul cW).mul continuous_const).mul cR).mul cZ).add (continuous_const.mul (cu.mul cZ'))
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab (cB.intervalIntegrable a' b')
    (cX.intervalIntegrable a' b')
    (fun t ht => pointwise_window_ge hδ ha hf hf1 hv hW hEb hc m hL16 ht)
  -- the left side
  have hleft : ∫ t in a'..b', -(win L t * (KB * zsq t + 2 * SF)) =
      -(KB * ∫ t in a'..b', win L t * zsq t) - 2 * SF * ∫ t in a'..b', win L t := by
    have e : (fun t => -(win L t * (KB * zsq t + 2 * SF))) =
        fun t => -(KB * (win L t * zsq t)) - 2 * SF * win L t := by funext t; ring
    have i1 : IntervalIntegrable (fun t => -(KB * (win L t * zsq t))) volume a' b' :=
      ((cw.mul cZ).const_mul KB).neg.intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => 2 * SF * win L t) volume a' b' :=
      (cw.const_mul _).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- the right side
  set I := ∫ t in a'..b', win L t * (twoPointWeight c m t * (1 - (dilSeries a (linePt t)).re) *
    zsq t) with hI
  have hright : ∫ t in a'..b', (win L t * twoPointWeight c m t * (Real.log L / 2) *
      (1 - (dilSeries a (linePt t)).re) * zsq t + 1 / 2 * (uFun a L c m t * zsqDeriv t)) =
      Real.log L / 2 * I + 1 / 2 * ∫ t in a'..b', uFun a L c m t * zsqDeriv t := by
    have e : (fun t => win L t * twoPointWeight c m t * (Real.log L / 2) *
        (1 - (dilSeries a (linePt t)).re) * zsq t + 1 / 2 * (uFun a L c m t * zsqDeriv t)) =
        fun t => Real.log L / 2 * (win L t * (twoPointWeight c m t *
          (1 - (dilSeries a (linePt t)).re) * zsq t)) + 1 / 2 * (uFun a L c m t * zsqDeriv t) := by
      funext t; ring
    have i3 : IntervalIntegrable (fun t => Real.log L / 2 * (win L t * (twoPointWeight c m t *
        (1 - (dilSeries a (linePt t)).re) * zsq t))) volume a' b' :=
      ((cw.mul ((cW.mul cR).mul cZ)).const_mul _).intervalIntegrable _ _
    have i4 : IntervalIntegrable (fun t => 1 / 2 * (uFun a L c m t * zsqDeriv t)) volume a' b' :=
      ((cu.mul cZ').const_mul _).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_add i3 i4,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hIBP : ∫ t in a'..b', uFun a L c m t * zsqDeriv t =
      -∫ t in a'..b', uDeriv a L c m t * zsq t := integral_uFun_mul_deriv hδ ha hL0 c m
  have hUb : -(U * ∫ t in a'..b', zsq t) ≤ ∫ t in a'..b', uDeriv a L c m t * zsq t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_mono_on hab ((cZ.const_mul U).neg.intervalIntegrable _ _)
      ((cud.mul cZ).intervalIntegrable _ _) fun t _ => ?_
    have hb := abs_uDeriv_le hδ ha hL16 hc m hm t
    have hz := zsq_nonneg t
    have := (abs_le.mp hb).1
    nlinarith
  -- the window integrals
  have hwz : ∫ t in a'..b', win L t * zsq t ≤ K₀ * L * Real.log L := by
    have h := hmom hL16
    unfold momentRe at h
    simp only [zero_mul, Real.cos_zero, mul_one] at h
    rwa [integral_win_mul_eq hL0] at h
  have hw : ∫ t in a'..b', win L t ≤ 2 * L := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hab (cw.intervalIntegrable a' b')
      ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).intervalIntegrable a' b')
      fun t _ => blockWindow_le_one L (2 * L) (L / 2) t
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
    simp only [a', b'] at h
    linarith
  have hz := hzint hL
  -- conclude
  rw [hleft, hright, hIBP] at hmono
  have hLlog : L ≤ L * Real.log L := le_mul_of_one_le_right hL0.le hlogL
  have hkey : -((KB * K₀ + U * K₂ / 2 + 4 * SF) * (L * Real.log L)) ≤ Real.log L / 2 * I := by
    have h1 : KB * ∫ t in a'..b', win L t * zsq t ≤ KB * (K₀ * L * Real.log L) :=
      mul_le_mul_of_nonneg_left hwz hKB0
    have h2 : 2 * SF * ∫ t in a'..b', win L t ≤ 2 * SF * (2 * L) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have h3 : U * ∫ t in a'..b', zsq t ≤ U * (K₂ * L * Real.log L) :=
      mul_le_mul_of_nonneg_left hz hU0
    have h4 : 4 * SF * L ≤ 4 * SF * (L * Real.log L) := mul_le_mul_of_nonneg_left hLlog (by positivity)
    nlinarith
  have hlog2 : 0 < Real.log L / 2 := by linarith
  have hfinal : -(2 * (KB * K₀ + U * K₂ / 2 + 4 * SF) * L) * (Real.log L / 2) ≤ I * (Real.log L / 2) := by
    nlinarith
  have := le_of_mul_le_mul_right hfinal hlog2
  linarith

end RHTower.WeilZetaSquare
