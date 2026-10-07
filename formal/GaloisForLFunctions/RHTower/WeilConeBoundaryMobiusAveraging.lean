import GaloisForLFunctions.RHTower.WeilZetaSquareDilationRigidity
import GaloisForLFunctions.RHTower.WeilConeBoundaryDilationLogAveraging

/-!
# The `|ζ|²`-weighted boundary inequality in the boundary class

Let `a, f, v : ℕ → ℝ` with `Σ |a(n)| n^{−½} (1 + log n) < ∞`, `Σ |f(n)| n^{−½} < ∞`,
`Σ |v(n)| n^{−½} < ∞`, `f(1) = 0` and `v(0) = v(1) = 0`. Write `A`, `F`, `V` for their Dirichlet
series. All three converge absolutely on `Re s ≥ ½`, and the critical line may be a natural
boundary. Suppose `λ = Λ ⋆ a + μ ⋆ f + v` is full-cone Weil-positive, with Herglotz
continuation `Φ`.

* **Master identity** (`zeta_mul_eq_boundary`). On `Re s > ½`, `s ≠ 1`:
  `ζ (Φ − G − 1/(s − 1) + V) = A ζ′ − F`. Also `A(1) = 1` (`dilSeries_one_eq_one_boundary`).
* **Boundary inequality** (`re_boundary_ge_boundary`). For every real `t`, at `s = ½ + it`:
  `Re V(s) |ζ(s)|² + Re(F(s) ζ̄(s)) ≤ Re((A(s) − 1) ζ′(s) ζ̄(s))`.
  The numerator `H = Φ ζ` is continuous on the closed half-plane `Re s ≥ ½`, and
  `Re(H ζ̄) = |ζ|² Re Φ ≥ 0` inside it. The weight `|ζ|²` removes every zero, so no division by
  `ζ` occurs.
* **Averaged inequality** (`exists_averaged_ge_boundary`). Fix `|c| ≤ 1`, `m ≥ 1` and put
  `W = 1 + c² + 2c cos(t log m)`. Then `∫ ω_L W (1 − Re A) |ζ|² ≥ −K L` for `L ≥ 32`.
  The term `Im A · (|ζ|²)′` is integrated by parts. The height derivative of `A(½+it)` is
  `−i Σ a(n) log n · n^{−½−it}`, which is bounded by the log moment, so no analyticity across the
  line is needed.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation
open RHTower.WeilZetaSquare

namespace RHTower.WeilBoundaryMobius

open RHTower.WeilBoundaryDilation (HalfSummable BoundaryRegular regSeries)

variable {a f v : ℕ → ℝ}

/-! ## The master identity -/

/-- On `Re s > 1`: `Σ λ(n) n^{−s} = −A ζ′/ζ + F/ζ + V`. -/
theorem LSeries_finiteTypeSeq_boundary (ha : HalfSummable a) (hf : HalfSummable f)
    (hv : BoundaryRegular v) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (finiteTypeSeq a f v n : ℂ)) s =
      -(dilSeries a s * deriv riemannZeta s / riemannZeta s) + dilSeries f s / riemannZeta s +
        regSeries v s := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hμ := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hA : LSeriesSummable (fun n => (a n : ℂ)) s :=
    WeilBoundaryDilation.summable_of_half ha (by linarith)
  have hF : LSeriesSummable (fun n => (f n : ℂ)) s :=
    WeilBoundaryDilation.summable_of_half hf (by linarith)
  have hV : LSeriesSummable (fun n => (v n : ℂ)) s :=
    hv.summable.of_re_le_re (by norm_num; linarith)
  rw [finiteTypeSeq_cast, LSeries_add ((hΛ.convolution hA).add (hμ.convolution hF)) hV,
    LSeries_add (hΛ.convolution hA) (hμ.convolution hF), LSeries_convolution' hΛ hA,
    LSeries_convolution' hμ hF, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hμζ : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = 1 / riemannZeta s := by
    have h := LSeries_one_mul_Lseries_moebius hs
    rw [LSeries_one_eq_riemannZeta hs] at h
    field_simp
    linear_combination h
  rw [hμζ]
  field_simp

/-- **The master identity** on `Re s > ½`. -/
theorem master_identity_boundary (ha : HalfSummable a) (hf : HalfSummable f) (hf1 : f 1 = 0)
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v)) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    masterLeft hW (regSeries v) s = WeilZetaSquare.masterRight a f s := by
  have hpre : IsPreconnected {s : ℂ | 1 / 2 < s.re} :=
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2U : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  refine (analyticOnNhd_masterLeft hW
    (WeilBoundaryDilation.differentiableOn_regSeries hv)).eqOn_of_preconnected_of_eventuallyEq
    (fun z hz => analyticOnNhd_masterRight ha hf z
      (by simp only [mem_setOf_eq] at hz ⊢; linarith)) hpre h2U ?_ hs
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hV] with z hz
  have hz : 1 < z.re := hz
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  unfold masterLeft WeilZetaSquare.masterRight
  rw [weilContinuation_eq hW hz, weilFunction, lamC_finiteTypeSeq a hf1 hv.zero hv.one,
    LSeries_finiteTypeSeq_boundary ha hf hv hz, ← sq_mul_deriv_riemannZeta hz1,
    (zetaResidueUnit_eventuallyEq hz1).eq_of_nhds]
  unfold zetaArchimedeanDatum
  field_simp
  ring

/-- **Off `s = 1`**: `ζ (Φ − G − 1/(s − 1) + V) = A ζ′ − F`. -/
theorem zeta_mul_eq_boundary (ha : HalfSummable a) (hf : HalfSummable f) (hf1 : f 1 = 0)
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v)) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * (weilContinuation hW s - zetaArchimedeanDatum s - 1 / (s - 1) +
      regSeries v s) = dilSeries a s * deriv riemannZeta s - dilSeries f s := by
  have h := master_identity_boundary ha hf hf1 hv hW hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold masterLeft WeilZetaSquare.masterRight at h
  rw [← sq_mul_deriv_riemannZeta hs1, (zetaResidueUnit_eventuallyEq hs1).eq_of_nhds] at h
  have h2 : (s - 1) ^ 2 * (riemannZeta s *
      (weilContinuation hW s - zetaArchimedeanDatum s - 1 / (s - 1) + regSeries v s)) =
      (s - 1) ^ 2 * (dilSeries a s * deriv riemannZeta s - dilSeries f s) := by
    have e : (s - 1) ^ 2 * (riemannZeta s *
        (weilContinuation hW s - zetaArchimedeanDatum s - 1 / (s - 1) + regSeries v s)) =
        (s - 1) * riemannZeta s *
          ((s - 1) * (weilContinuation hW s - zetaArchimedeanDatum s + regSeries v s) - 1) := by
      field_simp; ring
    rw [e, h]; ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hs1') h2

/-- **Normalization**: `A(1) = Σ a(n)/n = 1`. -/
theorem dilSeries_one_eq_one_boundary (ha : HalfSummable a) (hf : HalfSummable f)
    (hf1 : f 1 = 0) (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v)) :
    dilSeries a 1 = 1 := by
  have h := master_identity_boundary ha hf hf1 hv hW (s := 1) (by norm_num)
  unfold masterLeft WeilZetaSquare.masterRight at h
  simp only [sub_self, zero_mul, zetaResidueUnit_one, zero_sub, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_neg, mul_one] at h
  linear_combination h

/-! ## The boundary numerator on the closed half-plane -/

theorem weilContinuation_mul_zeta_boundary (ha : HalfSummable a) (hf : HalfSummable f)
    (hf1 : f 1 = 0) (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v))
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    weilContinuation hW s * riemannZeta s = boundaryNumerator a f (regSeries v) s := by
  have h := zeta_mul_eq_boundary ha hf hf1 hv hW hs hs1
  unfold boundaryNumerator
  linear_combination h

/-- `Re(H ζ̄) = |ζ|² Re Φ ≥ 0` on `Re s > ½`. -/
theorem re_boundaryNumerator_mul_conj_nonneg_boundary (ha : HalfSummable a)
    (hf : HalfSummable f) (hf1 : f 1 = 0) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    0 ≤ (boundaryNumerator a f (regSeries v) s * conj (riemannZeta s)).re := by
  rw [← weilContinuation_mul_zeta_boundary ha hf hf1 hv hW hs hs1, mul_assoc, Complex.mul_conj,
    Complex.re_mul_ofReal]
  exact mul_nonneg (re_weilContinuation_nonneg hW hs) (Complex.normSq_nonneg _)

theorem continuousWithinAt_boundaryNumerator_line (ha : HalfSummable a) (hf : HalfSummable f)
    (hv : BoundaryRegular v) (t : ℝ) :
    ContinuousWithinAt (boundaryNumerator a f (regSeries v)) {s : ℂ | 1 / 2 ≤ s.re}
      (linePt t) := by
  have hre := linePt_re t
  have hs1 : linePt t ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hmem : linePt t ∈ {s : ℂ | 1 / 2 ≤ s.re} := by
    show (1 / 2 : ℝ) ≤ (linePt t).re; rw [hre]
  have hG : ContinuousAt zetaArchimedeanDatum (linePt t) :=
    (differentiableAt_zetaArchimedeanDatum (by rw [hre]; norm_num)).continuousAt
  have hinv : ContinuousAt (fun s : ℂ => 1 / (s - 1)) (linePt t) :=
    continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hs1)
  have hZan : AnalyticAt ℂ riemannZeta (linePt t) := analyticOn_riemannZeta (linePt t) hs1
  have hA := WeilBoundaryDilation.continuousOn_dilSeries ha (linePt t) hmem
  have hF := WeilBoundaryDilation.continuousOn_dilSeries hf (linePt t) hmem
  have hV := WeilBoundaryDilation.continuousOn_regSeries hv (linePt t) hmem
  unfold boundaryNumerator
  exact ((((hG.add hinv).continuousWithinAt.sub hV).mul
    hZan.continuousAt.continuousWithinAt).add
      (hA.mul hZan.deriv.continuousAt.continuousWithinAt)).sub hF

/-- **The boundary inequality before simplification**: `Re(H ζ̄) ≥ 0` on the critical line. -/
theorem re_boundaryNumerator_mul_conj_line_nonneg_boundary (ha : HalfSummable a)
    (hf : HalfSummable f) (hf1 : f 1 = 0) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) (t : ℝ) :
    0 ≤ (boundaryNumerator a f (regSeries v) (linePt t) * conj (riemannZeta (linePt t))).re := by
  have hre := linePt_re t
  have hs1 : linePt t ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  obtain ⟨path, hpath⟩ : ∃ path : ℝ → ℂ, path = fun σ : ℝ => (σ : ℂ) + (t : ℂ) * I := ⟨_, rfl⟩
  have hpre : ∀ σ, (path σ).re = σ := fun σ => by simp [hpath]
  have hpath0 : path (1 / 2) = linePt t := by simp [hpath, linePt]
  have hpc : Continuous path := by rw [hpath]; fun_prop
  have hlim : Tendsto path (𝓝[>] (1 / 2)) (𝓝[{s : ℂ | 1 / 2 ≤ s.re}] (linePt t)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · rw [← hpath0]; exact hpc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      show (1 / 2 : ℝ) ≤ (path σ).re
      rw [hpre]; exact le_of_lt hσ
  have hfun : ContinuousWithinAt
      (fun s => (boundaryNumerator a f (regSeries v) s * conj (riemannZeta s)).re)
      {s : ℂ | 1 / 2 ≤ s.re} (linePt t) :=
    Complex.continuous_re.continuousAt.comp_continuousWithinAt
      ((continuousWithinAt_boundaryNumerator_line ha hf hv t).mul
        (Complex.continuous_conj.continuousAt.comp_continuousWithinAt
          (differentiableAt_riemannZeta hs1).continuousAt.continuousWithinAt))
  refine ge_of_tendsto (hfun.tendsto.comp hlim) ?_
  have hev : ∀ᶠ σ in 𝓝[>] (1 / 2 : ℝ), σ < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hev] with σ hσ hσ1
  have hσ' : (1 / 2 : ℝ) < σ := hσ
  have hne : path σ ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hpre] at this; simp at this; linarith
  exact re_boundaryNumerator_mul_conj_nonneg_boundary ha hf hf1 hv hW
    (by rw [hpre]; exact hσ') hne

/-- **The boundary inequality**: at `s = ½ + it`,
`Re V(s) |ζ(s)|² + Re(F(s) ζ̄(s)) ≤ Re((A(s) − 1) ζ′(s) ζ̄(s))`. -/
theorem re_boundary_ge_boundary (ha : HalfSummable a) (hf : HalfSummable f) (hf1 : f 1 = 0)
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v)) (t : ℝ) :
    (regSeries v (linePt t)).re * Complex.normSq (riemannZeta (linePt t)) +
        (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re ≤
      ((dilSeries a (linePt t) - 1) * deriv riemannZeta (linePt t) *
        conj (riemannZeta (linePt t))).re := by
  have h := re_boundaryNumerator_mul_conj_line_nonneg_boundary ha hf hf1 hv hW t
  have hfe := re_datum_normSq_add_deriv_mul_conj t
  obtain ⟨s, hs⟩ : ∃ s, s = linePt t := ⟨_, rfl⟩
  rw [← hs] at h hfe ⊢
  have hsplit : boundaryNumerator a f (regSeries v) s * conj (riemannZeta s) =
      ((zetaArchimedeanDatum s + 1 / (s - 1)) * (riemannZeta s * conj (riemannZeta s)) +
        deriv riemannZeta s * conj (riemannZeta s)) +
      (dilSeries a s - 1) * deriv riemannZeta s * conj (riemannZeta s) -
      regSeries v s * ((Complex.normSq (riemannZeta s) : ℝ) : ℂ) -
      dilSeries f s * conj (riemannZeta s) := by
    unfold boundaryNumerator
    rw [← Complex.mul_conj]
    ring
  rw [hsplit, Complex.sub_re, Complex.sub_re, Complex.add_re, hfe, Complex.re_mul_ofReal] at h
  linarith

/-- **Pointwise form**: `θ′(1 − Re A)Z − Im A · Im(ζ′ζ̄) ≥ Re V · Z + Re(F ζ̄)`. -/
theorem pointwise_ge_boundary (ha : HalfSummable a) (hf : HalfSummable f) (hf1 : f 1 = 0)
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v)) (t : ℝ) :
    (regSeries v (linePt t)).re * zsq t +
        (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re ≤
      gammaHardyPhaseRate t * (1 - (dilSeries a (linePt t)).re) * zsq t -
        (dilSeries a (linePt t)).im *
          (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).im := by
  have h := re_boundary_ge_boundary ha hf hf1 hv hW t
  have hP := re_deriv_mul_conj_line t
  obtain ⟨P, hPdef⟩ : ∃ P, P = deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t)) :=
    ⟨_, rfl⟩
  rw [← hPdef] at hP ⊢
  have e : ((dilSeries a (linePt t) - 1) * deriv riemannZeta (linePt t) *
      conj (riemannZeta (linePt t))).re =
      ((dilSeries a (linePt t)).re - 1) * P.re - (dilSeries a (linePt t)).im * P.im := by
    rw [mul_assoc, ← hPdef, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero]
  rw [e, hP] at h
  unfold zsq
  nlinarith [h]

/-! ## Calculus on the line -/

/-- The derivative of `u = ω_L W Im A` along the critical line. -/
def uDerivLine (a : ℕ → ℝ) (L c : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  deriv (win L) t * twoPointWeight c m t * (dilSeries a (linePt t)).im +
    win L t * (-(2 * c * Real.log m * Real.sin (t * Real.log m))) * (dilSeries a (linePt t)).im +
    win L t * twoPointWeight c m t * (WeilBoundaryDilation.lineDeriv a t).im

/-- The log moment `Σ |a(n)| log n · n^{−½} < ∞`. -/
abbrev LogHalfSummable (a : ℕ → ℝ) : Prop :=
  LSeriesSummable (LSeries.logMul fun n => (a n : ℂ)) (1 / 2)

theorem hasDerivAt_im_dilSeries_line_boundary (ha : HalfSummable a) (hla : LogHalfSummable a)
    (t : ℝ) :
    HasDerivAt (fun τ : ℝ => (dilSeries a (linePt τ)).im)
      (WeilBoundaryDilation.lineDeriv a t).im t := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
    (WeilBoundaryDilation.hasDerivAt_lineSeries ha hla t)
  simpa [Function.comp_def] using h

theorem hasDerivAt_uFun_boundary (ha : HalfSummable a) (hla : LogHalfSummable a) (L c : ℝ)
    (m : ℕ) (t : ℝ) : HasDerivAt (uFun a L c m) (uDerivLine a L c m t) t := by
  have h := ((hasDerivAt_win L t).mul (hasDerivAt_twoPointWeight c m t)).mul
    (hasDerivAt_im_dilSeries_line_boundary ha hla t)
  unfold uFun uDerivLine
  exact h.congr_deriv (by simp only [Pi.mul_apply]; ring)

theorem continuous_uFun_boundary (ha : HalfSummable a) (hla : LogHalfSummable a) (L c : ℝ)
    (m : ℕ) : Continuous (uFun a L c m) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_uFun_boundary ha hla L c m t).continuousAt

theorem continuous_uDerivLine (ha : HalfSummable a) (hla : LogHalfSummable a) (L c : ℝ)
    (m : ℕ) : Continuous (uDerivLine a L c m) := by
  have hw : Continuous (win L) := (contDiff_blockWindow L (2 * L) (L / 2)).continuous
  have hW := continuous_twoPointWeight c m
  have hA : Continuous fun t : ℝ => (dilSeries a (linePt t)).im :=
    Complex.continuous_im.comp (WeilBoundaryDilation.continuous_lineSeries ha)
  have hA' : Continuous fun t : ℝ => (WeilBoundaryDilation.lineDeriv a t).im :=
    Complex.continuous_im.comp (WeilBoundaryDilation.continuous_lineDeriv hla)
  have hs : Continuous fun t : ℝ => -(2 * c * Real.log m * Real.sin (t * Real.log m)) := by
    fun_prop
  unfold uDerivLine
  exact (((continuous_deriv_win L).mul hW).mul hA).add ((hw.mul hs).mul hA) |>.add
    ((hw.mul hW).mul hA')

/-- **Integration by parts**: `∫ u Z′ = −∫ u′ Z` over `[L/2, 5L/2]`. -/
theorem integral_uFun_mul_deriv_boundary (ha : HalfSummable a) (hla : LogHalfSummable a)
    {L : ℝ} (hL : 0 < L) (c : ℝ) (m : ℕ) :
    ∫ t in (L / 2)..(5 * L / 2), uFun a L c m t * zsqDeriv t =
      -∫ t in (L / 2)..(5 * L / 2), uDerivLine a L c m t * zsq t := by
  have hv : ∀ t, HasDerivAt zsq (zsqDeriv t) t := fun t => hasDerivAt_normSq_zeta_line t
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => hasDerivAt_uFun_boundary ha hla L c m t) (fun t _ => hv t)
    ((continuous_uDerivLine ha hla L c m).intervalIntegrable _ _)
    (continuous_zsq_deriv.intervalIntegrable _ _)]
  have h1 : uFun a L c m (5 * L / 2) = 0 := by unfold uFun; rw [win_right hL]; ring
  have h2 : uFun a L c m (L / 2) = 0 := by unfold uFun; rw [win_left hL]; ring
  rw [h1, h2]
  ring

/-! ## Uniform bounds on the line -/

/-- `S_A = Σ ‖a(n) n^{−½}‖`. -/
abbrev halfMass (a : ℕ → ℝ) : ℝ := ∑' n, ‖LSeries.term (fun n => (a n : ℂ)) (1 / 2) n‖

/-- `D_A = Σ ‖a(n) log n · n^{−½}‖`. -/
abbrev logHalfMass (a : ℕ → ℝ) : ℝ :=
  ∑' n, ‖LSeries.term (LSeries.logMul fun n => (a n : ℂ)) (1 / 2) n‖

theorem halfMass_nonneg (a : ℕ → ℝ) : 0 ≤ halfMass a := tsum_nonneg fun _ => norm_nonneg _

theorem norm_dilSeries_line_le_boundary (ha : HalfSummable a) (t : ℝ) :
    ‖dilSeries a (linePt t)‖ ≤ halfMass a :=
  WeilBoundaryDilation.norm_LSeries_linePt_le ha.half t

theorem norm_lineDeriv_le (hla : LogHalfSummable a) (t : ℝ) :
    ‖WeilBoundaryDilation.lineDeriv a t‖ ≤ logHalfMass a := by
  unfold WeilBoundaryDilation.lineDeriv
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact WeilBoundaryDilation.norm_LSeries_linePt_le hla t

theorem abs_uDerivLine_le (ha : HalfSummable a) (hla : LogHalfSummable a) {L : ℝ}
    (hL : 16 ≤ L) {c : ℝ} (hc : |c| ≤ 1) (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    |uDerivLine a L c m t| ≤ blockWindowConst 1 / 8 * 4 * halfMass a +
      2 * Real.log m * halfMass a + 4 * logHalfMass a := by
  set SA := halfMass a
  set DA := logHalfMass a
  have hL0 : 0 < L := by linarith
  have hImA : |(dilSeries a (linePt t)).im| ≤ SA :=
    (abs_im_le_norm _).trans (norm_dilSeries_line_le_boundary ha t)
  have hDA : |(WeilBoundaryDilation.lineDeriv a t).im| ≤ DA :=
    (abs_im_le_norm _).trans (norm_lineDeriv_le hla t)
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
  unfold uDerivLine
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
  have e3 : |win L t * twoPointWeight c m t * (WeilBoundaryDilation.lineDeriv a t).im| ≤
      4 * DA := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hW0]
    calc win L t * twoPointWeight c m t * |(WeilBoundaryDilation.lineDeriv a t).im| ≤
          1 * 4 * DA := by
          gcongr
      _ = 4 * DA := by ring
  calc _ ≤ |deriv (win L) t * twoPointWeight c m t * (dilSeries a (linePt t)).im| +
        |win L t * (-(2 * c * Real.log m * Real.sin (t * Real.log m))) *
          (dilSeries a (linePt t)).im| +
        |win L t * twoPointWeight c m t * (WeilBoundaryDilation.lineDeriv a t).im| := by
        refine (abs_add_le _ _).trans ?_
        exact add_le_add_left (abs_add_le _ _) _ |>.trans_eq (by ring)
    _ ≤ _ := by linarith

/-! ## The averaged inequality -/

/-- **Pointwise lower bound on the window.** With `R = 1 − Re A`,
`ω W (log L/2) R Z + ½ u Z′ ≥ −ω (K_B Z + 2 S_F)`. -/
theorem pointwise_window_ge_boundary (ha : HalfSummable a) (hf : HalfSummable f)
    (hf1 : f 1 = 0) (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v))
    {c : ℝ} (hc : |c| ≤ 1) (m : ℕ) {L : ℝ} (hL : 16 ≤ L) {t : ℝ}
    (ht : t ∈ Icc (L / 2) (5 * L / 2)) :
    -(win L t * ((4 * halfMass v + 2 * halfMass f + 12 * (1 + halfMass a)) * zsq t +
        2 * halfMass f)) ≤
      win L t * twoPointWeight c m t * (Real.log L / 2) * (1 - (dilSeries a (linePt t)).re) *
          zsq t + 1 / 2 * (uFun a L c m t * zsqDeriv t) := by
  set SA := halfMass a with hSA
  set SF := halfMass f with hSF
  set SE := halfMass v with hSE
  have hp := pointwise_ge_boundary ha hf hf1 hv hW t
  have hg := abs_gammaHardyPhaseRate_sub_half_log_le hL ht
  have hw0 := blockWindow_nonneg L (2 * L) (L / 2) t
  have hW0 := twoPointWeight_nonneg hc m t
  have hW1 := twoPointWeight_le hc m t
  have hZ := zsq_nonneg t
  have hReA : |(dilSeries a (linePt t)).re| ≤ SA :=
    (abs_re_le_norm _).trans (norm_dilSeries_line_le_boundary ha t)
  have hF : ‖dilSeries f (linePt t)‖ ≤ SF := norm_dilSeries_line_le_boundary hf t
  have hE : |(regSeries v (linePt t)).re| ≤ SE :=
    (abs_re_le_norm _).trans (WeilBoundaryDilation.norm_LSeries_linePt_le hv.summable t)
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
  have hmul := mul_le_mul_of_nonneg_left hp hφ0
  have hcorr : φ * ((g - Real.log L / 2) * R * zsq t) ≤ 4 * win L t * (3 * (1 + SA) * zsq t) := by
    have hX : (g - Real.log L / 2) * R ≤ 3 * (1 + SA) := by
      have : |(g - Real.log L / 2) * R| ≤ 3 * (1 + SA) := by
        rw [abs_mul]; exact mul_le_mul hg hRabs (abs_nonneg _) (by norm_num)
      exact (le_abs_self _).trans this
    have hSA0 : 0 ≤ SA := halfMass_nonneg a
    have h1 : (g - Real.log L / 2) * R * zsq t ≤ 3 * (1 + SA) * zsq t :=
      mul_le_mul_of_nonneg_right hX hZ
    have h2 : φ * ((g - Real.log L / 2) * R * zsq t) ≤ φ * (3 * (1 + SA) * zsq t) :=
      mul_le_mul_of_nonneg_left h1 hφ0
    have h3 : φ * (3 * (1 + SA) * zsq t) ≤ 4 * win L t * (3 * (1 + SA) * zsq t) :=
      mul_le_mul_of_nonneg_right hφ4 (by positivity)
    linarith
  have hsrc : -(4 * win L t * (SE * zsq t + SF * ((1 + zsq t) / 2))) ≤
      φ * ((regSeries v (linePt t)).re * zsq t +
        (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re) := by
    have h1 : -(SE * zsq t + SF * ((1 + zsq t) / 2)) ≤ (regSeries v (linePt t)).re * zsq t +
        (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re := by
      have e1 : -(SE * zsq t) ≤ (regSeries v (linePt t)).re * zsq t := by
        have := (abs_le.mp hE).1
        nlinarith
      have e2 := (abs_le.mp hFz).1
      linarith
    have hSE0 : 0 ≤ SE := halfMass_nonneg v
    have hSF0 : 0 ≤ SF := halfMass_nonneg f
    have h2 : 0 ≤ SE * zsq t + SF * ((1 + zsq t) / 2) := by positivity
    have h3 : φ * (-(SE * zsq t + SF * ((1 + zsq t) / 2))) ≥
        -(4 * win L t * (SE * zsq t + SF * ((1 + zsq t) / 2))) := by
      nlinarith [mul_le_mul_of_nonneg_right hφ4 h2]
    linarith [mul_le_mul_of_nonneg_left h1 hφ0]
  have hu : uFun a L c m t * zsqDeriv t =
      -(2 * (φ * ((dilSeries a (linePt t)).im *
        (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).im))) := by
    unfold uFun zsqDeriv; rw [hφ]; ring
  have hsplit : φ * (g * R * zsq t) =
      φ * (Real.log L / 2) * R * zsq t + φ * ((g - Real.log L / 2) * R * zsq t) := by ring
  rw [hu]
  have hmul' : φ * ((regSeries v (linePt t)).re * zsq t +
      (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re) ≤
      φ * (g * R * zsq t) - φ * ((dilSeries a (linePt t)).im *
        (deriv riemannZeta (linePt t) * conj (riemannZeta (linePt t))).im) := by
    rw [← mul_sub]; exact hmul
  nlinarith [hmul', hsplit, hcorr, hsrc]

/-- **The averaged `|ζ|²`-weighted inequality**: `∫ ω_L W (1 − Re A) Z ≥ −K L` for `L ≥ 32`. -/
theorem exists_averaged_ge_boundary (ha : HalfSummable a) (hla : LogHalfSummable a)
    (hf : HalfSummable f) (hf1 : f 1 = 0) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {c : ℝ} (hc : |c| ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, ∀ {L : ℝ}, 32 ≤ L →
      -(K * L) ≤ ∫ t, win L t * (twoPointWeight c m t * (1 - (dilSeries a (linePt t)).re) *
        zsq t) := by
  obtain ⟨K₀, hK₀, hmom⟩ := exists_momentRe_zero_le
  obtain ⟨K₂, hK₂, hzint⟩ := exists_intervalIntegral_zsq_le
  set SA := halfMass a with hSA
  set SF := halfMass f with hSF
  set KB := 4 * halfMass v + 2 * SF + 12 * (1 + SA) with hKB
  set U := blockWindowConst 1 / 8 * 4 * SA + 2 * Real.log m * SA + 4 * logHalfMass a with hU
  have hSA0 : 0 ≤ SA := halfMass_nonneg a
  have hSF0 : 0 ≤ SF := halfMass_nonneg f
  have hSE0 : 0 ≤ halfMass v := halfMass_nonneg v
  have hKB0 : 0 ≤ KB := by positivity
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (abs_uDerivLine_le ha hla (L := 16) le_rfl hc m hm 0)
  refine ⟨2 * (KB * K₀ + U * K₂ / 2 + 4 * SF), fun {L} hL => ?_⟩
  have hL0 : 0 < L := by linarith
  have hL16 : 16 ≤ L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  rw [integral_win_mul_eq hL0]
  have cw : Continuous (win L) := (contDiff_blockWindow L (2 * L) (L / 2)).continuous
  have cW := continuous_twoPointWeight c m
  have cR : Continuous fun t : ℝ => 1 - (dilSeries a (linePt t)).re :=
    continuous_const.sub
      (Complex.continuous_re.comp (WeilBoundaryDilation.continuous_lineSeries ha))
  have cZ := continuous_zsq
  have cu := continuous_uFun_boundary ha hla L c m
  have cZ' : Continuous zsqDeriv := continuous_zsq_deriv
  have cud := continuous_uDerivLine ha hla L c m
  obtain ⟨a', ha'⟩ : ∃ x : ℝ, x = L / 2 := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ x : ℝ, x = 5 * L / 2 := ⟨_, rfl⟩
  rw [← ha', ← hb']
  have hab : a' ≤ b' := by rw [ha', hb']; linarith
  have cB : Continuous fun t => -(win L t * (KB * zsq t + 2 * SF)) :=
    (cw.mul ((continuous_const.mul cZ).add continuous_const)).neg
  have cX : Continuous fun t => win L t * twoPointWeight c m t * (Real.log L / 2) *
      (1 - (dilSeries a (linePt t)).re) * zsq t + 1 / 2 * (uFun a L c m t * zsqDeriv t) :=
    ((((cw.mul cW).mul continuous_const).mul cR).mul cZ).add (continuous_const.mul (cu.mul cZ'))
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab (cB.intervalIntegrable a' b')
    (cX.intervalIntegrable a' b')
    (fun t ht => pointwise_window_ge_boundary ha hf hf1 hv hW hc m hL16
      (by rw [ha', hb'] at ht; exact ht))
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
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ t in a'..b', win L t * (twoPointWeight c m t *
      (1 - (dilSeries a (linePt t)).re) * zsq t) := ⟨_, rfl⟩
  rw [← hI]
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
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI]
  have hIBP : ∫ t in a'..b', uFun a L c m t * zsqDeriv t =
      -∫ t in a'..b', uDerivLine a L c m t * zsq t := by
    rw [ha', hb']; exact integral_uFun_mul_deriv_boundary ha hla hL0 c m
  have hUb : -(U * ∫ t in a'..b', zsq t) ≤ ∫ t in a'..b', uDerivLine a L c m t * zsq t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_mono_on hab ((cZ.const_mul U).neg.intervalIntegrable _ _)
      ((cud.mul cZ).intervalIntegrable _ _) fun t _ => ?_
    have hb := abs_uDerivLine_le ha hla hL16 hc m hm t
    have hz := zsq_nonneg t
    have := (abs_le.mp hb).1
    nlinarith
  have hwz : ∫ t in a'..b', win L t * zsq t ≤ K₀ * L * Real.log L := by
    have h := hmom hL16
    unfold momentRe at h
    simp only [zero_mul, Real.cos_zero, mul_one] at h
    rwa [integral_win_mul_eq hL0, ← ha', ← hb'] at h
  have hw : ∫ t in a'..b', win L t ≤ 2 * L := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hab (cw.intervalIntegrable a' b')
      ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).intervalIntegrable a' b')
      fun t _ => blockWindow_le_one L (2 * L) (L / 2) t
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, ha', hb'] at h
    rw [ha', hb']
    linarith
  have hz : ∫ t in a'..b', zsq t ≤ K₂ * L * Real.log L := by rw [ha', hb']; exact hzint hL
  rw [hleft, hright, hIBP] at hmono
  have hLlog : L ≤ L * Real.log L := le_mul_of_one_le_right hL0.le hlogL
  have hkey : -((KB * K₀ + U * K₂ / 2 + 4 * SF) * (L * Real.log L)) ≤ Real.log L / 2 * I := by
    have h1 : KB * ∫ t in a'..b', win L t * zsq t ≤ KB * (K₀ * L * Real.log L) :=
      mul_le_mul_of_nonneg_left hwz hKB0
    have h2 : 2 * SF * ∫ t in a'..b', win L t ≤ 2 * SF * (2 * L) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have h3 : U * ∫ t in a'..b', zsq t ≤ U * (K₂ * L * Real.log L) :=
      mul_le_mul_of_nonneg_left hz hU0
    have h4 : 4 * SF * L ≤ 4 * SF * (L * Real.log L) :=
      mul_le_mul_of_nonneg_left hLlog (by positivity)
    linarith only [hmono, hUb, h1, h2, h3, h4]
  have hlog2 : 0 < Real.log L / 2 := by linarith
  have hfinal : -(2 * (KB * K₀ + U * K₂ / 2 + 4 * SF) * L) * (Real.log L / 2) ≤
      I * (Real.log L / 2) := by
    linarith only [hkey]
  have := le_of_mul_le_mul_right hfinal hlog2
  linarith

end RHTower.WeilBoundaryMobius
