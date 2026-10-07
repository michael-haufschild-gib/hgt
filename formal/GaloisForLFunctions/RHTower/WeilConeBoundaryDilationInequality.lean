import GaloisForLFunctions.RHTower.WeilConeInfiniteDilationRigidity
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic

/-!
# The boundary inequality of a Weil-positive dilation system on the critical line

Let `A(s) = Σ a(n) n^{−s}` and `V(s) = Σ v(n) n^{−s}` converge absolutely at `s = ½`, with
`v(0) = v(1) = 0`, and suppose `λ = Λ ⋆ a + v` is full-cone Weil-positive, with Herglotz
continuation `Φ` on `Re s > ½`. The master identity gives

`Φ = G + 1/(s − 1) + A ζ'/ζ − V`   on `Re s > ½`,  with `A(1) = 1`,

where `G` is the archimedean datum. The right side extends continuously to every point of the
critical line where `ζ ≠ 0`, so its real part is nonnegative there. In Hardy coordinates,
`ζ'/ζ(½ + it) = −θ'(t) − i Z'(t)/Z(t)`, and the real parts of `G` and of the pole cancel down to
`θ'`. Hence

`0 ≤ (1 − Re A)·θ' + Im A·Z'/Z − Re V`   wherever `ζ(½ + it) ≠ 0`,

and, multiplied by `Z²`, the inequality `(Re A − 1)·θ'·Z² ≤ Im A·Z·Z' − Re V·Z²` holds at every
height.
When the log-weighted series converges at `½`, the line function `t ↦ A(½ + it)` is
differentiable with continuous derivative `−i Σ a(n) log n · n^{−½−it}`.
-/

noncomputable section

open Complex Filter Topology Set
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType

namespace RHTower.WeilBoundaryDilation

open RHTower.WeilInfiniteDilation

variable {a : ℕ → ℝ}

/-- `Σ a(n) n^{−s}` converges absolutely at `s = ½`, hence on the closed half-plane `Re s ≥ ½`. -/
abbrev HalfSummable (a : ℕ → ℝ) : Prop :=
  LSeriesSummable (fun n => (a n : ℂ)) (((1 / 2 - 0 : ℝ)) : ℂ)

theorem summable_of_half (ha : HalfSummable a) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    LSeriesSummable (fun n => (a n : ℂ)) s :=
  summable_of_le_re ha (by simpa using hs)

theorem continuousOn_dilSeries (ha : HalfSummable a) :
    ContinuousOn (dilSeries a) {s : ℂ | 1 / 2 ≤ s.re} := by
  have hsum : Summable fun n => ‖LSeries.term (fun n => (a n : ℂ)) (((1 / 2 - 0 : ℝ)) : ℂ) n‖ :=
    summable_norm_iff.mpr ha
  refine continuousOn_tsum (fun n => ?_) hsum (fun n s hs => ?_)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [LSeries.term_zero]; exact continuousOn_const
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      refine ContinuousOn.congr (f := fun s => (a n : ℂ) / (n : ℂ) ^ s) ?_
        (fun s _ => LSeries.term_of_ne_zero hn.ne' _ s)
      exact continuousOn_const.div (continuousOn_const.cpow continuousOn_id
        (fun _ _ => Or.inl (by exact_mod_cast hn))) (fun s _ => by
          rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
  · exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n

/-- The regular part `v`: `v(0) = v(1) = 0` and `Σ |v(n)| n^{−½} < ∞`. -/
structure BoundaryRegular (v : ℕ → ℝ) : Prop where
  zero : v 0 = 0
  one : v 1 = 0
  summable : LSeriesSummable (fun n => (v n : ℂ)) (1 / 2)

/-- `V(s) = Σ v(n) n^{−s}`. -/
abbrev regSeries (v : ℕ → ℝ) : ℂ → ℂ := LSeries (fun n => (v n : ℂ))

variable {v : ℕ → ℝ}

theorem continuousOn_LSeries_half {f : ℕ → ℂ} (hf : LSeriesSummable f (1 / 2)) :
    ContinuousOn (LSeries f) {s : ℂ | 1 / 2 ≤ s.re} := by
  have hsum : Summable fun n => ‖LSeries.term f (1 / 2) n‖ := summable_norm_iff.mpr hf
  refine continuousOn_tsum (fun n => ?_) hsum (fun n s hs => ?_)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [LSeries.term_zero]; exact continuousOn_const
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      refine ContinuousOn.congr (f := fun s => f n / (n : ℂ) ^ s) ?_
        (fun s _ => LSeries.term_of_ne_zero hn.ne' _ s)
      exact continuousOn_const.div (continuousOn_const.cpow continuousOn_id
        (fun _ _ => Or.inl (by exact_mod_cast hn))) (fun s _ => by
          rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hn0 h.1)
  · exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n

theorem continuousOn_regSeries (hv : BoundaryRegular v) :
    ContinuousOn (regSeries v) {s : ℂ | 1 / 2 ≤ s.re} :=
  continuousOn_LSeries_half hv.summable

theorem differentiableOn_regSeries (hv : BoundaryRegular v) :
    DifferentiableOn ℂ (regSeries v) {s : ℂ | 1 / 2 < s.re} := by
  refine (LSeries_differentiableOn _).mono fun s hs => ?_
  have h1 := hv.summable.abscissaOfAbsConv_le
  simp only [mem_setOf_eq] at hs ⊢
  refine lt_of_le_of_lt h1 ?_
  have : ((1 / 2 : ℂ).re : EReal) = ((1 / 2 : ℝ) : EReal) := by norm_num
  rw [this]
  exact EReal.coe_lt_coe_iff.mpr hs

/-- **The master identity** for `Λ ⋆ a + v` with `a, v` absolutely convergent on `Re s ≥ ½`. -/
theorem master_identity_half (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {s : ℂ} (hs : 1 / 2 < s.re) :
    masterLeft hW (regSeries v) s = masterRightSeries a s := by
  have hpre : IsPreconnected {s : ℂ | 1 / 2 < s.re} :=
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2U : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  refine (analyticOnNhd_masterLeft hW
    (differentiableOn_regSeries hv)).eqOn_of_preconnected_of_eventuallyEq
    (fun z hz => analyticOnNhd_masterRightSeries ha z
      (by simp only [mem_setOf_eq] at hz ⊢; linarith)) hpre h2U ?_ hs
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hV] with z hz
  have hz : 1 < z.re := hz
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hζ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hz
  have hA : LSeriesSummable (fun n => (a n : ℂ)) z := summable_of_half ha (by linarith)
  have hvz : LSeriesSummable (fun n => (v n : ℂ)) z :=
    hv.summable.of_re_le_re (by norm_num; linarith)
  have hL : LSeries (fun n => (finiteTypeSeq a 0 v n : ℂ)) z =
      -(dilSeries a z * deriv riemannZeta z / riemannZeta z) + regSeries v z := by
    rw [finiteTypeSeq_zero_cast, LSeries_add (hΛ.convolution hA) hvz, LSeries_convolution' hΛ hA,
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz]
    ring
  unfold masterLeft masterRightSeries
  rw [weilContinuation_eq hW hz, weilFunction, lamC_finiteTypeSeq a rfl hv.zero hv.one, hL,
    ← sq_mul_deriv_riemannZeta hz1, (zetaResidueUnit_eventuallyEq hz1).eq_of_nhds]
  unfold zetaArchimedeanDatum
  field_simp
  ring

/-- Off the zeros: `Φ = G + 1/(s − 1) + A ζ'/ζ − V`. -/
theorem weilContinuation_eq_half (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    weilContinuation hW s = zetaArchimedeanDatum s + 1 / (s - 1) +
      dilSeries a s * deriv riemannZeta s / riemannZeta s - regSeries v s := by
  have h := master_identity_half ha hv hW hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold masterLeft masterRightSeries at h
  rw [← sq_mul_deriv_riemannZeta hs1, (zetaResidueUnit_eventuallyEq hs1).eq_of_nhds] at h
  have h2 : (s - 1) ^ 2 * riemannZeta s * (weilContinuation hW s - zetaArchimedeanDatum s -
      1 / (s - 1) - dilSeries a s * deriv riemannZeta s / riemannZeta s + regSeries v s) = 0 := by
    have e : (s - 1) ^ 2 * riemannZeta s * (weilContinuation hW s - zetaArchimedeanDatum s -
        1 / (s - 1) - dilSeries a s * deriv riemannZeta s / riemannZeta s + regSeries v s) =
        (s - 1) * riemannZeta s * ((s - 1) * (weilContinuation hW s - zetaArchimedeanDatum s +
          regSeries v s) - 1) - dilSeries a s * ((s - 1) ^ 2 * deriv riemannZeta s) := by
      field_simp
      ring
    rw [e, h]; ring
  have hne : (s - 1) ^ 2 * riemannZeta s ≠ 0 := mul_ne_zero (pow_ne_zero 2 hs1') hζ
  have := (mul_eq_zero.mp h2).resolve_left hne
  linear_combination this

/-- **Normalization**: `A(1) = 1`. -/
theorem dilSeries_one_eq_one_half (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) : dilSeries a 1 = 1 := by
  have h := master_identity_half ha hv hW (s := 1) (by norm_num)
  unfold masterLeft masterRightSeries at h
  simp only [sub_self, zero_mul, zetaResidueUnit_one, zero_sub, mul_neg, mul_one] at h
  linear_combination h

/-- The boundary function `H = G + 1/(s − 1) + A ζ'/ζ − V`. -/
def boundaryFun (a v : ℕ → ℝ) (s : ℂ) : ℂ :=
  zetaArchimedeanDatum s + 1 / (s - 1) + dilSeries a s * deriv riemannZeta s / riemannZeta s -
    regSeries v s

theorem linePt_re (t : ℝ) : (linePt t).re = 1 / 2 := by simp [linePt]

theorem linePt_ne_one (t : ℝ) : linePt t ≠ 1 := by
  intro h; have := congrArg Complex.re h; rw [linePt_re] at this; norm_num at this

theorem continuousWithinAt_boundaryFun (ha : HalfSummable a) (hv : BoundaryRegular v) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) (hζ : riemannZeta ρ ≠ 0) :
    ContinuousWithinAt (boundaryFun a v) {s : ℂ | 1 / 2 ≤ s.re} ρ := by
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hρ; norm_num at hρ
  have hG : ContinuousAt zetaArchimedeanDatum ρ :=
    (differentiableAt_zetaArchimedeanDatum (by rw [hρ]; norm_num)).continuousAt
  have hmem : ρ ∈ {s : ℂ | 1 / 2 ≤ s.re} := by show (1 / 2 : ℝ) ≤ ρ.re; rw [hρ]
  have hA : ContinuousWithinAt (dilSeries a) {s : ℂ | 1 / 2 ≤ s.re} ρ :=
    continuousOn_dilSeries ha ρ hmem
  have hV : ContinuousWithinAt (regSeries v) {s : ℂ | 1 / 2 ≤ s.re} ρ :=
    continuousOn_regSeries hv ρ hmem
  have hZan : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  have hZ : ContinuousAt riemannZeta ρ := hZan.continuousAt
  have hZ' : ContinuousAt (deriv riemannZeta) ρ := hZan.deriv.continuousAt
  unfold boundaryFun
  refine (((hG.add (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
    (sub_ne_zero.mpr hρ1))).continuousWithinAt).add ?_).sub hV
  exact (hA.mul hZ'.continuousWithinAt).div hZ.continuousWithinAt hζ

theorem re_boundaryFun_nonneg (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hζ : riemannZeta ρ ≠ 0) : 0 ≤ (boundaryFun a v ρ).re := by
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hρ; norm_num at hρ
  have hcont := continuousWithinAt_boundaryFun ha hv hρ hζ
  have hpath : Tendsto (fun ε : ℝ => ρ + (ε : ℂ)) (𝓝[>] 0) (𝓝[{s : ℂ | 1 / 2 ≤ s.re}] ρ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => ρ + (ε : ℂ)) (𝓝 0) (𝓝 (ρ + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      show (1 / 2 : ℝ) ≤ (ρ + (ε : ℂ)).re
      simp only [Complex.add_re, Complex.ofReal_re, hρ]
      linarith [(Set.mem_Ioi.mp hε)]
  have hlim := (Complex.continuous_re.tendsto _).comp (hcont.tendsto.comp hpath)
  refine ge_of_tendsto hlim ?_
  have hζev : ∀ᶠ s in 𝓝 ρ, riemannZeta s ≠ 0 ∧ s ≠ 1 :=
    ((analyticOn_riemannZeta ρ hρ1).continuousAt.eventually_ne hζ).and (eventually_ne_nhds hρ1)
  have hpath' : Tendsto (fun ε : ℝ => ρ + (ε : ℂ)) (𝓝[>] 0) (𝓝 ρ) :=
    hpath.mono_right nhdsWithin_le_nhds
  filter_upwards [hpath'.eventually hζev, self_mem_nhdsWithin] with ε hε hεpos
  obtain ⟨hζε, hε1⟩ := hε
  have hre : 1 / 2 < (ρ + (ε : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, hρ]; linarith [(Set.mem_Ioi.mp hεpos)]
  show 0 ≤ (boundaryFun a v (ρ + (ε : ℂ))).re
  rw [boundaryFun, ← weilContinuation_eq_half ha hv hW hre hε1 hζε]
  exact re_weilContinuation_nonneg hW hre

/-- `ζ'/ζ` on the critical line in Hardy coordinates: `ζ'/ζ(½ + it) = −θ'(t) − i Z'(t)/Z(t)`. -/
theorem logDeriv_zeta_line {t : ℝ} (hζ : riemannZeta (linePt t) ≠ 0) :
    deriv riemannZeta (linePt t) / riemannZeta (linePt t) =
      -(gammaHardyPhaseRate t : ℂ) - I * ((deriv hardyZ t / hardyZ t : ℝ) : ℂ) := by
  have h1 := exp_theta_mul_deriv_riemannZeta_line t
  have h2 := exp_theta_mul_riemannZeta_line_eq_hardyZ t
  rw [deriv_riemannZeta_line] at h1
  have hE : Complex.exp (I * (gammaHardyTheta t : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hZ : (hardyZ t : ℂ) ≠ 0 := by rw [← h2]; exact mul_ne_zero hE hζ
  have hq : ((deriv hardyZ t / hardyZ t : ℝ) : ℂ) * (hardyZ t : ℂ) =
      ((deriv hardyZ t : ℝ) : ℂ) := by
    push_cast; exact div_mul_cancel₀ _ hZ
  rw [div_eq_iff hζ]
  refine mul_left_cancel₀ (mul_ne_zero hE Complex.I_ne_zero) ?_
  linear_combination h1 + (I * (gammaHardyPhaseRate t : ℂ)) * h2 +
    (I ^ 2 * ((deriv hardyZ t / hardyZ t : ℝ) : ℂ)) * h2 + I ^ 2 * hq +
    ((deriv hardyZ t : ℝ) : ℂ) * Complex.I_sq

/-- **The boundary inequality.**  At every point of the critical line where `ζ ≠ 0`,
`0 ≤ (1 − Re A)·θ' + Im A·Z'/Z − Re V`. -/
theorem boundary_ineq (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) {t : ℝ} (hζ : riemannZeta (linePt t) ≠ 0) :
    0 ≤ (1 - (dilSeries a (linePt t)).re) * gammaHardyPhaseRate t +
      (dilSeries a (linePt t)).im * (deriv hardyZ t / hardyZ t) -
        (regSeries v (linePt t)).re := by
  have h := re_boundaryFun_nonneg ha hv hW (linePt_re t) hζ
  rw [boundaryFun, mul_div_assoc, logDeriv_zeta_line hζ] at h
  have hG : (zetaArchimedeanDatum (linePt t)).re = gammaHardyPhaseRate t + (1 / linePt t).re := by
    unfold zetaArchimedeanDatum gammaHardyPhaseRate
    simp only [Complex.add_re, Complex.sub_re, Complex.div_re]
    norm_num
    ring
  have hpole : (1 / (linePt t - 1)).re = -(1 / linePt t).re := by
    simp only [one_div, Complex.inv_re, linePt, Complex.normSq_apply]
    simp
    ring
  simp only [Complex.sub_re, Complex.add_re, hG, hpole, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    Complex.sub_im, Complex.neg_im] at h
  nlinarith [h]

theorem norm_riemannZeta_linePt (t : ℝ) : ‖riemannZeta (linePt t)‖ = |hardyZ t| := by
  rw [riemannZeta_line_eq_exp_neg_theta_mul_hardyZ, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_exp]
  simp

theorem riemannZeta_linePt_ne_zero {t : ℝ} (hZ : hardyZ t ≠ 0) : riemannZeta (linePt t) ≠ 0 := by
  intro h
  have := norm_riemannZeta_linePt t
  rw [h, norm_zero] at this
  exact hZ (abs_eq_zero.mp this.symm)

/-- **The boundary inequality at every height**: `(Re A − 1)·θ'·Z² ≤ Im A·Z Z' − Re V·Z²`. -/
theorem boundary_ineq_sq (ha : HalfSummable a) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq a 0 v)) (t : ℝ) :
    ((dilSeries a (linePt t)).re - 1) * gammaHardyPhaseRate t * hardyZ t ^ 2 ≤
      (dilSeries a (linePt t)).im * (hardyZ t * deriv hardyZ t) -
        (regSeries v (linePt t)).re * hardyZ t ^ 2 := by
  by_cases hZ : hardyZ t = 0
  · simp [hZ]
  · have h := mul_nonneg (boundary_ineq ha hv hW (riemannZeta_linePt_ne_zero hZ))
      (sq_nonneg (hardyZ t))
    have e : (dilSeries a (linePt t)).im * (deriv hardyZ t / hardyZ t) * hardyZ t ^ 2 =
        (dilSeries a (linePt t)).im * (hardyZ t * deriv hardyZ t) := by
      field_simp
    rw [sub_mul, add_mul, e] at h
    linarith

/-! ## The line function and its derivative -/

theorem continuous_linePt : Continuous linePt := by
  unfold linePt; fun_prop

theorem continuous_LSeries_linePt {f : ℕ → ℂ} (hf : LSeriesSummable f (1 / 2)) :
    Continuous fun t : ℝ => LSeries f (linePt t) :=
  (continuousOn_LSeries_half hf).comp_continuous continuous_linePt
    (fun t => by show (1 / 2 : ℝ) ≤ (linePt t).re; rw [linePt_re])

theorem hasDerivAt_term_linePt (f : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => LSeries.term f (linePt t) n)
      (-I * LSeries.term (LSeries.logMul f) (linePt t) n) t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [LSeries.term_zero, mul_zero]; exact hasDerivAt_const _ _
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have e : ∀ t : ℝ, LSeries.term f (linePt t) n =
        f n * Complex.exp (-(Complex.log n * linePt t)) := by
      intro t
      rw [LSeries.term_of_ne_zero hn.ne', Complex.cpow_def_of_ne_zero hn0, div_eq_mul_inv,
        ← Complex.exp_neg]
    have e' : LSeries.term (LSeries.logMul f) (linePt t) n =
        Complex.log n * (f n * Complex.exp (-(Complex.log n * linePt t))) := by
      rw [LSeries.term_of_ne_zero hn.ne', LSeries.logMul, Complex.cpow_def_of_ne_zero hn0,
        div_eq_mul_inv, ← Complex.exp_neg]
      ring
    simp_rw [e]
    rw [e']
    have h1 : HasDerivAt (fun t : ℝ => linePt t) I t := by
      unfold linePt
      simpa using ((hasDerivAt_id (t : ℝ)).ofReal_comp.mul_const I).const_add (1 / 2 : ℂ)
    have hL : HasDerivAt (fun t : ℝ => -(Complex.log n * linePt t)) (-(Complex.log n * I)) t :=
      (h1.const_mul _).neg
    refine ((hL.cexp).const_mul (f n)).congr_deriv ?_
    ring

/-- With `Σ |f(n)| n^{−½} log n < ∞`, the line function `t ↦ L(f, ½ + it)` has derivative
`−i L(log·f, ½ + it)`. -/
theorem hasDerivAt_LSeries_linePt {f : ℕ → ℂ} (hf : LSeriesSummable f (1 / 2))
    (hlog : LSeriesSummable (LSeries.logMul f) (1 / 2)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => LSeries f (linePt t))
      (-I * LSeries (LSeries.logMul f) (linePt t)) t := by
  have hre : ∀ t : ℝ, (1 / 2 : ℂ).re ≤ (linePt t).re := fun t => by
    rw [linePt_re]; norm_num
  have hb : ∀ n (t : ℝ), ‖-I * LSeries.term (LSeries.logMul f) (linePt t) n‖ ≤
      ‖LSeries.term (LSeries.logMul f) (1 / 2) n‖ := by
    intro n t
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, LSeries.norm_term_eq, LSeries.norm_term_eq,
      linePt_re]
    norm_num
  have h := hasDerivAt_tsum (summable_norm_iff.mpr hlog)
    (fun n t => hasDerivAt_term_linePt f n t) hb ((hf.of_re_le_re (hre 0))) t
  unfold LSeries
  exact h.congr_deriv tsum_mul_left

end RHTower.WeilBoundaryDilation
