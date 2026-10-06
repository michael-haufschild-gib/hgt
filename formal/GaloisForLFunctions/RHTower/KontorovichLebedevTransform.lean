import GaloisForLFunctions.RHTower.BesselKImaginaryOrderUniformBound
import GaloisForLFunctions.RHTower.MaassWhittakerUniqueness

/-!
# The Kontorovich–Lebedev transform of test functions

For `x > 0` and every real `τ`,

`‖K_x(iτ)‖ ≤ e² (|log x| + log(2+|τ|) + 3) e^{−π|τ|/2}`

(`norm_modifiedBesselKOrder_I_mul_le_log`): the Schläfli integral on the shifted line
`Im u = π/2 − 1/τ` and `∫_0^∞ e^{−y cosh u} du ≤ |log y| + 2`.

For a smooth `f` with compact support in `(0, ∞)` (`IsKLTest`) the Kontorovich–Lebedev transform
`g(y) = ∫ f(t) K_{iy}(t) dt` satisfies `KL[Mf] = −y² g` with `Mf = t²f'' + 3tf' + f − t²f`
(`klTransform_besselOp`): Bessel's equation `t²K'' + tK' − t²K = −y²K` and three integrations by
parts.  Iterating, `(1 + y^{2m}) ‖g(y)‖ ≤ C (log(2+|y|) + 1) e^{−π|y|/2}` for every `m`
(`exists_bound_klTransform`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff

namespace GaloisForLFunctions.RHTower.KontorovichLebedev

open GaloisForLFunctions.HTGeometry
open MaassWhittaker (besK besKd besKdd bessel_ode hasDerivAt_besK hasDerivAt_besKd)

noncomputable section

/-! ## A uniform bound for `K_x(iτ)` -/

/-- `∫_0^∞ e^{−y cosh u} du ≤ |log y| + 2` for every `y > 0`. -/
theorem integral_exp_neg_mul_cosh_le_abs_log {y : ℝ} (hy : 0 < y) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-y * Real.cosh t)) ≤ |Real.log y| + 2 := by
  rcases le_or_gt y 2 with h2 | h2
  · refine (integral_exp_neg_mul_cosh_le hy h2).trans ?_
    rw [Real.log_div (by norm_num) hy.ne']
    have := neg_le_abs (Real.log y)
    have : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  · have hmono : (∫ t in Ioi (0 : ℝ), Real.exp (-y * Real.cosh t)) ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-2 * Real.cosh t) := by
      refine setIntegral_mono_on (integrableOn_exp_neg_mul_cosh_Ioi hy)
        (integrableOn_exp_neg_mul_cosh_Ioi (by norm_num)) measurableSet_Ioi (fun t _ => ?_)
      apply Real.exp_le_exp.mpr
      have := Real.cosh_pos t
      nlinarith
    have h := integral_exp_neg_mul_cosh_le (y := 2) (by norm_num) le_rfl
    rw [div_self (by norm_num), Real.log_one] at h
    have := abs_nonneg (Real.log y)
    linarith

/-- **Uniform bound for `K_x(iτ)`**, all `x > 0`, all real `τ`. -/
theorem norm_modifiedBesselKOrder_I_mul_le_log {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ ≤
      Real.exp 2 * (|Real.log x| + Real.log (2 + |τ|) + 3) * Real.exp (-(Real.pi * |τ|) / 2) := by
  -- reduction to `τ ≥ 0`
  have hsym : ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ =
      ‖modifiedBesselKOrder x (((|τ| : ℝ) : ℂ) * I)‖ := by
    rcases le_or_gt 0 τ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, show (((-τ : ℝ) : ℂ) * I) = -((τ : ℂ) * I) by push_cast; ring,
        modifiedBesselKOrder_neg]
  rw [hsym]
  set τ' := |τ| with hτ'
  have hτ'0 : 0 ≤ τ' := abs_nonneg τ
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hlog2 : 0 ≤ Real.log (2 + τ') := Real.log_nonneg (by linarith)
  rcases le_or_gt τ' 1 with h1 | h1
  · -- small order: the unshifted integral
    have hbase := norm_modifiedBesselKOrder_I_mul_le_shifted hx τ' le_rfl (by positivity)
    simp only [mul_zero, Real.exp_zero, one_mul, Real.cos_zero, mul_one] at hbase
    have hJ := integral_exp_neg_mul_cosh_le_abs_log hx
    have hexp : 1 ≤ Real.exp 2 * Real.exp (-(Real.pi * τ') / 2) := by
      rw [← Real.exp_add]
      have := mul_le_mul_of_nonneg_left h1 hπ.le
      exact Real.one_le_exp (by nlinarith [Real.pi_lt_four])
    have hA : 0 ≤ |Real.log x| + Real.log (2 + τ') + 3 := by positivity
    calc ‖modifiedBesselKOrder x ((τ' : ℂ) * I)‖ ≤ |Real.log x| + 2 := hbase.trans hJ
      _ ≤ |Real.log x| + Real.log (2 + τ') + 3 := by linarith
      _ ≤ (Real.exp 2 * Real.exp (-(Real.pi * τ') / 2)) *
            (|Real.log x| + Real.log (2 + τ') + 3) := le_mul_of_one_le_left hA hexp
      _ = _ := by ring
  · -- large order: the line `Im u = π/2 − 1/τ`
    have hτ0 : 0 < τ' := by linarith
    set θ : ℝ := Real.pi / 2 - 1 / τ' with hθdef
    have h1τ : 1 / τ' ≤ 1 := by rw [div_le_one hτ0]; exact h1.le
    have h1τ0 : 0 < 1 / τ' := by positivity
    have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith
    have hθ : θ < Real.pi / 2 := by rw [hθdef]; linarith
    have hcosθ : Real.cos θ = Real.sin (1 / τ') := by rw [hθdef, Real.cos_pi_div_two_sub]
    have hsin : 2 / Real.pi * (1 / τ') ≤ Real.sin (1 / τ') :=
      Real.mul_le_sin h1τ0.le (by linarith)
    have hsin1 : Real.sin (1 / τ') ≤ 1 := Real.sin_le_one _
    have hsinpos : 0 < Real.sin (1 / τ') := lt_of_lt_of_le (by positivity) hsin
    have hbase := norm_modifiedBesselKOrder_I_mul_le_shifted hx τ' hθ0 hθ
    have hxc : 0 < x * Real.cos θ := by rw [hcosθ]; positivity
    have hJ := integral_exp_neg_mul_cosh_le_abs_log hxc
    -- `|log (x cos θ)| ≤ |log x| + log(2+τ') + 1`
    have hlogc : |Real.log (x * Real.cos θ)| ≤ |Real.log x| + Real.log (2 + τ') + 1 := by
      rw [Real.log_mul hx.ne' (by rw [hcosθ]; exact hsinpos.ne'), hcosθ]
      have hl1 : Real.log (Real.sin (1 / τ')) ≤ 0 := Real.log_nonpos hsinpos.le hsin1
      have hl2 : Real.log (2 / Real.pi * (1 / τ')) ≤ Real.log (Real.sin (1 / τ')) :=
        Real.log_le_log (by positivity) hsin
      have hl3 : Real.log (2 / Real.pi * (1 / τ')) = Real.log 2 - Real.log Real.pi - Real.log τ' := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by norm_num) hπ.ne',
          one_div, Real.log_inv]
        ring
      have hlπ : Real.log Real.pi < 2 * Real.log 2 := by
        rw [← Real.log_rpow (by norm_num)]
        exact Real.log_lt_log hπ (by norm_num; exact Real.pi_lt_four)
      have hl21 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      have hlτ : Real.log τ' ≤ Real.log (2 + τ') := Real.log_le_log hτ0 (by linarith)
      have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have := abs_add_le (Real.log x) (Real.log (Real.sin (1 / τ')))
      rw [abs_of_nonpos hl1] at this
      linarith
    have hexpθ : Real.exp (-τ' * θ) = Real.exp 1 * Real.exp (-(Real.pi * τ') / 2) := by
      rw [← Real.exp_add]
      congr 1
      rw [hθdef]
      field_simp
      ring
    have he12 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    calc ‖modifiedBesselKOrder x ((τ' : ℂ) * I)‖
        ≤ Real.exp (-τ' * θ) *
            ∫ t in Ioi (0 : ℝ), Real.exp (-(x * Real.cos θ) * Real.cosh t) := hbase
      _ ≤ Real.exp (-τ' * θ) * (|Real.log x| + Real.log (2 + τ') + 3) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = Real.exp 1 * (|Real.log x| + Real.log (2 + τ') + 3) *
            Real.exp (-(Real.pi * τ') / 2) := by rw [hexpθ]; ring
      _ ≤ Real.exp 2 * (|Real.log x| + Real.log (2 + τ') + 3) *
            Real.exp (-(Real.pi * τ') / 2) := by gcongr

/-! ## Test functions -/

/-- Smooth functions with compact support in `(0, ∞)`. -/
structure IsKLTest (f : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ f
  hasCompactSupport : HasCompactSupport f
  tsupport_subset : tsupport f ⊆ Ioi 0

/-- The Kontorovich–Lebedev transform `g(y) = ∫ f(t) K_{iy}(t) dt`. -/
def klTransform (f : ℝ → ℂ) (y : ℝ) : ℂ := ∫ t, f t * modifiedBesselKOrder t ((y : ℂ) * I)

variable {f : ℝ → ℂ}

theorem IsKLTest.exists_Icc (hf : IsKLTest f) : ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ tsupport f ⊆ Icc a b := by
  rcases (tsupport f).eq_empty_or_nonempty with h | h
  · exact ⟨1, 1, one_pos, le_rfl, by rw [h]; exact empty_subset _⟩
  obtain ⟨m, hm, hmin⟩ := hf.hasCompactSupport.isCompact.exists_isMinOn h continuousOn_id
  obtain ⟨b, hb⟩ := hf.hasCompactSupport.isCompact.bddAbove
  refine ⟨m, b, hf.tsupport_subset hm, hb hm, fun t ht => ⟨hmin ht, hb ht⟩⟩

theorem eq_zero_of_tsupport_subset {a b : ℝ} (hab : tsupport f ⊆ Icc a b) {t : ℝ}
    (ht : t ∉ Icc a b) : f t = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => ht (hab h)

theorem IsKLTest.continuous (hf : IsKLTest f) : Continuous f := hf.smooth.continuous

theorem IsKLTest.deriv (hf : IsKLTest f) : IsKLTest (_root_.deriv f) :=
  ⟨hf.smooth.iterate_deriv 1, hf.hasCompactSupport.deriv,
    tsupport_deriv_subset.trans hf.tsupport_subset⟩

theorem IsKLTest.hasDerivAt (hf : IsKLTest f) (t : ℝ) : HasDerivAt f (_root_.deriv f t) t :=
  ((hf.smooth.differentiable (by simp)) t).hasDerivAt

theorem IsKLTest.mul_left (hf : IsKLTest f) {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) :
    IsKLTest (fun t => c t * f t) := by
  refine ⟨hc.mul hf.smooth, hf.hasCompactSupport.mul_left, ?_⟩
  exact (tsupport_mul_subset_right).trans hf.tsupport_subset

theorem IsKLTest.add {g : ℝ → ℂ} (hf : IsKLTest f) (hg : IsKLTest g) : IsKLTest (f + g) :=
  ⟨hf.smooth.add hg.smooth, hf.hasCompactSupport.add hg.hasCompactSupport,
    (tsupport_add f g).trans (union_subset hf.tsupport_subset hg.tsupport_subset)⟩

theorem IsKLTest.sub {g : ℝ → ℂ} (hf : IsKLTest f) (hg : IsKLTest g) : IsKLTest (f - g) := by
  have h : f - g = f + (fun t => (-1 : ℂ) * g t) := by funext t; simp [sub_eq_add_neg]
  rw [h]
  exact hf.add (hg.mul_left contDiff_const)

/-- The Bessel operator `Mf = t²f'' + 3tf' + f − t²f`. -/
def besselOp (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ 2 * deriv (deriv f) t + 3 * (t : ℂ) * deriv f t + f t - (t : ℂ) ^ 2 * f t

theorem besselOp_eq (f : ℝ → ℂ) : besselOp f =
    ((fun t : ℝ => (t : ℂ) ^ 2 * deriv (deriv f) t) + fun t : ℝ => 3 * (t : ℂ) * deriv f t) + f -
      fun t : ℝ => (t : ℂ) ^ 2 * f t := by
  funext t; rfl

theorem tsupport_besselOp_subset (f : ℝ → ℂ) : tsupport (besselOp f) ⊆ tsupport f := by
  rw [besselOp_eq]
  refine (tsupport_sub _ _).trans (union_subset ((tsupport_add _ _).trans
    (union_subset ((tsupport_add _ _).trans (union_subset ?_ ?_)) subset_rfl))
    tsupport_mul_subset_right)
  · exact tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans tsupport_deriv_subset)
  · exact tsupport_mul_subset_right.trans tsupport_deriv_subset

theorem contDiff_ofReal_complex : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) :=
  Complex.ofRealCLM.contDiff

theorem IsKLTest.besselOp (hf : IsKLTest f) : IsKLTest (besselOp f) := by
  have hsq : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ) ^ 2) := contDiff_ofReal_complex.pow 2
  have hlin : ContDiff ℝ ∞ (fun t : ℝ => 3 * (t : ℂ)) := contDiff_const.mul contDiff_ofReal_complex
  rw [besselOp_eq]
  exact (((hf.deriv.deriv.mul_left hsq).add (hf.deriv.mul_left hlin)).add hf).sub (hf.mul_left hsq)

/-! ## Integration by parts against Bessel's equation -/

theorem continuousOn_besK (ν : ℂ) : ContinuousOn (besK ν) (Ioi 0) := fun _ hs =>
  (hasDerivAt_besK ν hs).continuousAt.continuousWithinAt

theorem continuousOn_besKd (ν : ℂ) : ContinuousOn (besKd ν) (Ioi 0) := fun _ hs =>
  (hasDerivAt_besKd ν hs).continuousAt.continuousWithinAt

theorem continuousOn_besKdd (ν : ℂ) : ContinuousOn (besKdd ν) (Ioi 0) := by
  unfold besKdd
  exact continuousOn_const.mul ((continuousOn_besKd _).add (continuousOn_besKd _))

/-- **`KL[Mf] = −y² KL[f]`.** -/
theorem klTransform_besselOp (hf : IsKLTest f) (y : ℝ) :
    klTransform (besselOp f) y = -((y : ℂ) ^ 2) * klTransform f y := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := hf.exists_Icc
  set c : ℝ := a / 2
  set d : ℝ := b + 1
  have hc : 0 < c := by positivity
  have hcd : c ≤ d := by simp only [c, d]; linarith
  have hca : c < a := by simp only [c]; linarith
  have hbd : b < d := by simp only [d]; linarith
  set ν : ℂ := (y : ℂ) * I
  have hsub : Icc c d ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le hc ht.1
  have hU : uIcc c d = Icc c d := uIcc_of_le hcd
  -- vanishing at the endpoints
  have hz : ∀ t, t ∉ Icc a b → f t = 0 := fun t ht => eq_zero_of_tsupport_subset hsupp ht
  have hsupp' : tsupport (deriv f) ⊆ Icc a b := tsupport_deriv_subset.trans hsupp
  have hz' : ∀ t, t ∉ Icc a b → deriv f t = 0 := fun t ht => eq_zero_of_tsupport_subset hsupp' ht
  have hcn : c ∉ Icc a b := fun h => absurd h.1 (not_le.2 hca)
  have hdn : d ∉ Icc a b := fun h => absurd h.2 (not_le.2 hbd)
  -- reduction of the whole-line integrals to `[c, d]`
  have hred : ∀ g : ℝ → ℂ, (∀ t, t ∉ Icc a b → g t = 0) →
      ∫ t, g t * besK ν t = ∫ t in c..d, g t * besK ν t := fun g hg => by
    rw [intervalIntegral.integral_of_le hcd, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro t ht
    have : t ∉ Icc a b := fun h => ht ⟨lt_of_lt_of_le hca h.1, h.2.trans hbd.le⟩
    rw [hg t this, zero_mul]
  have hMz : ∀ t, t ∉ Icc a b → besselOp f t = 0 := fun t ht =>
    eq_zero_of_tsupport_subset ((tsupport_besselOp_subset f).trans hsupp) ht
  change ∫ t, besselOp f t * besK ν t = -((y : ℂ) ^ 2) * ∫ t, f t * besK ν t
  rw [hred _ hMz, hred _ hz, ← intervalIntegral.integral_const_mul]
  -- derivatives on `[c, d]`
  have hK : ∀ t ∈ uIcc c d, HasDerivAt (besK ν) (besKd ν t) t := fun t ht =>
    hasDerivAt_besK ν (hsub (hU ▸ ht))
  have hKd : ∀ t ∈ uIcc c d, HasDerivAt (besKd ν) (besKdd ν t) t := fun t ht =>
    hasDerivAt_besKd ν (hsub (hU ▸ ht))
  have hii : ∀ g : ℝ → ℂ, ContinuousOn g (Ioi 0) → IntervalIntegrable g volume c d := fun g hg =>
    (hg.mono hsub).intervalIntegrable_of_Icc hcd
  have hf1 := hf.deriv
  have hf2 := hf.deriv.deriv
  set f1 := deriv f
  set f2 := deriv (deriv f)
  have hd0 : ∀ t, HasDerivAt f (f1 t) t := hf.hasDerivAt
  have hd1 : ∀ t, HasDerivAt f1 (f2 t) t := hf.deriv.hasDerivAt
  have hT : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := fun t => (hasDerivAt_id t).ofReal_comp
  -- (1) `∫ (t² f) K'' = −∫ (t² f' + 2 t f) K'`
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => (t : ℂ) ^ 2 * f t) (v := besKd ν)
    (u' := fun t : ℝ => (t : ℂ) ^ 2 * f1 t + 2 * (t : ℂ) * f t) (v' := besKdd ν)
    (fun t _ => by
      have h := ((hT t).pow 2).mul (hd0 t)
      exact h.congr_deriv (by simp only [Pi.pow_apply]; push_cast; ring)) hKd
    (hii _ (Continuous.continuousOn (by
      have := hf.continuous; have := hf1.continuous; fun_prop)))
    (hii _ (continuousOn_besKdd ν))
  -- (2) `∫ (t² f' + 2tf) K' = −∫ (t² f'' + 4 t f' + 2 f) K`
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => (t : ℂ) ^ 2 * f1 t + 2 * (t : ℂ) * f t) (v := besK ν)
    (u' := fun t : ℝ => (t : ℂ) ^ 2 * f2 t + 4 * (t : ℂ) * f1 t + 2 * f t) (v' := besKd ν)
    (fun t _ => by
      have h := (((hT t).pow 2).mul (hd1 t)).add (((hT t).const_mul 2).mul (hd0 t))
      exact h.congr_deriv (by simp only [Pi.pow_apply]; push_cast; ring)) hK
    (hii _ (Continuous.continuousOn (by
      have := hf.continuous; have := hf1.continuous; have := hf2.continuous; fun_prop)))
    (hii _ (continuousOn_besKd ν))
  -- (3) `∫ (t f) K' = −∫ (f + t f') K`
  have h3 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => (t : ℂ) * f t) (v := besK ν)
    (u' := fun t : ℝ => f t + (t : ℂ) * f1 t) (v' := besKd ν)
    (fun t _ => by
      have h := (hT t).mul (hd0 t)
      exact h.congr_deriv (by ring)) hK
    (hii _ (Continuous.continuousOn (by
      have := hf.continuous; have := hf1.continuous; fun_prop)))
    (hii _ (continuousOn_besKd ν))
  simp only [hz c hcn, hz d hdn, hz' c hcn, hz' d hdn, mul_zero, zero_mul, add_zero, sub_zero,
    zero_sub] at h1 h2 h3
  -- Bessel's equation on `[c, d]`
  have hode : ∀ t ∈ uIcc c d, f t * ((t : ℂ) ^ 2 * besKdd ν t + (t : ℂ) * besKd ν t -
      (t : ℂ) ^ 2 * besK ν t) = -((y : ℂ) ^ 2) * (f t * besK ν t) := fun t ht => by
    have h := bessel_ode ν (hsub (hU ▸ ht))
    have hν : ν ^ 2 = -((y : ℂ) ^ 2) := by
      simp only [ν, mul_pow, Complex.I_sq]; ring
    rw [hν] at h
    linear_combination f t * h
  rw [← intervalIntegral.integral_congr hode]
  -- assemble
  have hcont : ∀ g : ℝ → ℂ, Continuous g → ContinuousOn (fun t => g t * besK ν t) (Ioi 0) :=
    fun g hg => hg.continuousOn.mul (continuousOn_besK ν)
  have hcont' : ∀ g : ℝ → ℂ, Continuous g → ContinuousOn (fun t => g t * besKd ν t) (Ioi 0) :=
    fun g hg => hg.continuousOn.mul (continuousOn_besKd ν)
  have hcont'' : ∀ g : ℝ → ℂ, Continuous g → ContinuousOn (fun t => g t * besKdd ν t) (Ioi 0) :=
    fun g hg => hg.continuousOn.mul (continuousOn_besKdd ν)
  have e1 : ∫ t in c..d, f t * ((t : ℂ) ^ 2 * besKdd ν t + (t : ℂ) * besKd ν t -
      (t : ℂ) ^ 2 * besK ν t) =
      (∫ t in c..d, (t : ℂ) ^ 2 * f t * besKdd ν t) + (∫ t in c..d, (t : ℂ) * f t * besKd ν t) -
        ∫ t in c..d, (t : ℂ) ^ 2 * f t * besK ν t := by
    rw [← intervalIntegral.integral_add, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    · exact (hii _ (hcont'' _ (by have := hf.continuous; fun_prop))).add
        (hii _ (hcont' _ (by have := hf.continuous; fun_prop)))
    · exact hii _ (hcont _ (by have := hf.continuous; fun_prop))
    · exact hii _ (hcont'' _ (by have := hf.continuous; fun_prop))
    · exact hii _ (hcont' _ (by have := hf.continuous; fun_prop))
  have e2 : ∫ t in c..d, besselOp f t * besK ν t =
      (∫ t in c..d, ((t : ℂ) ^ 2 * f2 t + 4 * (t : ℂ) * f1 t + 2 * f t) * besK ν t) -
        (∫ t in c..d, (f t + (t : ℂ) * f1 t) * besK ν t) -
          ∫ t in c..d, (t : ℂ) ^ 2 * f t * besK ν t := by
    rw [← intervalIntegral.integral_sub, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [besselOp, f1, f2]; ring
    · exact (hii _ (hcont _ (by
        have := hf.continuous; have := hf1.continuous; have := hf2.continuous; fun_prop))).sub
        (hii _ (hcont _ (by have := hf.continuous; have := hf1.continuous; fun_prop)))
    · exact hii _ (hcont _ (by have := hf.continuous; fun_prop))
    · exact hii _ (hcont _ (by
        have := hf.continuous; have := hf1.continuous; have := hf2.continuous; fun_prop))
    · exact hii _ (hcont _ (by have := hf.continuous; have := hf1.continuous; fun_prop))
  have e3 : (∫ t in c..d, (t : ℂ) ^ 2 * f t * besKdd ν t) =
      ∫ t in c..d, (fun t : ℝ => (t : ℂ) ^ 2 * f t) t * besKdd ν t := rfl
  rw [e1, e2, e3, h1, h2]
  rw [show (∫ t in c..d, (t : ℂ) * f t * besKd ν t) =
      ∫ t in c..d, (fun t : ℝ => (t : ℂ) * f t) t * besKd ν t from rfl, h3]
  ring

/-! ## Decay of the transform -/

theorem IsKLTest.besselOp_iterate (hf : IsKLTest f) (m : ℕ) :
    IsKLTest (KontorovichLebedev.besselOp^[m] f) := by
  induction m with
  | zero => exact hf
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.besselOp

theorem klTransform_besselOp_iterate (hf : IsKLTest f) (m : ℕ) (y : ℝ) :
    klTransform (besselOp^[m] f) y = (-((y : ℂ) ^ 2)) ^ m * klTransform f y := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', klTransform_besselOp (hf.besselOp_iterate m), ih, pow_succ]
    ring

theorem IsKLTest.integrable (hf : IsKLTest f) : Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hf.hasCompactSupport

/-- `‖g(y)‖ ≤ C (log(2+|y|) + 1) e^{−π|y|/2}`. -/
theorem exists_bound_klTransform_basic (hf : IsKLTest f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
      ‖klTransform f y‖ ≤ C * (Real.log (2 + |y|) + 1) * Real.exp (-(Real.pi * |y|) / 2) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := hf.exists_Icc
  set L : ℝ := max |Real.log a| |Real.log b|
  have hL : 0 ≤ L := (abs_nonneg _).trans (le_max_left _ _)
  set B : ℝ := ∫ t, ‖f t‖
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  refine ⟨Real.exp 2 * (L + 3) * B, by positivity, fun y => ?_⟩
  have hlog : 0 ≤ Real.log (2 + |y|) := Real.log_nonneg (by linarith [abs_nonneg y])
  have hpt : ∀ t, ‖f t * modifiedBesselKOrder t ((y : ℂ) * I)‖ ≤
      ‖f t‖ * (Real.exp 2 * (L + Real.log (2 + |y|) + 3) * Real.exp (-(Real.pi * |y|) / 2)) := by
    intro t
    by_cases ht : t ∈ Icc a b
    · have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      have hlt : |Real.log t| ≤ L := by
        have h1 := Real.log_le_log ha ht.1
        have h2 := Real.log_le_log ht0 ht.2
        exact abs_le_max_abs_abs h1 h2
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ((norm_modifiedBesselKOrder_I_mul_le_log ht0 y).trans ?_)
        (norm_nonneg _)
      gcongr
    · simp [eq_zero_of_tsupport_subset hsupp ht]
  unfold klTransform
  refine (norm_integral_le_of_norm_le (hf.integrable.norm.mul_const _)
    (Eventually.of_forall hpt)).trans ?_
  rw [integral_mul_const]
  have he : 0 ≤ Real.exp 2 * Real.exp (-(Real.pi * |y|) / 2) := by positivity
  calc B * (Real.exp 2 * (L + Real.log (2 + |y|) + 3) * Real.exp (-(Real.pi * |y|) / 2))
      = (Real.exp 2 * Real.exp (-(Real.pi * |y|) / 2)) * (B * (L + 3) + B * Real.log (2 + |y|)) := by
        ring
    _ ≤ (Real.exp 2 * Real.exp (-(Real.pi * |y|) / 2)) *
          ((L + 3) * B * (Real.log (2 + |y|) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ he
        nlinarith [mul_nonneg hB hlog, mul_nonneg hB hL]
    _ = _ := by ring

/-- **Decay of the Kontorovich–Lebedev transform**:
`‖g(y)‖ ≤ C (log(2+|y|) + 1) e^{−π|y|/2} / (1 + y^{2m})` for every `m`. -/
theorem exists_bound_klTransform (hf : IsKLTest f) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖klTransform f y‖ ≤
      C * (Real.log (2 + |y|) + 1) * Real.exp (-(Real.pi * |y|) / 2) / (1 + y ^ (2 * m)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_bound_klTransform_basic hf
  obtain ⟨C₁, hC₁, h₁⟩ := exists_bound_klTransform_basic (hf.besselOp_iterate m)
  refine ⟨C₀ + C₁, by positivity, fun y => ?_⟩
  have hpos : 0 < 1 + y ^ (2 * m) := by
    have : 0 ≤ y ^ (2 * m) := by rw [pow_mul]; positivity
    linarith
  rw [le_div_iff₀ hpos]
  have hm : ‖klTransform (besselOp^[m] f) y‖ = y ^ (2 * m) * ‖klTransform f y‖ := by
    rw [klTransform_besselOp_iterate hf, norm_mul, norm_pow, norm_neg, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, pow_mul, sq_abs]
  have h1 := h₁ y
  rw [hm] at h1
  have h0 := h₀ y
  nlinarith

end

end GaloisForLFunctions.RHTower.KontorovichLebedev
