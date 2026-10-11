import GaloisForLFunctions.RHTower.WeilWindowedLinearLockQuantization

/-!
# Constant-rate evaporation locks are impossible

Let `G` be a Herglotz producer.  If a positive fraction of its spectral mass is diffuse at a constant
rate, the lower-line lock phase grows like `x log x`.  The twist with this phase is

`W_B(s) = exp(−B (s − ½)(Log(s − ½) + iπ/2))`,  `W_B(½ + iy) = e^{iB|y| log|y|}` for `y < 0`.

On the lower strip `|W_B| ≤ 1`, and on `Re s = 3/2` it decays like `|y|^{−B}` (`norm_evapTwist_le`,
`norm_evapTwist_three_halves_le`).  So the right edge of the contour shift is `O(δ^{B−1})` instead of
the `O(1/δ)` of the untwisted kernel, and the twisted radial integral tends to `0`.

**Theorem** (`evaporation_lock_impossible`).  No Herglotz producer satisfies
`G(1 − s) = κ₀ e^{iη(−τ)} W_B(s) G(s)` on the lower line (`s = ½ + 2iτ`, `τ < 0`) with `B > 0`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- The evaporation twist `W_B(s) = exp(−B (s − ½)(Log(s − ½) + iπ/2))`. -/
def evapTwist (B : ℝ) (s : ℂ) : ℂ :=
  cexp (-((B : ℂ) * ((s - 1 / 2) * (Complex.log (s - 1 / 2) + (Real.pi / 2 : ℝ) * I))))

/-- `Re(w (Log w + iπ/2)) ≥ Re w · log‖w‖` for `Re w ≥ 0`, `Im w < 0`. -/
theorem re_mul_log_add_ge {w : ℂ} (hre : 0 ≤ w.re) (him : w.im < 0) :
    w.re * Real.log ‖w‖ ≤ (w * (Complex.log w + (Real.pi / 2 : ℝ) * I)).re := by
  have harg : -(Real.pi / 2) ≤ w.arg := (abs_le.mp (abs_arg_le_pi_div_two_iff.mpr hre)).1
  have e : (w * (Complex.log w + (Real.pi / 2 : ℝ) * I)).re =
      w.re * Real.log ‖w‖ - w.im * (w.arg + Real.pi / 2) := by
    simp [Complex.mul_re, Complex.log_re, Complex.log_im]
  rw [e]
  have : 0 ≤ -w.im * (w.arg + Real.pi / 2) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- `‖W_B(s)‖ ≤ ‖s − ½‖^{−B(Re s − ½)}`-type bound: `‖W_B(s)‖ ≤ exp(−B (Re s − ½) log‖s − ½‖)` on
`Re s ≥ ½`, `Im s < 0`, for `B ≥ 0`. -/
theorem norm_evapTwist_le_exp {B : ℝ} (hB : 0 ≤ B) {s : ℂ} (hs : 1 / 2 ≤ s.re) (him : s.im < 0) :
    ‖evapTwist B s‖ ≤ Real.exp (-(B * ((s.re - 1 / 2) * Real.log ‖s - 1 / 2‖))) := by
  unfold evapTwist
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hw := re_mul_log_add_ge (w := s - 1 / 2) (by simp; linarith) (by simpa using him)
  have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  rw [hre] at hw
  have e : (-((B : ℂ) * ((s - 1 / 2) * (Complex.log (s - 1 / 2) + (Real.pi / 2 : ℝ) * I)))).re =
      -(B * ((s - 1 / 2) * (Complex.log (s - 1 / 2) + (Real.pi / 2 : ℝ) * I)).re) := by
    simp [Complex.mul_re]
  rw [e]
  nlinarith

/-- `‖W_B(s)‖ ≤ 1` on the lower strip `Re s ≥ ½`, `Im s ≤ −1`. -/
theorem norm_evapTwist_le_one {B : ℝ} (hB : 0 ≤ B) {s : ℂ} (hs : 1 / 2 ≤ s.re) (him : s.im ≤ -1) :
    ‖evapTwist B s‖ ≤ 1 := by
  refine (norm_evapTwist_le_exp hB hs (by linarith)).trans ?_
  rw [Real.exp_le_one_iff]
  have h1 : 1 ≤ ‖s - 1 / 2‖ := by
    have h := Complex.abs_im_le_norm (s - 1 / 2)
    have him' : (s - 1 / 2).im = s.im := by simp
    rw [him', abs_of_neg (by linarith)] at h; linarith
  have hl : 0 ≤ Real.log ‖s - 1 / 2‖ := Real.log_nonneg h1
  have : 0 ≤ B * ((s.re - 1 / 2) * Real.log ‖s - 1 / 2‖) := by
    apply mul_nonneg hB; apply mul_nonneg (by linarith) hl
  linarith

/-- On `Re s = 3/2`: `‖W_B(3/2 + iy)‖ ≤ |y|^{−B}` for `y ≤ −1`. -/
theorem norm_evapTwist_three_halves_le {B : ℝ} (hB : 0 ≤ B) {y : ℝ} (hy : y ≤ -1) :
    ‖evapTwist B (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ |y| ^ (-B) := by
  set s : ℂ := ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hs
  have hre : s.re = 3 / 2 := by simp [hs]
  have him : s.im = y := by simp [hs]
  refine (norm_evapTwist_le_exp hB (by rw [hre]; norm_num) (by rw [him]; linarith)).trans ?_
  have hy0 : 0 < |y| := by rw [abs_of_neg (by linarith)]; linarith
  have hnorm : |y| ≤ ‖s - 1 / 2‖ := by
    have h := Complex.abs_im_le_norm (s - 1 / 2)
    have him' : (s - 1 / 2).im = y := by simp [hs]
    rwa [him'] at h
  rw [hre, Real.rpow_def_of_pos hy0]
  apply Real.exp_le_exp.mpr
  have hl : Real.log |y| ≤ Real.log ‖s - 1 / 2‖ := Real.log_le_log hy0 hnorm
  nlinarith

/-- On the lower critical line `W_B` is unimodular: `W_B(½ + 2it) = e^{2iB|t| log(2|t|)}`. -/
theorem evapTwist_lineS {B t : ℝ} (ht : t < 0) :
    evapTwist B (lineS t) = cexp (((2 * B * (-t) * Real.log (2 * (-t)) : ℝ) : ℂ) * I) := by
  unfold evapTwist
  congr 1
  have hw : lineS t - 1 / 2 = (((-(2 * t)) : ℝ) : ℂ) * (-I) := by
    rw [lineS_eq]; push_cast; ring
  have hpos : (0 : ℝ) < -(2 * t) := by linarith
  have hlog : Complex.log (lineS t - 1 / 2) =
      (Real.log (-(2 * t)) : ℂ) - (Real.pi / 2 : ℝ) * I := by
    rw [hw, Complex.log_ofReal_mul hpos (by simp), Complex.log_neg_I]
    push_cast; ring
  rw [hlog, hw]
  push_cast
  ring_nf

theorem norm_evapTwist_lineS {B t : ℝ} (ht : t < 0) : ‖evapTwist B (lineS t)‖ = 1 := by
  rw [evapTwist_lineS ht, Complex.norm_exp_ofReal_mul_I]

/-! ### Regularity of the twist -/

/-- The exponent `(s − ½)(Log(s − ½) + iπ/2)` is continuous on `Re s ≥ ½`, including `s = ½`. -/
theorem continuousAt_evapExponent {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ContinuousAt (fun z : ℂ => (z - 1 / 2) * (Complex.log (z - 1 / 2) + (Real.pi / 2 : ℝ) * I))
      s := by
  by_cases hs0 : s = 1 / 2
  · subst hs0
    have hval : ((1 / 2 : ℂ) - 1 / 2) * (Complex.log ((1 / 2 : ℂ) - 1 / 2) +
        (Real.pi / 2 : ℝ) * I) = 0 := by simp
    rw [ContinuousAt, hval]
    have hw : Tendsto (fun z : ℂ => ‖z - 1 / 2‖) (𝓝 (1 / 2 : ℂ)) (𝓝 0) := by
      have h : Continuous (fun z : ℂ => ‖z - 1 / 2‖) := by fun_prop
      simpa using h.tendsto (1 / 2 : ℂ)
    have hml : Tendsto (fun z : ℂ => ‖z - 1 / 2‖ * Real.log ‖z - 1 / 2‖) (𝓝 (1 / 2 : ℂ))
        (𝓝 0) := by
      have h := (Real.continuous_mul_log.tendsto 0).comp hw
      simpa [Function.comp_def] using h
    have hg : Tendsto (fun z : ℂ => |‖z - 1 / 2‖ * Real.log ‖z - 1 / 2‖| +
        2 * Real.pi * ‖z - 1 / 2‖) (𝓝 (1 / 2 : ℂ)) (𝓝 0) := by
      have := hml.abs.add (hw.const_mul (2 * Real.pi))
      simpa using this
    refine squeeze_zero_norm (fun z => ?_) hg
    set w := z - 1 / 2
    have hlog : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + Real.pi := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [Complex.log_re, Complex.log_im]
      linarith [Complex.abs_arg_le_pi w]
    have hc : ‖((Real.pi / 2 : ℝ) : ℂ) * I‖ = Real.pi / 2 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    calc ‖w * (Complex.log w + ((Real.pi / 2 : ℝ) : ℂ) * I)‖
        ≤ ‖w‖ * (‖Complex.log w‖ + Real.pi / 2) := by
          rw [norm_mul]; gcongr; exact (norm_add_le _ _).trans (by rw [hc])
      _ ≤ ‖w‖ * (|Real.log ‖w‖| + Real.pi + Real.pi / 2) := by gcongr
      _ ≤ |‖w‖ * Real.log ‖w‖| + 2 * Real.pi * ‖w‖ := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg w)]
          nlinarith [norm_nonneg w, Real.pi_pos]
  · have hslit : s - 1 / 2 ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_cases hre : s.re = 1 / 2
      · right
        intro him
        apply hs0
        apply Complex.ext
        · simpa using hre
        · simpa using him
      · left
        have : 1 / 2 < s.re := lt_of_le_of_ne hs (Ne.symm hre)
        simp; linarith
    exact (continuousAt_id.sub continuousAt_const).mul
      (((continuousAt_id.sub continuousAt_const).clog hslit).add continuousAt_const)

theorem continuousAt_evapTwist (B : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ContinuousAt (evapTwist B) s := by
  unfold evapTwist
  exact ((continuousAt_const.mul (continuousAt_evapExponent hs)).neg).cexp

theorem hasDerivAt_evapTwist (B : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    HasDerivAt (evapTwist B)
      (evapTwist B s * (-((B : ℂ) * (Complex.log (s - 1 / 2) + (Real.pi / 2 : ℝ) * I + 1)))) s := by
  have hslit : s - 1 / 2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp; linarith
  have hne : s - 1 / 2 ≠ 0 := Complex.slitPlane_ne_zero hslit
  have h1 : HasDerivAt (fun z : ℂ => z - 1 / 2) 1 s := (hasDerivAt_id s).sub_const _
  have hlog := h1.clog hslit
  have hprod := h1.mul (hlog.add_const ((Real.pi / 2 : ℝ) * I))
  have hexp := ((hprod.const_mul (B : ℂ)).neg).cexp
  unfold evapTwist
  refine hexp.congr_deriv ?_
  have e : (s - 1 / 2) * (1 / (s - 1 / 2)) = 1 := mul_one_div_cancel hne
  simp only [Pi.neg_apply, Pi.mul_apply, e, one_mul]

/-- The evaporation-twisted producer `W_B · W_η · G`. -/
def evapG (B η : ℝ) (G : ℂ → ℂ) (s : ℂ) : ℂ := evapTwist B s * twistG η G s

theorem continuousAt_evapG {G : ℂ → ℂ} (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (B η : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) : ContinuousAt (evapG B η G) s :=
  (continuousAt_evapTwist B hs).mul (continuousAt_twistG hGc η hs)

theorem hasDerivAt_evapG {Φ G : ℂ → ℂ}
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (B η : ℝ) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    HasDerivAt (evapG B η G)
      ((Φ s - ((η / 2 : ℝ) : ℂ) -
        (B : ℂ) * (Complex.log (s - 1 / 2) + (Real.pi / 2 : ℝ) * I + 1)) * evapG B η G s) s := by
  have h := (hasDerivAt_evapTwist B hs).mul (hasDerivAt_twistG hGd η hs)
  refine h.congr_deriv ?_
  unfold evapG
  ring

theorem prodF_evapG (B η : ℝ) (G : ℂ → ℂ) (s : ℂ) :
    prodF (evapG B η G) s = evapTwist B s * prodF (twistG η G) s := by
  unfold prodF evapG; ring

theorem phiG_evapG (B η : ℝ) (G : ℂ → ℂ) (t : ℝ) :
    phiG (evapG B η G) t = evapTwist B (lineS t) * phiG (twistG η G) t := by
  unfold phiG evapG; ring

theorem edgeIntegrand_evapG (B η : ℝ) (G : ℂ → ℂ) (τ s : ℂ) :
    edgeIntegrand (evapG B η G) τ s = evapTwist B s * edgeIntegrand (twistG η G) τ s := by
  unfold edgeIntegrand; rw [prodF_evapG]; ring

/-! ### The contour shift on the lower half-line -/

theorem norm_horizontalEdge_le_lower {G : ℂ → ℂ} {CF ν : ℝ}
    (hF : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → y ≤ -2 →
      ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * (1 + |y|) ^ ν)
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {y : ℝ} (hy : y ≤ -2) :
    ‖∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + (y : ℂ) * I)‖ ≤
      CF * (1 + |y|) ^ ν * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
        Real.exp (-(|y| * (τ.re / ‖τ‖)))) := by
  have hbd : ∀ x ∈ Set.uIoc (1 / 2 : ℝ) (3 / 2), ‖edgeIntegrand G τ ((x : ℂ) + (y : ℂ) * I)‖ ≤
      CF * (1 + |y|) ^ ν * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
        Real.exp (-(|y| * (τ.re / ‖τ‖)))) := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    unfold edgeIntegrand
    rw [norm_mul]
    have hCF : 0 ≤ CF * (1 + |y|) ^ ν :=
      (norm_nonneg _).trans (hF x y (by linarith [hx.1]) hx.2 hy)
    exact mul_le_mul (hF x y (by linarith [hx.1]) hx.2 hy)
      (norm_offKernel_le hτre hτ1 (by linarith [hx.1]) hx.2
        (by rw [abs_of_neg (by linarith)]; linarith)) (norm_nonneg _) hCF
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rwa [show |(3 / 2 : ℝ) - 1 / 2| = 1 by norm_num, mul_one] at h

theorem setIntegral_Iic_radial_eq_of_lower {Φ G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) {CF M : ℝ} (hCF : 0 ≤ CF)
    (hF : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → y ≤ -2 →
      ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * (1 + |y|) ^ (1 / 2 : ℝ))
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖)
    (hedge : ∀ y : ℝ, y ≤ -1 → ‖edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      M * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * (τ.re / ‖τ‖)))))
    {b : ℝ} (hb : b ≤ -1)
    (hfint : IntegrableOn (fun t => phiG G t * pairKernel (2 * t) τ) (Iic b)) :
    ∫ t in Iic b, phiG G t * pairKernel (2 * t) τ = (1 / 2 : ℂ) *
      ((∫ y in Iic (2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) +
        I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)) := by
  have hpi := Real.pi_pos
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hτpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  have hδ0 : 0 < δ := div_pos hτre hτpos
  set K : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ with hK
  have hec : Continuous fun y : ℝ => edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hre : (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re = 3 / 2 := by simp
    have h0 : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    have h1 : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; norm_num at this
    refine ContinuousAt.comp (g := edgeIntegrand G τ) ?_ (by fun_prop)
    exact (continuousAt_prodF hGc (by rw [hre]; norm_num) h0 h1).mul
      (differentiableAt_offKernel hτ0 (by rw [hre]; norm_num) (by rw [hre]; norm_num)).continuousAt
  have heint : IntegrableOn (fun y : ℝ => edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      (Iic (2 * b)) := by
    have hdom : IntegrableOn (fun y : ℝ => M * K * ‖cexp ((δ : ℂ) * (y : ℂ))‖)
        (Iic (2 * b)) :=
      ((integrableOn_exp_mul_complex_Iic (a := (δ : ℂ)) (by simpa using hδ0) (2 * b)).norm).const_mul _
    refine hdom.mono' hec.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Iic).mpr
      (Eventually.of_forall fun y hy => ?_))
    have hy0 : y < 0 := by have : y ≤ 2 * b := hy; linarith
    have hy1 : 1 ≤ |y| := by rw [abs_of_neg hy0]; have : y ≤ 2 * b := hy; linarith
    have h := hedge y (by have : y ≤ 2 * b := hy; linarith)
    rw [Complex.norm_exp]
    have he : ((δ : ℂ) * (y : ℂ)).re = -(|y| * δ) := by
      rw [abs_of_neg hy0]; simp; ring
    rw [he]
    calc ‖edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
          M * (K * Real.exp (-(|y| * δ))) := h
      _ = M * K * Real.exp (-(|y| * δ)) := by ring
  -- the bottom edge vanishes
  have hbotb : ∀ a : ℝ, a ≤ -1 → ‖∫ x in (1 / 2 : ℝ)..(3 / 2),
      edgeIntegrand G τ ((x : ℂ) + ((2 * a : ℝ) : ℂ) * I)‖ ≤ CF * K * (2 / δ ^ 2) / |a| := by
    intro a ha
    have ha0 : 0 < |a| := by rw [abs_of_neg (by linarith)]; linarith
    have hu : 2 ≤ |2 * a| := by rw [abs_mul, abs_two]; rw [abs_of_neg (by linarith : a < 0)]; linarith
    have h := norm_horizontalEdge_le_lower hF hτre hτ1 (by linarith : 2 * a ≤ -2)
    set u : ℝ := |2 * a| with hu_def
    have hu1 : (1 + u) ^ (1 / 2 : ℝ) ≤ 1 + u := by
      calc (1 + u) ^ (1 / 2 : ℝ) ≤ (1 + u) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = 1 + u := Real.rpow_one _
    have hexp : Real.exp (-(u * δ)) ≤ 2 / (u * δ) ^ 2 := by
      have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ u * δ by positivity)
      have hpos : 0 < u * δ := by positivity
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div,
        div_le_iff₀ (by norm_num)]
      nlinarith [sq_nonneg (u * δ)]
    have hua : u = 2 * |a| := by rw [hu_def, abs_mul, abs_two]
    calc _ ≤ CF * (1 + u) ^ (1 / 2 : ℝ) * (K * Real.exp (-(u * δ))) := h
      _ ≤ CF * (1 + u) * (K * (2 / (u * δ) ^ 2)) := by
          gcongr
      _ ≤ CF * K * (2 / δ ^ 2) / |a| := by
          rw [hua]
          have hK0 : 0 ≤ K := by positivity
          have e : CF * (1 + 2 * |a|) * (K * (2 / (2 * |a| * δ) ^ 2)) =
              CF * K * (2 / δ ^ 2) * ((1 + 2 * |a|) / (4 * |a| ^ 2)) := by
            field_simp; ring
          rw [e, div_eq_mul_one_div (CF * K * (2 / δ ^ 2))]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) ha0]
          nlinarith
  have hbot : Tendsto (fun a : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2),
      edgeIntegrand G τ ((x : ℂ) + ((2 * a : ℝ) : ℂ) * I)) atBot (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun a : ℝ => CF * K * (2 / δ ^ 2) / |a|) ?_ ?_
    · filter_upwards [eventually_le_atBot (-1 : ℝ)] with a ha using hbotb a ha
    · have := (tendsto_inv_atTop_zero.comp tendsto_abs_atBot_atTop).const_mul (CF * K * (2 / δ ^ 2))
      rw [mul_zero] at this
      exact this.congr fun a => by simp [div_eq_mul_inv]
  -- pass to the limit
  have h1 : Tendsto (fun a : ℝ => ∫ t in a..b, phiG G t * pairKernel (2 * t) τ) atBot
      (𝓝 (∫ t in Iic b, phiG G t * pairKernel (2 * t) τ)) :=
    intervalIntegral_tendsto_integral_Iic b hfint tendsto_id
  have h2 : Tendsto (fun a : ℝ => ∫ y in (2 * a)..(2 * b),
      edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) atBot
      (𝓝 (∫ y in Iic (2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) :=
    intervalIntegral_tendsto_integral_Iic (2 * b) heint (tendsto_id.const_mul_atBot two_pos)
  set T : ℂ := ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)
    with hT
  have h3 := ((h2.sub (hbot.const_mul I)).add (tendsto_const_nhds (x := I * T))).const_mul
    (1 / 2 : ℂ)
  rw [mul_zero, sub_zero] at h3
  refine tendsto_nhds_unique h1 (h3.congr' ?_)
  filter_upwards [eventually_le_atBot b] with a ha
  rw [intervalIntegral_radial_eq hGc hGd hτ0 ha hb]



/-! ### The twisted radial integral vanishes -/

/-- `∫_{y ≤ −2} |y|^{−B} e^{−δ|y|} dy ≤ Γ(1 − B) δ^{B−1}` for `B < 1`. -/
theorem integral_rpow_exp_Iic_le {B δ : ℝ} (hB1 : B < 1) (hδ : 0 < δ) :
    ∫ y in Iic (-2 : ℝ), |y| ^ (-B) * Real.exp (-(|y| * δ)) ≤
      (1 / δ) ^ (1 - B) * Real.Gamma (1 - B) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (-B) * Real.exp (-(δ * x))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -B) (p := 1) (b := δ) (by linarith)
      le_rfl hδ
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  have e1 : ∫ y in Iic (-2 : ℝ), |y| ^ (-B) * Real.exp (-(|y| * δ)) =
      ∫ x in Ioi (2 : ℝ), x ^ (-B) * Real.exp (-(δ * x)) := by
    have h := integral_comp_neg_Iic (-2) (fun x : ℝ => x ^ (-B) * Real.exp (-(δ * x)))
    rw [neg_neg] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic fun y hy => ?_
    have hy0 : y < 0 := lt_of_le_of_lt hy (by norm_num)
    simp only [abs_of_neg hy0]
    ring_nf
  rw [e1]
  have hval := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 - B) (r := δ) (by linarith) hδ
  rw [show 1 - B - 1 = -B by ring] at hval
  rw [← hval]
  refine setIntegral_mono_set hint ?_ ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    positivity
  · exact (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2)).eventuallyLE

/-- **The evaporation-twisted radial integral tends to `0`.**  For a Herglotz producer, `B > 0`
and any `η`, `ε ∫_{t<0} W_B(½+2it) W_η(½+2it) F(½+2it) k(2t, ε + i) dt → 0`. -/
theorem tendsto_evap_radial {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {B : ℝ} (hB : 0 < B) (η : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ), evapTwist B (lineS t) *
      (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 0) := by
  have hpi := Real.pi_pos
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  obtain ⟨CF₀, hCF₀, hF₀⟩ := exists_norm_prodF_le hsl hΦre hid hGc hGd hG2
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
  set B' : ℝ := min B (1 / 2) with hB'
  have hB'0 : 0 < B' := lt_min hB (by norm_num)
  have hB'1 : B' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hB'B : B' ≤ B := min_le_left _ _
  set c₁ : ℝ := Real.exp (|η| / 2) with hc₁
  set c₂ : ℝ := Real.exp (-(η / 2)) with hc₂
  set K : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  set CF : ℝ := c₁ * CF₀ with hCF
  have hCF0 : 0 ≤ CF := by positivity
  -- the twisted function
  set H : ℂ → ℂ := evapG B η G with hH
  have hHc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt H s := fun s hs => continuousAt_evapG hGc B η hs
  have hHd := fun (s : ℂ) (hs : 1 / 2 < s.re) => hasDerivAt_evapG hGd B η hs
  have hF : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → y ≤ -2 →
      ‖prodF H ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * (1 + |y|) ^ (1 / 2 : ℝ) := by
    intro x y hx1 hx2 hy
    have hre : (1 / 2 : ℝ) ≤ ((x : ℂ) + (y : ℂ) * I).re := by simpa using hx1
    have hre2 : ((x : ℂ) + (y : ℂ) * I).re ≤ 3 / 2 := by simpa using hx2
    have him : ((x : ℂ) + (y : ℂ) * I).im ≤ -1 := by simp; linarith
    rw [hH, prodF_evapG, prodF_twistG, norm_mul, norm_mul, hCF]
    have h1 := norm_evapTwist_le_one hB.le hre him
    have h2 := norm_linTwist_strip_le η hre hre2
    have h3 := hF₀ x y hx1 hx2 (by rw [abs_of_neg (by linarith)]; linarith)
    calc ‖evapTwist B ((x : ℂ) + (y : ℂ) * I)‖ * (‖linTwist η ((x : ℂ) + (y : ℂ) * I)‖ *
          ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖)
        ≤ 1 * (c₁ * (CF₀ * (1 + |y|) ^ (1 / 2 : ℝ))) := by gcongr
      _ = c₁ * CF₀ * (1 + |y|) ^ (1 / 2 : ℝ) := by ring
  -- the near part
  have hnear : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0, evapTwist B (lineS t) *
      (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 0) := by
    refine (tendsto_eps_mul_setIntegral_Ioo (h := fun t => evapTwist B (lineS t) *
      phiG (twistG η G) t) (B := CB * 2 ^ N) (fun t ht => ?_) le_rfl).congr fun ε => ?_
    · rw [norm_mul, norm_evapTwist_lineS ht.2, one_mul, norm_phiG_twistG]
      have hta : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      refine (hpoly t).1.trans ?_
      gcongr; linarith
    · simp only [mul_assoc]
  -- the far part
  have hfar_bound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), evapTwist B (lineS t) *
        (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))‖ ≤
      (c₂ * Real.exp S * K * 2) * (2 ^ (1 - B') * Real.Gamma (1 - B')) * ε ^ B' +
        CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2) * ε := by
    intro ε hε hε1
    set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
    have hτre : τ.re = ε := by simp [hτ]
    have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
    have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = 1 := by simp [hτ]
      rw [him, abs_one] at h; exact h
    have hτ2 : ‖τ‖ ≤ 2 := by
      have h := norm_add_le (ε : ℂ) (((1 : ℕ) : ℂ) * I)
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Nat.cast_one, norm_one,
        Real.norm_eq_abs, abs_of_pos hε] at h
      have e : τ = (ε : ℂ) + 1 * I := by rw [hτ, Nat.cast_one]
      rw [e]; linarith
    have hτpos : 0 < ‖τ‖ := by linarith
    set δ : ℝ := τ.re / ‖τ‖ with hδ
    have hδ0 : 0 < δ := div_pos hτre0 hτpos
    have hδε : ε / 2 ≤ δ := by
      rw [hδ, hτre]; exact div_le_div_of_nonneg_left hε.le hτpos hτ2
    -- the edge bound on `Re s = 3/2`
    have hedge0 : ∀ y : ℝ, y ≤ -1 → ‖edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        |y| ^ (-B) * ((c₂ * Real.exp S) * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) := by
      intro y hy
      rw [hH, edgeIntegrand_evapG, edgeIntegrand_twistG, norm_mul, norm_mul]
      have hW := norm_evapTwist_three_halves_le hB.le hy
      have hL : ‖linTwist η (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ = c₂ := by
        rw [norm_linTwist]; simp only [hc₂]; congr 1; simp; ring
      have hE := norm_edgeIntegrand_three_halves_le hsl hid hGd hG2 hτre0 hτ1
        (show 1 ≤ |y| by rw [abs_of_neg (by linarith)]; linarith)
      rw [hL]
      have hE' : ‖edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
          Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ))) := hE
      calc ‖evapTwist B (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ *
            (c₂ * ‖edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖)
          ≤ |y| ^ (-B) * (c₂ * (Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ))))) := by
            gcongr
        _ = |y| ^ (-B) * ((c₂ * Real.exp S) * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) := by ring
    have hedge : ∀ y : ℝ, y ≤ -1 → ‖edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        (c₂ * Real.exp S) * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * (τ.re / ‖τ‖)))) := by
      intro y hy
      refine (hedge0 y hy).trans ?_
      have hy1 : 1 ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
      have hp : |y| ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
      have h0 : 0 ≤ (c₂ * Real.exp S) * (K * ‖τ‖ * Real.exp (-(|y| * δ))) := by positivity
      calc |y| ^ (-B) * ((c₂ * Real.exp S) * (K * ‖τ‖ * Real.exp (-(|y| * δ))))
          ≤ 1 * ((c₂ * Real.exp S) * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) := by gcongr
        _ = _ := by rw [one_mul, hδ, hK]
    -- integrability on the half-line
    have hfint : IntegrableOn (fun t => phiG H t * pairKernel (2 * t) τ) (Iic (-1)) := by
      have h := (MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2
        hτre0).integrableOn (s := Iic (-1))
      refine h.norm.mono' ?_ ((ae_restrict_iff' measurableSet_Iic).mpr
        (Filter.Eventually.of_forall fun t ht => ?_))
      · exact ((continuous_phiG hHc).mul (continuous_pairKernel_two_mul hτ0)).aestronglyMeasurable
      · have ht0 : t < 0 := lt_of_le_of_lt ht (by norm_num)
        rw [hH, phiG_evapG, norm_mul, norm_mul, norm_mul, norm_evapTwist_lineS ht0, one_mul,
          norm_phiG_twistG]
    have hcont := setIntegral_Iic_radial_eq_of_lower hHc hHd hCF0 hF hτre0 hτ1 hedge le_rfl hfint
    have hrewrite : ∫ t in Iic (-1 : ℝ), evapTwist B (lineS t) *
        (phiG (twistG η G) t * pairKernel (2 * t) τ) =
        ∫ t in Iic (-1 : ℝ), phiG H t * pairKernel (2 * t) τ := by
      refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
      rw [hH, phiG_evapG]; ring
    rw [hrewrite, hcont]
    -- the right edge
    have hright : ‖∫ y in Iic (2 * (-1 : ℝ)), edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        (c₂ * Real.exp S * K * 2) * ((1 / δ) ^ (1 - B') * Real.Gamma (1 - B')) := by
      have hg : IntegrableOn (fun y : ℝ => (c₂ * Real.exp S * K * ‖τ‖) *
          (|y| ^ (-B') * Real.exp (-(|y| * δ)))) (Iic (-2 : ℝ)) := by
        have hdom := ((integrableOn_exp_mul_complex_Iic (a := (δ : ℂ)) (by simpa using hδ0)
          (-2 : ℝ)).norm).const_mul (c₂ * Real.exp S * K * ‖τ‖)
        refine hdom.mono' (by fun_prop) ((ae_restrict_iff' measurableSet_Iic).mpr
          (Eventually.of_forall fun y hy => ?_))
        have hy0 : y < 0 := lt_of_le_of_lt hy (by norm_num)
        have hy1 : 1 ≤ |y| := by rw [abs_of_neg hy0]; have : y ≤ -2 := hy; linarith
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_exp]
        have he : ((δ : ℂ) * (y : ℂ)).re = -(|y| * δ) := by rw [abs_of_neg hy0]; simp; ring
        rw [he]
        have hp : |y| ^ (-B') ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
        have h0 : 0 ≤ c₂ * Real.exp S * K * ‖τ‖ := by positivity
        calc (c₂ * Real.exp S * K * ‖τ‖) * (|y| ^ (-B') * Real.exp (-(|y| * δ)))
            ≤ (c₂ * Real.exp S * K * ‖τ‖) * (1 * Real.exp (-(|y| * δ))) := by gcongr
          _ = _ := by ring
      have h : ‖∫ y in Iic (-2 : ℝ), edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
          ∫ y in Iic (-2 : ℝ), (c₂ * Real.exp S * K * ‖τ‖) *
            (|y| ^ (-B') * Real.exp (-(|y| * δ))) :=
        norm_integral_le_of_norm_le hg
          ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => ?_))
      · rw [show (2 * (-1 : ℝ)) = -2 by norm_num]
        refine h.trans ?_
        rw [integral_const_mul]
        have hI := integral_rpow_exp_Iic_le hB'1 hδ0
        have h0 : 0 ≤ c₂ * Real.exp S * K := by positivity
        have hτ2' : c₂ * Real.exp S * K * ‖τ‖ ≤ c₂ * Real.exp S * K * 2 :=
          mul_le_mul_of_nonneg_left hτ2 h0
        have hInn : 0 ≤ ∫ y in Iic (-2 : ℝ), |y| ^ (-B') * Real.exp (-(|y| * δ)) :=
          setIntegral_nonneg measurableSet_Iic fun y _ => by positivity
        exact mul_le_mul hτ2' hI hInn (by positivity)
      · have hy0 : y ≤ -2 := hy
        refine (hedge0 y (by linarith)).trans ?_
        have hy1 : 1 ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
        have hp : |y| ^ (-B) ≤ |y| ^ (-B') :=
          Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
        have h0 : 0 ≤ (c₂ * Real.exp S) * (K * ‖τ‖ * Real.exp (-(|y| * δ))) := by positivity
        calc |y| ^ (-B) * ((c₂ * Real.exp S) * (K * ‖τ‖ * Real.exp (-(|y| * δ))))
            ≤ |y| ^ (-B') * ((c₂ * Real.exp S) * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) := by gcongr
          _ = _ := by ring
    -- the top edge
    have htop : ‖∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand H τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖ ≤
        CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2) := by
      have h := norm_horizontalEdge_le_lower hF hτre0 hτ1 (y := 2 * (-1 : ℝ)) (by norm_num)
      refine h.trans ?_
      have habs : |2 * (-1 : ℝ)| = 2 := by norm_num
      rw [habs]
      have he : Real.exp (-(2 * (τ.re / ‖τ‖))) ≤ 1 := by
        rw [Real.exp_le_one_iff]; have := div_pos hτre0 hτpos; linarith
      have h0 : 0 ≤ CF * (1 + 2) ^ (1 / 2 : ℝ) := by positivity
      calc CF * (1 + 2) ^ (1 / 2 : ℝ) * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
            Real.exp (-(2 * (τ.re / ‖τ‖))))
          ≤ CF * (1 + 2) ^ (1 / 2 : ℝ) * (4 * Real.pi ^ (3 / 4 : ℝ) * 2 * 1) := by gcongr
        _ = CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2) := by rw [hK]; ring
    -- assemble
    have hpow : ε * (1 / δ) ^ (1 - B') ≤ 2 ^ (1 - B') * ε ^ B' := by
      have h1 : (1 / δ) ^ (1 - B') ≤ (2 / ε) ^ (1 - B') := by
        apply Real.rpow_le_rpow (by positivity)
        · rw [div_le_div_iff₀ hδ0 hε]; linarith
        · linarith
      calc ε * (1 / δ) ^ (1 - B') ≤ ε * (2 / ε) ^ (1 - B') := by gcongr
        _ = 2 ^ (1 - B') * ε ^ B' := by
          rw [Real.div_rpow (by norm_num) hε.le]
          have : ε ^ (1 - B') = ε / ε ^ B' := by
            rw [Real.rpow_sub hε, Real.rpow_one]
          rw [this]
          field_simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, norm_mul,
      show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
    have htri := norm_add_le (∫ y in Iic (2 * (-1 : ℝ)),
      edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      (I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand H τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I))
    rw [norm_mul (I : ℂ), Complex.norm_I, one_mul] at htri
    have hA : 0 ≤ c₂ * Real.exp S * K * 2 := by positivity
    calc ε * (1 / 2 * ‖(∫ y in Iic (2 * (-1 : ℝ)),
            edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) +
          I * ∫ x in (1 / 2 : ℝ)..(3 / 2),
            edgeIntegrand H τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖)
        ≤ ε * (1 / 2 * ((c₂ * Real.exp S * K * 2) * ((1 / δ) ^ (1 - B') * Real.Gamma (1 - B')) +
            CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2))) := by
          gcongr
          exact htri.trans (add_le_add hright htop)
      _ ≤ (c₂ * Real.exp S * K * 2) * (2 ^ (1 - B') * Real.Gamma (1 - B')) * ε ^ B' +
            CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2) * ε := by
          have hG0 : 0 ≤ Real.Gamma (1 - B') := (Real.Gamma_pos_of_pos (by linarith)).le
          have h1 : ε * ((c₂ * Real.exp S * K * 2) * ((1 / δ) ^ (1 - B') * Real.Gamma (1 - B'))) ≤
              (c₂ * Real.exp S * K * 2) * (2 ^ (1 - B') * Real.Gamma (1 - B')) * ε ^ B' := by
            calc ε * ((c₂ * Real.exp S * K * 2) * ((1 / δ) ^ (1 - B') * Real.Gamma (1 - B')))
                = (c₂ * Real.exp S * K * 2) * Real.Gamma (1 - B') * (ε * (1 / δ) ^ (1 - B')) := by
                  ring
              _ ≤ (c₂ * Real.exp S * K * 2) * Real.Gamma (1 - B') * (2 ^ (1 - B') * ε ^ B') := by
                  gcongr
              _ = _ := by ring
          have h2 : 0 ≤ CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2) * ε := by positivity
          have h3 : 0 ≤ (c₂ * Real.exp S * K * 2) * (2 ^ (1 - B') * Real.Gamma (1 - B')) *
              ε ^ B' := by positivity
          have e : ε * (1 / 2 * ((c₂ * Real.exp S * K * 2) * ((1 / δ) ^ (1 - B') *
              Real.Gamma (1 - B')) + CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2))) =
              1 / 2 * (ε * ((c₂ * Real.exp S * K * 2) * ((1 / δ) ^ (1 - B') *
                Real.Gamma (1 - B')))) + 1 / 2 * (CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2) * ε) := by
            ring
          rw [e]; linarith
  have hfar : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ), evapTwist B (lineS t) *
      (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 0) := by
    have hlim : Tendsto (fun ε : ℝ =>
        (c₂ * Real.exp S * K * 2) * (2 ^ (1 - B') * Real.Gamma (1 - B')) * ε ^ B' +
          CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2) * ε) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ => ε ^ B') (𝓝[>] 0) (𝓝 0) := by
        have h := ((Real.continuous_rpow_const hB'0.le).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        rwa [Real.zero_rpow hB'0.ne'] at h
      have h2 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)) (a := (0 : ℝ)))
      simpa using (h1.const_mul ((c₂ * Real.exp S * K * 2) * (2 ^ (1 - B') *
        Real.Gamma (1 - B')))).add (h2.const_mul (CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2)))
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
    exact hfar_bound ε hε.1 hε.2.le
  -- combine
  have hsum := hfar.add hnear
  rw [add_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  have hε' : (0 : ℝ) < ε := hε
  set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
  have hτre : 0 < τ.re := by simp [hτ]; exact hε'
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hint : IntegrableOn (fun t => evapTwist B (lineS t) * (phiG (twistG η G) t *
      pairKernel (2 * t) τ)) (Iio 0) := by
    have hphik := (integrable_phiG_twistG_mul_pairKernel hsl hΦre hid hGc hGd hG2 η hτre).integrableOn
      (s := Iio (0 : ℝ))
    refine hphik.norm.mono' ?_ ((ae_restrict_iff' measurableSet_Iio).mpr
      (Eventually.of_forall fun t ht => ?_))
    · have hc : Continuous fun t : ℝ => phiG H t * pairKernel (2 * t) τ :=
        (continuous_phiG fun s hs => continuousAt_evapG hGc B η hs).mul
          (continuous_pairKernel_two_mul hτ0)
      refine (hc.congr fun t => ?_).aestronglyMeasurable
      rw [hH, phiG_evapG]; ring
    · have ht0 : t < 0 := ht
      rw [norm_mul, norm_evapTwist_lineS ht0, one_mul]
  have hsplit : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
    ext t
    simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
    constructor
    · intro h
      by_cases h1 : t ≤ -1
      · exact Or.inl h1
      · exact Or.inr ⟨by linarith, h⟩
    · rintro (h | h)
      · linarith
      · exact h.2
  have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) 0) :=
    Set.disjoint_left.mpr fun t h1 h2 => by
      simp only [mem_Iic] at h1; simp only [mem_Ioo] at h2; linarith [h2.1]
  have h1 : IntegrableOn (fun t => evapTwist B (lineS t) * (phiG (twistG η G) t *
      pairKernel (2 * t) τ)) (Iic (-1)) := hint.mono_set (by rw [hsplit]; exact subset_union_left)
  have h2 : IntegrableOn (fun t => evapTwist B (lineS t) * (phiG (twistG η G) t *
      pairKernel (2 * t) τ)) (Ioo (-1) 0) := hint.mono_set (by rw [hsplit]; exact subset_union_right)
  simp only
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioo h1 h2]
  ring


/-! ### The theorem -/

/-- **Constant-rate evaporation locks are impossible.**  Let `G` be a Herglotz producer.  There
are no `B > 0`, `η` and `κ₀` with
`G(1 − s) = κ₀ e^{iη(−τ)} W_B(s) G(s)` for `s = ½ + 2iτ`, `τ < 0`,
i.e. no lower-line lock phase `η x + 2B x log(2x)` (`x = −τ`). -/
theorem evaporation_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {B η : ℝ} (hB : 0 < B) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ₀ * cexp (((η * (-τ) : ℝ) : ℂ) * I) * evapTwist B (lineS τ) * G (lineS τ)) :
    False := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  have hpi := Real.pi_pos
  have hβ : betaG G ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
      two_ne_zero
  set R : ℝ → ℂ := fun ε => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
    phiStar G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) with hR
  have hRlim : Tendsto R (𝓝[>] 0) (𝓝 (2 * betaG G)) := by
    have h := (tendsto_lower_reflected_radial hsl hΦre hidT hGc hGd hG2 (le_refl 1)).const_mul
      ((2 * Real.pi : ℝ) : ℂ)
    have hval : ((2 * Real.pi : ℝ) : ℂ) * (betaG G / (Real.pi : ℂ)) = 2 * betaG G := by
      have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
      push_cast; field_simp
    rw [hval] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_)
    set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
    unfold defectLaplace
    have hind : (fun t => (Iio (0 : ℝ)).indicator (phiStar G) t * pairKernel (2 * t) τ) =
        (Iio (0 : ℝ)).indicator (fun t => phiStar G t * pairKernel (2 * t) τ) := by
      funext t
      by_cases ht : t ∈ Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
    rw [hind, integral_indicator measurableSet_Iio]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    simp only [hR]
    linear_combination ((ε : ℂ) * ∫ t in Iio (0 : ℝ), phiStar G t * pairKernel (2 * t) τ) * h2pi
  have hR0 : Tendsto R (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_evap_radial hsl hΦre hidT hGc hGd hG2 hB η).const_mul κ₀
    rw [mul_zero] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_)
    simp only [hR]
    rw [← mul_assoc, mul_comm κ₀, mul_assoc, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
    have ht0 : t < 0 := ht
    rw [phiG_twistG, linTwist_lineS]
    simp only [phiStar, phiG]
    rw [hlock t ht0]
    ring
  have h0 : (2 : ℂ) * betaG G = 0 := tendsto_nhds_unique hRlim hR0
  exact hβ ((mul_eq_zero.mp h0).resolve_left two_ne_zero)

/-! ### Windows -/

/-- **A windowed lock with a vanishing twisted radial integral is impossible.**  Let `w` be bounded
and measurable.  If on windows `−Y_j ≤ τ ≤ −X_j` (`X_j → ∞`, `Y_j` super-polynomial in `X_j`)
`G(1 − s) = κ_j e^{iη(−τ)} w(τ) G(s)`, and `ε ∫_{t<0} w(t) φ_η(t) k(2t, ε + i) dt → 0`, then there is
no such producer. -/
theorem windowed_lock_impossible_of_tendsto {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {η K₀ Mw : ℝ} {w : ℝ → ℂ} (hwm : AEStronglyMeasurable w volume) (hwb : ∀ t, ‖w t‖ ≤ Mw)
    {X Y : ℕ → ℝ} {κ : ℕ → ℂ}
    (hX : Tendsto X atTop atTop) (hY : ∀ p : ℕ, ∀ᶠ j in atTop, (1 + X j) ^ p ≤ Y j)
    (hκ : ∀ j, ‖κ j‖ ≤ K₀)
    (hlock : ∀ j, ∀ τ : ℝ, -Y j ≤ τ → τ ≤ -X j →
      G (1 - lineS τ) = κ j * cexp (((η * (-τ) : ℝ) : ℂ) * I) * w τ * G (lineS τ))
    (hLw0 : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ), w t *
      (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 0)) :
    False := by
  have hpi := Real.pi_pos
  have hβ : betaG G ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
      two_ne_zero
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hidT hGc hGd hG2
  have hK₀ : 0 ≤ K₀ := (norm_nonneg _).trans (hκ 0)
  have hMw : 0 ≤ Mw := (norm_nonneg _).trans (hwb 0)
  set R : ℝ → ℂ := fun ε => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
    phiStar G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) with hR
  set Lw : ℝ → ℂ := fun ε => (ε : ℂ) * ∫ t in Iio (0 : ℝ), w t *
    (phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)) with hLw
  have hLlim : Tendsto Lw (𝓝[>] 0) (𝓝 0) := hLw0
  have hRlim : Tendsto R (𝓝[>] 0) (𝓝 (2 * betaG G)) := by
    have h := (tendsto_lower_reflected_radial hsl hΦre hidT hGc hGd hG2 (le_refl 1)).const_mul
      ((2 * Real.pi : ℝ) : ℂ)
    have hval : ((2 * Real.pi : ℝ) : ℂ) * (betaG G / (Real.pi : ℂ)) = 2 * betaG G := by
      have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
      push_cast; field_simp
    rw [hval] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_)
    set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
    unfold defectLaplace
    have hind : (fun t => (Iio (0 : ℝ)).indicator (phiStar G) t * pairKernel (2 * t) τ) =
        (Iio (0 : ℝ)).indicator (fun t => phiStar G t * pairKernel (2 * t) τ) := by
      funext t
      by_cases ht : t ∈ Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
    rw [hind, integral_indicator measurableSet_Iio]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    simp only [hR]
    linear_combination ((ε : ℂ) * ∫ t in Iio (0 : ℝ), phiStar G t * pairKernel (2 * t) τ) * h2pi
  -- the sequence `ε_j = (1 + X_j)^{−(N+2)}`
  set e : ℕ → ℝ := fun j => ((1 + X j) ^ (N + 2))⁻¹ with he
  have hXnn : ∀ᶠ j in atTop, 0 ≤ X j := hX.eventually_ge_atTop 0
  have he_pos : ∀ᶠ j in atTop, 0 < e j := hXnn.mono fun j hj => by
    simp only [he]; positivity
  have he_le : ∀ᶠ j in atTop, e j ≤ 1 := hXnn.mono fun j hj => by
    simp only [he]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have he0 : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => (1 + X j) ^ (N + 2)) atTop atTop :=
      (tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_left _ 1 hX)
    exact h1.inv_tendsto_atTop
  have he_within : Tendsto e atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨he0, he_pos⟩
  have hRe := hRlim.comp he_within
  have hLe := hLlim.comp he_within
  -- the window defect along the sequence
  set c : ℝ := 2 * ((N : ℝ) + 1) with hc
  set Md : ℝ := 3 * ((2 + K₀ * Mw) * CB) with hMd
  have hMd0 : 0 ≤ Md := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hbound : ∀ᶠ j in atTop, ‖R (e j) - κ j * Lw (e j)‖ ≤ Md / (1 + X j) +
      2 * Md * c ^ N * ((1 + X j) ^ ((N + 2) * N) * Real.exp (-((1 + X j) / 2))) := by
    filter_upwards [hXnn, hY 1, hY (N + 3), he_pos, he_le] with j hj hY1 hYN hej hej1
    have hXY : X j ≤ Y j := by rw [pow_one] at hY1; linarith
    have hest := norm_reflected_sub_twisted_le hGc (η := η) (hκ j) hwm hwb hCB hpoly hj hXY
      (hlock j) hej hej1
    refine hest.trans ?_
    have hP : 0 < 1 + X j := by linarith
    have hPN : 0 < (1 + X j) ^ (N + 2) := by positivity
    have t1 : e j * X j * (1 + X j) ^ N ≤ 1 / (1 + X j) := by
      simp only [he]
      rw [inv_mul_eq_div, div_mul_eq_mul_div, div_le_div_iff₀ hPN hP, one_mul]
      calc X j * (1 + X j) ^ N * (1 + X j) ≤ (1 + X j) * (1 + X j) ^ N * (1 + X j) := by
            gcongr; linarith
        _ = (1 + X j) ^ (N + 2) := by ring
    have heY : 1 + X j ≤ e j * Y j := by
      simp only [he]
      rw [inv_mul_eq_div, le_div_iff₀ hPN]
      calc (1 + X j) * (1 + X j) ^ (N + 2) = (1 + X j) ^ (N + 3) := by ring
        _ ≤ Y j := hYN
    have hcpow : (c / e j) ^ N = c ^ N * (1 + X j) ^ ((N + 2) * N) := by
      simp only [he]; rw [div_inv_eq_mul, mul_pow, pow_mul]
    have hexp : Real.exp (-(e j * Y j / 2)) ≤ Real.exp (-((1 + X j) / 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc Md * (e j * X j * (1 + X j) ^ N) + 2 * Md * ((c / e j) ^ N * Real.exp (-(e j * Y j / 2)))
        ≤ Md * (1 / (1 + X j)) +
            2 * Md * ((c ^ N * (1 + X j) ^ ((N + 2) * N)) * Real.exp (-((1 + X j) / 2))) := by
          rw [hcpow]; gcongr
      _ = Md / (1 + X j) +
            2 * Md * c ^ N * ((1 + X j) ^ ((N + 2) * N) * Real.exp (-((1 + X j) / 2))) := by
          ring
  have hdef : Tendsto (fun j => R (e j) - κ j * Lw (e j)) atTop (𝓝 0) :=
    squeeze_zero_norm' hbound ((tendsto_window_bound Md c N).comp hX)
  have hκL : Tendsto (fun j => κ j * Lw (e j)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => ?_) ((hLe.norm.const_mul K₀).trans (by simp))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hκ j) (norm_nonneg _)
  have hR0 : Tendsto (fun j => R (e j)) atTop (𝓝 0) := by
    have := hdef.add hκL
    rw [add_zero] at this
    exact this.congr fun j => by ring
  have h0 : (2 : ℂ) * betaG G = 0 := tendsto_nhds_unique hRe hR0
  exact hβ ((mul_eq_zero.mp h0).resolve_left two_ne_zero)


/-- **Windowed constant-rate evaporation is impossible.**  No Herglotz producer satisfies
`G(1 − s) = κ_j e^{iη(−τ)} W_B(s) G(s)` (`B > 0`) on windows `−Y_j ≤ τ ≤ −X_j` with `X_j → ∞` and
`Y_j ≥ (1 + X_j)^p` eventually for every `p`; the lock between the windows is arbitrary. -/
theorem windowed_evaporation_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {B η K₀ : ℝ} (hB : 0 < B) {X Y : ℕ → ℝ} {κ : ℕ → ℂ}
    (hX : Tendsto X atTop atTop) (hY : ∀ p : ℕ, ∀ᶠ j in atTop, (1 + X j) ^ p ≤ Y j)
    (hκ : ∀ j, ‖κ j‖ ≤ K₀)
    (hlock : ∀ j, ∀ τ : ℝ, -Y j ≤ τ → τ ≤ -X j →
      G (1 - lineS τ) = κ j * cexp (((η * (-τ) : ℝ) : ℂ) * I) * evapTwist B (lineS τ) *
        G (lineS τ)) :
    False := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  set w : ℝ → ℂ := (Iio (0 : ℝ)).indicator fun τ => evapTwist B (lineS τ) with hw
  have hwc : Continuous fun τ : ℝ => evapTwist B (lineS τ) := by
    refine continuous_iff_continuousAt.mpr fun τ => ?_
    have hl : Continuous lineS := by unfold lineS; fun_prop
    exact (continuousAt_evapTwist B (le_of_eq (lineS_re τ).symm)).comp hl.continuousAt
  have hwm : AEStronglyMeasurable w volume :=
    (hwc.measurable.indicator measurableSet_Iio).aestronglyMeasurable
  have hwb : ∀ t, ‖w t‖ ≤ 1 := by
    intro t
    by_cases ht : t < 0
    · rw [hw, Set.indicator_of_mem (show t ∈ Iio (0 : ℝ) from ht), norm_evapTwist_lineS ht]
    · rw [hw, Set.indicator_of_notMem (show t ∉ Iio (0 : ℝ) from ht), norm_zero]; norm_num
  have hXpos : ∀ᶠ j in atTop, 0 < X j := hX.eventually_gt_atTop 0
  obtain ⟨j₀, hj₀⟩ := hXpos.exists_forall_of_atTop
  -- shift the window sequence so that every window lies in `τ < 0`
  have hX' : Tendsto (fun j => X (j + j₀)) atTop atTop := hX.comp (tendsto_add_atTop_nat j₀)
  have hY' : ∀ p : ℕ, ∀ᶠ j in atTop, (1 + X (j + j₀)) ^ p ≤ Y (j + j₀) := fun p =>
    (tendsto_add_atTop_nat j₀).eventually (hY p)
  refine windowed_lock_impossible_of_tendsto hsl hΦd hΦre hidT hGc hGd hG2 (η := η) (K₀ := K₀)
    hwm hwb hX' hY' (fun j => hκ (j + j₀)) (fun j τ h1 h2 => ?_) ?_
  · have hτ0 : τ < 0 := by have := hj₀ (j + j₀) (by omega); linarith
    rw [hlock (j + j₀) τ h1 h2, hw, Set.indicator_of_mem (show τ ∈ Iio (0 : ℝ) from hτ0)]
  · refine (tendsto_evap_radial hsl hΦre hidT hGc hGd hG2 hB η).congr fun ε => ?_
    congr 1
    refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
    rw [hw, Set.indicator_of_mem ht]

end

end AbelianTwist

end RHTower
