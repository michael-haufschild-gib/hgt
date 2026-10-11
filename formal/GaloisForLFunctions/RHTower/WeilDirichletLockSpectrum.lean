import GaloisForLFunctions.RHTower.WeilLockSpectralTwist

/-!
# The Abel spectrum of a Dirichlet lock factor

Let `P : ℕ → ℂ` with `Σ_k |P(k)| < ∞`, and let `V(s) = Σ_k P(k) k^{−(s−½)}`.  On the critical line
`V(½ + it) = Σ_k P(k) k^{−it}` is an almost-periodic function whose frequencies `log k` are
logarithms of integers.  These are the frequencies that resonate with the Dirichlet coefficients of a
producer.  This file computes the edge Abel transforms of `V` that enter the spectral system
`twist_spectral_system`.

**Theorem** (`tendsto_dirLock_abel`).  For `m, n ≥ 1`,

`lim_{ε→0⁺} ε ∫_{y ≤ −2} V(3/2 + iy) e^{y(κ_{ε+im} − i log n)} dy = n P(m/n)` if `n ∣ m`, and `0`
otherwise.

**Proof.**  On `Re s = 3/2` the series converges absolutely, and the `k`-th term integrates to
`(P(k)/k) e^{−2w_k}/w_k` with `w_k = κ_{ε+im} − i log(nk)`.  The edge exponent satisfies
`Re κ_{ε+im} = ½ arcsin(2εm/(ε²+m²)) ~ ε/m` and `Im κ_{ε+im} = log m + O(ε²)`.  So `ε/w_k → m` if
`nk = m`, and `ε/w_k → 0` otherwise.  Tannery's theorem sums the limits.

`V` is continued to `Re s < ½` by `V(σ + it) = V(½ + it)`, which makes it continuous on `ℂ`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-! ### The edge exponent at `τ = ε + im` -/

theorem re_edgeExp_eps {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) (hεm : ε < m) :
    (edgeExp ((ε : ℂ) + (m : ℂ) * I)).re =
      Real.arcsin (2 * ε * m / (ε ^ 2 + (m : ℝ) ^ 2)) / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi := Real.pi_pos
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hx : (Real.pi : ℂ) * τ ^ 2 =
      ((Real.pi * (ε ^ 2 - (m : ℝ) ^ 2) : ℝ) : ℂ) + ((Real.pi * (2 * ε * m) : ℝ) : ℂ) * I := by
    rw [hτ]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hre : ((Real.pi : ℂ) * τ ^ 2).re = Real.pi * (ε ^ 2 - (m : ℝ) ^ 2) := by
    rw [hx]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have him : ((Real.pi : ℂ) * τ ^ 2).im = Real.pi * (2 * ε * m) := by
    rw [hx]
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have hnorm : ‖(Real.pi : ℂ) * τ ^ 2‖ = Real.pi * (ε ^ 2 + (m : ℝ) ^ 2) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi, Complex.sq_norm,
      Complex.normSq_apply]
    simp [hτ]; ring
  have hre0 : ((Real.pi : ℂ) * τ ^ 2).re < 0 := by
    rw [hre]
    have : ε ^ 2 < (m : ℝ) ^ 2 := by nlinarith
    nlinarith
  have him0 : 0 ≤ ((Real.pi : ℂ) * τ ^ 2).im := by
    rw [him]; exact mul_nonneg hpi.le (by positivity)
  rw [edgeExp_re, Complex.arg_of_re_neg_of_im_nonneg hre0 him0, Complex.neg_im, him, hnorm]
  have hden : 0 < ε ^ 2 + (m : ℝ) ^ 2 := by positivity
  have : -(Real.pi * (2 * ε * m)) / (Real.pi * (ε ^ 2 + (m : ℝ) ^ 2)) =
      -(2 * ε * m / (ε ^ 2 + (m : ℝ) ^ 2)) := by
    field_simp
  rw [this, Real.arcsin_neg]; ring

theorem hasDerivAt_edgeArcsin {m : ℕ} (hm : 1 ≤ m) :
    HasDerivAt (fun ε : ℝ => Real.arcsin (2 * ε * m / (ε ^ 2 + (m : ℝ) ^ 2)) / 2) (1 / (m : ℝ)) 0 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hg : HasDerivAt (fun ε : ℝ => 2 * ε * m / (ε ^ 2 + (m : ℝ) ^ 2)) (2 / (m : ℝ)) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => 2 * ε * m) (2 * m) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (m : ℝ)
    have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 + (m : ℝ) ^ 2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).add_const ((m : ℝ) ^ 2)
    have h := h1.div h2 (by positivity)
    have e : (2 * (m : ℝ) * ((0 : ℝ) ^ 2 + (m : ℝ) ^ 2) - 2 * 0 * m * 0) /
        ((0 : ℝ) ^ 2 + (m : ℝ) ^ 2) ^ 2 = 2 / (m : ℝ) := by
      field_simp
      ring
    rw [e] at h
    exact h
  have ha : HasDerivAt Real.arcsin 1 (2 * (0 : ℝ) * m / ((0 : ℝ) ^ 2 + (m : ℝ) ^ 2)) := by
    have : (2 * (0 : ℝ) * m / ((0 : ℝ) ^ 2 + (m : ℝ) ^ 2)) = 0 := by simp
    rw [this]
    simpa using Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
  have h := (ha.comp (0 : ℝ) hg).div_const 2
  have e : (1 : ℝ) * (2 / (m : ℝ)) / 2 = 1 / m := by field_simp
  rw [e] at h
  exact h

/-- `Re κ_{ε+im}/ε → 1/m`. -/
theorem tendsto_re_edgeExp_div {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (edgeExp ((ε : ℂ) + (m : ℂ) * I)).re / ε) (𝓝[>] 0)
      (𝓝 (1 / (m : ℝ))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  refine (hasDerivAt_edgeArcsin hm).tendsto_slope_zero_right.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hm0] with ε hε
  rw [re_edgeExp_eps hm hε.1 hε.2]
  simp [smul_eq_mul, div_eq_inv_mul]

/-- `(Im κ_{ε+im} − log m)/ε → 0`. -/
theorem tendsto_log_norm_sub_div {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (Real.log ‖(ε : ℂ) + (m : ℂ) * I‖ - Real.log m) / ε) (𝓝[>] 0)
      (𝓝 0) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : HasDerivAt (fun ε : ℝ => Real.log (ε ^ 2 + (m : ℝ) ^ 2) / 2) 0 0 := by
    have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 + (m : ℝ) ^ 2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).add_const ((m : ℝ) ^ 2)
    simpa using (h2.log (by positivity)).div_const 2
  refine hd.tendsto_slope_zero_right.congr' (Eventually.of_forall fun ε => ?_)
  have hn : ‖(ε : ℂ) + (m : ℂ) * I‖ = Real.sqrt (ε ^ 2 + (m : ℝ) ^ 2) := by
    rw [← Complex.norm_add_mul_I]; push_cast; rfl
  have hlm : Real.log ((0 : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2 = Real.log m := by
    rw [zero_pow two_ne_zero, zero_add, Real.log_pow]; push_cast; ring
  simp only [zero_add, smul_eq_mul]
  rw [hn, Real.log_sqrt (by positivity), ← hlm]
  ring

/-- `(κ_{ε+im} − i log m)/ε → 1/m`. -/
theorem tendsto_edgeExp_sub_div {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log m : ℝ) : ℂ) * I) / (ε : ℂ))
      (𝓝[>] 0) (𝓝 ((1 / m : ℝ) : ℂ)) := by
  have h1 := (Complex.continuous_ofReal.tendsto _).comp (tendsto_re_edgeExp_div hm)
  have h2 := (Complex.continuous_ofReal.tendsto _).comp (tendsto_log_norm_sub_div hm)
  have h := h1.add (h2.mul_const I)
  simp only [Function.comp_def, Complex.ofReal_zero, zero_mul, add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0 : ℝ) < ε from hε))
  have hk : edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log m : ℝ) : ℂ) * I =
      (((edgeExp ((ε : ℂ) + (m : ℂ) * I)).re : ℝ) : ℂ) +
        (((Real.log ‖(ε : ℂ) + (m : ℂ) * I‖ - Real.log m : ℝ)) : ℂ) * I := by
    apply Complex.ext <;> simp [edgeExp_im]
  rw [hk]
  push_cast
  field_simp

/-- `ε/(κ_{ε+im} − i log m) → m`. -/
theorem tendsto_eps_div_edgeExp_sub {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) / (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log m : ℝ) : ℂ) * I))
      (𝓝[>] 0) (𝓝 (m : ℂ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hne : ((1 / m : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have h := (tendsto_edgeExp_sub_div hm).inv₀ hne
  have hv : ((1 / m : ℝ) : ℂ)⁻¹ = (m : ℂ) := by push_cast; simp
  rw [hv] at h
  refine h.congr' (Eventually.of_forall fun ε => ?_)
  rw [inv_div]

/-- `κ_{ε+im} → i log m`. -/
theorem tendsto_edgeExp_eps {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => edgeExp ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0)
      (𝓝 (((Real.log m : ℝ) : ℂ) * I)) := by
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
    simpa using this
  have h := (hε.mul (tendsto_edgeExp_sub_div hm)).add_const (((Real.log m : ℝ) : ℂ) * I)
  rw [zero_mul, zero_add] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε'
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0 : ℝ) < ε from hε'))
  field_simp
  ring

/-! ### The lock factor -/

/-- The real part clamped to `[½, ∞)`. -/
def clampHalf (s : ℂ) : ℂ := ((max s.re (1 / 2) : ℝ) : ℂ) + (s.im : ℂ) * I

theorem clampHalf_of_le {s : ℂ} (hs : 1 / 2 ≤ s.re) : clampHalf s = s := by
  unfold clampHalf; rw [max_eq_left hs]; exact Complex.re_add_im s

theorem continuous_clampHalf : Continuous clampHalf := by
  unfold clampHalf
  exact (Complex.continuous_ofReal.comp (Complex.continuous_re.max continuous_const)).add
    ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)

theorem re_clampHalf (s : ℂ) : (clampHalf s).re = max s.re (1 / 2) := by simp [clampHalf]

/-- The Dirichlet lock factor `V(s) = Σ_k P(k) k^{−(s−½)}`, continued to `Re s < ½` by
`V(σ + it) = V(½ + it)`. -/
def dirLock (P : ℕ → ℂ) (s : ℂ) : ℂ := LSeries P (clampHalf s - 1 / 2)

theorem dirLock_of_le (P : ℕ → ℂ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    dirLock P s = LSeries P (s - 1 / 2) := by
  rw [dirLock, clampHalf_of_le hs]

theorem dirLock_edgePt (P : ℕ → ℂ) (y : ℝ) : dirLock P (edgePt y) = LSeries P (1 + (y : ℂ) * I) := by
  rw [dirLock_of_le P (by rw [edgePt_re]; norm_num)]
  unfold edgePt; push_cast; ring_nf

theorem norm_term_le_of_nonneg (P : ℕ → ℂ) {z : ℂ} (hz : 0 ≤ z.re) (k : ℕ) :
    ‖LSeries.term P z k‖ ≤ ‖P k‖ := by
  refine (LSeries.norm_term_le_of_re_le_re P (s := 0) (by simpa using hz) k).trans ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [LSeries.term_of_ne_zero hk, Complex.cpow_zero, div_one]

theorem lseriesSummable_of_nonneg {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {z : ℂ}
    (hz : 0 ≤ z.re) : LSeriesSummable P z :=
  Summable.of_norm_bounded hP (norm_term_le_of_nonneg P hz)

theorem norm_LSeries_le_of_nonneg {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {z : ℂ}
    (hz : 0 ≤ z.re) : ‖LSeries P z‖ ≤ ∑' k, ‖P k‖ :=
  (norm_tsum_le_tsum_norm (lseriesSummable_of_nonneg hP hz).norm).trans
    (Summable.tsum_le_tsum (norm_term_le_of_nonneg P hz) (lseriesSummable_of_nonneg hP hz).norm hP)

theorem continuousOn_LSeries_of_summable {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) :
    ContinuousOn (LSeries P) {z : ℂ | 0 ≤ z.re} := by
  refine continuousOn_tsum (f := fun k z => LSeries.term P z k) (u := fun k => ‖P k‖) ?_ hP
    fun k z hz => norm_term_le_of_nonneg P hz k
  intro k
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [LSeries.term_zero]; exact continuousOn_const
  · have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have : (fun z => LSeries.term P z k) = fun z => P k / (k : ℂ) ^ z :=
      funext fun z => LSeries.term_of_ne_zero hk P z
    rw [this]
    exact (continuousOn_const.div (continuous_id.const_cpow (Or.inl hk0)).continuousOn
      fun z _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hk0))

theorem continuous_dirLock {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) : Continuous (dirLock P) := by
  refine (continuousOn_LSeries_of_summable hP).comp_continuous
    (continuous_clampHalf.sub continuous_const) fun s => ?_
  show 0 ≤ (clampHalf s - 1 / 2).re
  rw [Complex.sub_re, re_clampHalf]
  have := le_max_right s.re (1 / 2)
  norm_num at this ⊢

theorem norm_dirLock_le {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) (s : ℂ) :
    ‖dirLock P s‖ ≤ ∑' k, ‖P k‖ := by
  refine norm_LSeries_le_of_nonneg hP ?_
  rw [Complex.sub_re, re_clampHalf]
  have := le_max_right s.re (1 / 2)
  norm_num at this ⊢

theorem differentiableAt_dirLock {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {s : ℂ}
    (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (dirLock P) s := by
  have habs : LSeries.abscissaOfAbsConv P ≤ ((0 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      lseriesSummable_of_nonneg hP (by simpa using hy.le)
  have hlt : LSeries.abscissaOfAbsConv P < ((s - 1 / 2).re : EReal) := by
    refine lt_of_le_of_lt habs ?_
    have : (0 : ℝ) < (s - 1 / 2).re := by
      rw [Complex.sub_re]; norm_num; linarith
    exact_mod_cast this
  have hL : DifferentiableAt ℂ (fun z => LSeries P (z - 1 / 2)) s :=
    (LSeries_hasDerivAt hlt).differentiableAt.comp s (differentiableAt_id.sub_const _)
  refine hL.congr_of_eventuallyEq ?_
  have ho : {z : ℂ | 1 / 2 < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [ho] with z hz
  exact dirLock_of_le P (le_of_lt hz)

/-! ### The edge Abel integral -/

theorem term_one_add_mul_exp (P : ℕ → ℂ) {k : ℕ} (hk : k ≠ 0) (y : ℝ) (w : ℂ) :
    LSeries.term P (1 + (y : ℂ) * I) k * cexp ((y : ℂ) * w) =
      P k / k * cexp ((y : ℂ) * (w - ((Real.log k : ℝ) : ℂ) * I)) := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [LSeries.term_of_ne_zero hk, Complex.cpow_def_of_ne_zero hk0, ← Complex.natCast_log]
  have he : cexp (((Real.log k : ℝ) : ℂ) * (1 + (y : ℂ) * I)) =
      (k : ℂ) * cexp (((Real.log k : ℝ) : ℂ) * ((y : ℂ) * I)) := by
    rw [mul_add, mul_one, Complex.exp_add, Complex.natCast_log, Complex.exp_log hk0]
  rw [he]
  have : cexp ((y : ℂ) * (w - ((Real.log k : ℝ) : ℂ) * I)) =
      cexp ((y : ℂ) * w) / cexp (((Real.log k : ℝ) : ℂ) * ((y : ℂ) * I)) := by
    rw [← Complex.exp_sub]; congr 1; ring
  rw [this]
  have hex : cexp (((Real.log k : ℝ) : ℂ) * ((y : ℂ) * I)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- The `k`-th edge Abel integral `(P(k)/k) e^{−2(w − i log k)}/(w − i log k)`. -/
def dirAbel (P : ℕ → ℂ) (w : ℂ) (k : ℕ) : ℂ :=
  if k = 0 then 0 else
    P k / k * (cexp ((w - ((Real.log k : ℝ) : ℂ) * I) * ((-2 : ℝ) : ℂ)) /
      (w - ((Real.log k : ℝ) : ℂ) * I))

theorem integral_LSeries_mul_exp {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {w : ℂ}
    (hw : 0 < w.re) :
    ∫ y in Iic (-2 : ℝ), LSeries P (1 + (y : ℂ) * I) * cexp ((y : ℂ) * w) = ∑' k, dirAbel P w k := by
  set F : ℕ → ℝ → ℂ := fun k y => LSeries.term P (1 + (y : ℂ) * I) k * cexp ((y : ℂ) * w) with hF
  have hre : ∀ k : ℕ, (w - ((Real.log k : ℝ) : ℂ) * I).re = w.re := by
    intro k
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have hnorm : ∀ k y, ‖F k y‖ = ‖P k / k‖ * Real.exp (w.re * y) := by
    intro k y
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hF]
    · simp only [hF]
      rw [term_one_add_mul_exp P hk, norm_mul, Complex.norm_exp]
      congr 2
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre]
      ring
  have hexpInt : IntegrableOn (fun y : ℝ => Real.exp (w.re * y)) (Iic (-2 : ℝ)) := by
    have h : IntegrableOn (fun y : ℝ => ‖cexp ((w.re : ℂ) * (y : ℂ))‖) (Iic (-2 : ℝ)) :=
      (integrableOn_exp_mul_complex_Iic (a := (w.re : ℂ)) (by simpa using hw) (-2)).norm
    refine h.congr_fun (fun y _ => ?_) measurableSet_Iic
    simp only
    rw [Complex.norm_exp]
    congr 1; simp
  have hcF : ∀ k, Continuous (F k) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · have : F 0 = fun _ => 0 := funext fun y => by simp [hF]
      rw [this]; exact continuous_const
    · have : F k = fun y : ℝ => P k / k * cexp ((y : ℂ) * (w - ((Real.log k : ℝ) : ℂ) * I)) :=
        funext fun y => term_one_add_mul_exp P hk y w
      rw [this]; fun_prop
  have hFint : ∀ k, Integrable (F k) (volume.restrict (Iic (-2 : ℝ))) := by
    intro k
    refine (hexpInt.const_mul ‖P k / k‖).mono' ((hcF k).aestronglyMeasurable) ?_
    exact Eventually.of_forall fun y => le_of_eq (hnorm k y)
  have hInorm : ∀ k, ∫ y in Iic (-2 : ℝ), ‖F k y‖ =
      ‖P k / k‖ * (Real.exp (w.re * (-2)) / w.re) := by
    intro k
    simp only [hnorm]
    rw [integral_const_mul, integral_exp_mul_Iic_real hw]
  have hPk : ∀ k : ℕ, ‖P k / k‖ ≤ ‖P k‖ := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · rw [norm_div, Complex.norm_natCast]
      exact div_le_self (norm_nonneg _) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)
  have hsum : Summable fun k => ∫ y in Iic (-2 : ℝ), ‖F k y‖ := by
    simp only [hInorm]
    exact Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => mul_le_mul_of_nonneg_right (hPk k) (by positivity)) (hP.mul_right _)
  have hlhs : (fun y : ℝ => LSeries P (1 + (y : ℂ) * I) * cexp ((y : ℂ) * w)) =
      fun y => ∑' k, F k y := by
    funext y
    simp only [hF, LSeries]
    rw [tsum_mul_right]
  rw [hlhs, ← integral_tsum_of_summable_integral_norm hFint hsum]
  congr 1
  funext k
  rcases eq_or_ne k 0 with rfl | hk
  · simp [hF, dirAbel]
  · have : F k = fun y : ℝ => P k / k * cexp ((w - ((Real.log k : ℝ) : ℂ) * I) * (y : ℂ)) :=
      funext fun y => by
        simp only [hF]; rw [term_one_add_mul_exp P hk y w, mul_comm (y : ℂ)]
    rw [this, integral_const_mul, integral_exp_mul_complex_Iic (by rw [hre]; exact hw)]
    simp [dirAbel, hk]

/-! ### The Abel limit -/

/-- The edge Abel spectrum of a Dirichlet lock factor: `n P(m/n)` if `n ∣ m`, else `0`. -/
def dirSpec (P : ℕ → ℂ) (m n : ℕ) : ℂ := if n ∣ m then (n : ℂ) * P (m / n) else 0

theorem tsum_resonant (P : ℕ → ℂ) {m n : ℕ} (hn : 1 ≤ n) :
    ∑' k, (if n * k = m then (n : ℂ) * P k else 0) = dirSpec P m n := by
  unfold dirSpec
  split_ifs with hd
  · obtain ⟨q, hq⟩ := hd
    rw [tsum_eq_single q]
    · rw [if_pos hq.symm, hq, Nat.mul_div_cancel_left q (by omega)]
    · intro k hk
      rw [if_neg]
      intro h
      exact hk (Nat.eq_of_mul_eq_mul_left (by omega) (h.trans hq))
  · have : ∀ k, (if n * k = m then (n : ℂ) * P k else 0) = 0 :=
      fun k => if_neg fun h => hd ⟨k, h.symm⟩
    simp only [this, tsum_zero]

/-- The log-frequency offset `log m − log n − log k` vanishes only at resonance `nk = m`. -/
theorem log_offset_ne_zero {m n k : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hk : 1 ≤ k) (h : n * k ≠ m) :
    ((Real.log m : ℝ) : ℂ) * I - ((Real.log n : ℝ) : ℂ) * I - ((Real.log k : ℝ) : ℂ) * I ≠ 0 := by
  intro h0
  have hre : (((Real.log m - Real.log n - Real.log k : ℝ)) : ℂ) * I = 0 := by
    rw [← h0]; push_cast; ring
  have hr : Real.log m - Real.log n - Real.log k = 0 := by
    rcases mul_eq_zero.mp hre with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 Complex.I_ne_zero
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log m = Real.log ((n : ℝ) * k) := by
    rw [Real.log_mul hn0.ne' hk0.ne']; linarith
  have heq : (m : ℝ) = (n : ℝ) * k :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hm0) (Set.mem_Ioi.mpr (mul_pos hn0 hk0)) hlog
  exact h (by exact_mod_cast heq.symm)

/-- **The edge Abel spectrum of `V(s) = Σ P(k)k^{−(s−½)}`.** -/
theorem tendsto_dirLock_abel {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ y in Iic (-2 : ℝ), dirLock P (edgePt y) *
      cexp ((y : ℂ) * (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 (dirSpec P m n)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set κ : ℝ → ℂ := fun ε => edgeExp ((ε : ℂ) + (m : ℂ) * I) with hκ
  have hreκ : ∀ ε : ℝ, ∀ k : ℕ,
      (κ ε - ((Real.log n : ℝ) : ℂ) * I - ((Real.log k : ℝ) : ℂ) * I).re = (κ ε).re := by
    intro ε k
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ 1 / (2 * (m : ℝ)) < (κ ε).re / ε := by
    have h1 : 1 / (2 * (m : ℝ)) < 1 / m := by
      rw [div_lt_div_iff_of_pos_left one_pos (by positivity) hm0]; linarith
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_re_edgeExp_div hm).eventually (lt_mem_nhds h1)] with ε hε h
    exact ⟨hε, h⟩
  have hfacts : ∀ ε : ℝ, 0 < ε → 1 / (2 * (m : ℝ)) < (κ ε).re / ε →
      0 < (κ ε).re ∧ ε / (κ ε).re ≤ 2 * m := by
    intro ε hε h
    have hpos : 0 < (κ ε).re := by
      have : 0 < (κ ε).re / ε := lt_trans (by positivity) h
      exact (div_pos_iff_of_pos_right hε).mp this
    refine ⟨hpos, ?_⟩
    rw [div_le_iff₀ hpos]
    rw [lt_div_iff₀ hε] at h
    have h2 : 2 * (m : ℝ) * (1 / (2 * m) * ε) = ε := by field_simp
    nlinarith
  set f : ℝ → ℕ → ℂ := fun ε k => (ε : ℂ) * dirAbel P (κ ε - ((Real.log n : ℝ) : ℂ) * I) k
    with hf
  set g : ℕ → ℂ := fun k => if n * k = m then (n : ℂ) * P k else 0 with hg
  have hsum_eq : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∑' k, f ε k = (ε : ℂ) * ∫ y in Iic (-2 : ℝ),
      dirLock P (edgePt y) * cexp ((y : ℂ) * (κ ε - ((Real.log n : ℝ) : ℂ) * I)) := by
    filter_upwards [hev] with ε hε
    obtain ⟨hpos, _⟩ := hfacts ε hε.1 hε.2
    have hw : 0 < (κ ε - ((Real.log n : ℝ) : ℂ) * I).re := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      linarith
    simp only [dirLock_edgePt]
    rw [integral_LSeries_mul_exp hP hw, ← tsum_mul_left]
  -- the limits of the terms
  have hκlim := tendsto_edgeExp_eps hm
  have hεlim : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
    simpa using this
  have hlim : ∀ k : ℕ, Tendsto (fun ε => f ε k) (𝓝[>] 0) (𝓝 (g k)) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · have hg0 : g 0 = 0 := by simp only [hg]; rw [if_neg (by omega)]
      rw [hg0]
      have h0 : ∀ ε, f ε 0 = 0 := fun ε => by simp [hf, dirAbel]
      simp only [h0]
      exact tendsto_const_nhds
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hfk : ∀ ε, f ε k = P k / k * (cexp ((κ ε - ((Real.log n : ℝ) : ℂ) * I -
        ((Real.log k : ℝ) : ℂ) * I) * ((-2 : ℝ) : ℂ)) * ((ε : ℂ) / (κ ε -
          ((Real.log n : ℝ) : ℂ) * I - ((Real.log k : ℝ) : ℂ) * I))) := by
      intro ε
      simp only [hf, dirAbel, if_neg hk]
      ring
    simp only [hfk]
    have hwlim : Tendsto (fun ε => κ ε - ((Real.log n : ℝ) : ℂ) * I - ((Real.log k : ℝ) : ℂ) * I)
        (𝓝[>] 0) (𝓝 (((Real.log m : ℝ) : ℂ) * I - ((Real.log n : ℝ) : ℂ) * I -
          ((Real.log k : ℝ) : ℂ) * I)) :=
      (hκlim.sub_const _).sub_const _
    by_cases hres : n * k = m
    · -- resonance
      have hlog : Real.log m = Real.log n + Real.log k := by
        rw [← hres]; push_cast
        exact Real.log_mul (by exact_mod_cast (show n ≠ 0 by omega)) (by exact_mod_cast hk)
      have hwm : ∀ ε, κ ε - ((Real.log n : ℝ) : ℂ) * I - ((Real.log k : ℝ) : ℂ) * I =
          κ ε - ((Real.log m : ℝ) : ℂ) * I := by
        intro ε; rw [hlog]; push_cast; ring
      have hc0 : ((Real.log m : ℝ) : ℂ) * I - ((Real.log n : ℝ) : ℂ) * I -
          ((Real.log k : ℝ) : ℂ) * I = 0 := by
        rw [hlog]; push_cast; ring
      have hexp : Tendsto (fun ε => cexp ((κ ε - ((Real.log n : ℝ) : ℂ) * I -
          ((Real.log k : ℝ) : ℂ) * I) * ((-2 : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 1) := by
        have := ((Complex.continuous_exp.tendsto _).comp (hwlim.mul_const ((-2 : ℝ) : ℂ)))
        rw [hc0, zero_mul, Complex.exp_zero] at this
        exact this
      have hdiv : Tendsto (fun ε : ℝ => (ε : ℂ) / (κ ε - ((Real.log n : ℝ) : ℂ) * I -
          ((Real.log k : ℝ) : ℂ) * I)) (𝓝[>] 0) (𝓝 (m : ℂ)) := by
        simp only [hwm]
        exact tendsto_eps_div_edgeExp_sub hm
      have hgk : g k = P k / k * (1 * (m : ℂ)) := by
        simp only [hg, if_pos hres]
        rw [← hres]; push_cast
        have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
        field_simp
      rw [hgk]
      exact (hexp.mul hdiv).const_mul _
    · -- no resonance
      have hc := log_offset_ne_zero hm hn hk1 hres
      have hgk : g k = 0 := by simp only [hg, if_neg hres]
      rw [hgk]
      have hq : Tendsto (fun ε => cexp ((κ ε - ((Real.log n : ℝ) : ℂ) * I -
          ((Real.log k : ℝ) : ℂ) * I) * ((-2 : ℝ) : ℂ)) / (κ ε - ((Real.log n : ℝ) : ℂ) * I -
            ((Real.log k : ℝ) : ℂ) * I)) (𝓝[>] 0) (𝓝 (cexp ((((Real.log m : ℝ) : ℂ) * I -
              ((Real.log n : ℝ) : ℂ) * I - ((Real.log k : ℝ) : ℂ) * I) * ((-2 : ℝ) : ℂ)) /
                (((Real.log m : ℝ) : ℂ) * I - ((Real.log n : ℝ) : ℂ) * I -
                  ((Real.log k : ℝ) : ℂ) * I))) :=
        ((Complex.continuous_exp.tendsto _).comp (hwlim.mul_const ((-2 : ℝ) : ℂ))).div hwlim hc
      have h := (hεlim.mul hq).const_mul (P k / k)
      rw [zero_mul, mul_zero] at h
      refine h.congr' (Eventually.of_forall fun ε => ?_)
      ring
  -- the dominating bound
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ k, ‖f ε k‖ ≤ 2 * m * ‖P k‖ := by
    filter_upwards [hev] with ε hε k
    obtain ⟨hpos, hq⟩ := hfacts ε hε.1 hε.2
    rcases eq_or_ne k 0 with rfl | hk
    · have h0 : f ε 0 = 0 := by simp [hf, dirAbel]
      rw [h0, norm_zero]; positivity
    set W : ℂ := κ ε - ((Real.log n : ℝ) : ℂ) * I - ((Real.log k : ℝ) : ℂ) * I with hW
    have hWre : W.re = (κ ε).re := hreκ ε k
    have hWn : (κ ε).re ≤ ‖W‖ := hWre ▸ Complex.re_le_norm W
    have hE : ‖cexp (W * ((-2 : ℝ) : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      have : (W * ((-2 : ℝ) : ℂ)).re = -2 * (κ ε).re := by
        rw [← hWre]; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
          sub_zero]; ring
      rw [this, Real.exp_le_one_iff]; linarith
    have hPk : ‖P k / k‖ ≤ ‖P k‖ := by
      rw [norm_div, Complex.norm_natCast]
      exact div_le_self (norm_nonneg _) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)
    have hf' : f ε k = (ε : ℂ) * (P k / k * (cexp (W * ((-2 : ℝ) : ℂ)) / W)) := by
      simp only [hf, dirAbel, if_neg hk, hW]
    rw [hf', norm_mul, norm_mul, norm_div (cexp (W * ((-2 : ℝ) : ℂ))) W, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε.1]
    have hW0 : 0 < ‖W‖ := lt_of_lt_of_le hpos hWn
    have h1 : ‖cexp (W * ((-2 : ℝ) : ℂ))‖ / ‖W‖ ≤ 1 / (κ ε).re :=
      div_le_div₀ zero_le_one hE hpos hWn
    calc ε * (‖P k / ↑k‖ * (‖cexp (W * ((-2 : ℝ) : ℂ))‖ / ‖W‖))
        ≤ ε * (‖P k‖ * (1 / (κ ε).re)) := by have := hε.1.le; gcongr
      _ = ‖P k‖ * (ε / (κ ε).re) := by ring
      _ ≤ ‖P k‖ * (2 * m) := by gcongr
      _ = 2 * m * ‖P k‖ := by ring
  have hT := tendsto_tsum_of_dominated_convergence (hP.mul_left (2 * (m : ℝ))) hlim hbound
  rw [tsum_resonant P hn] at hT
  exact hT.congr' hsum_eq

/-! ### The divisor system and the Dirichlet factorization -/

/-- The half-shifted coefficients `a(n) n^{−1/2}`. -/
def halfCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ := a n / (n : ℂ) ^ (1 / 2 : ℂ)

theorem term_three_halves_mul (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term a (((3 / 2 : ℝ) : ℂ)) n * n = halfCoeff a n := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [LSeries.term_of_ne_zero hn, halfCoeff]
  have h32 : (n : ℂ) ^ (((3 / 2 : ℝ) : ℂ)) = (n : ℂ) ^ (1 / 2 : ℂ) * n := by
    have h : (((3 / 2 : ℝ) : ℂ)) = 1 / 2 + 1 := by push_cast; norm_num
    rw [h, Complex.cpow_add _ _ hn0, Complex.cpow_one]
  rw [h32]
  have : (n : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn0)
  field_simp

theorem tsum_term_dirSpec (a P : ℕ → ℂ) {m : ℕ} (hm : 1 ≤ m) :
    ∑' n, LSeries.term a (((3 / 2 : ℝ) : ℂ)) n * dirSpec P m n =
      LSeries.convolution (halfCoeff a) P m := by
  rw [tsum_eq_sum (s := m.divisors)]
  · rw [LSeries.convolution_def]
    show _ = ∑ p ∈ m.divisorsAntidiagonal, halfCoeff a p.1 * P p.2
    rw [Nat.sum_divisorsAntidiagonal (fun i j => halfCoeff a i * P j)]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hd : n ∣ m := (Nat.mem_divisors.mp hn).1
    have hn0 : n ≠ 0 := (Nat.pos_of_mem_divisors hn).ne'
    rw [dirSpec, if_pos hd, ← mul_assoc, term_three_halves_mul a hn0]
  · intro n hn
    have : ¬ n ∣ m := fun hd => hn (Nat.mem_divisors.mpr ⟨hd, by omega⟩)
    rw [dirSpec, if_neg this, mul_zero]

/-- **The divisor system from an integer-resonant Abel spectrum.**  If `G(1 − s) = V(s) G(s)` on the
lower critical line and the edge Abel spectrum of `V` at frequency `m` is `n P(m/n)` (for `n ∣ m`,
and `0` otherwise), then `√m Σ_{n ∣ m} a(n) n^{−1/2} P(m/n) = G(1)`. -/
theorem divisor_system_of_spec {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {V : ℂ → ℂ} (hVc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im < 0 → ContinuousAt V s)
    (hVd : ∀ s : ℂ, 1 / 2 < s.re → s.re < 3 / 2 → s.im < 0 → DifferentiableAt ℂ V s) {A : ℝ}
    (hVs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → ‖V s‖ ≤ Real.exp A)
    (hVl : ∀ t : ℝ, t < 0 → ‖V (lineS t)‖ ≤ Real.exp A)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = V (lineS τ) * G (lineS τ))
    {P : ℕ → ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hspec : ∀ n : ℕ, 1 ≤ n → Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ y in Iic (-2 : ℝ),
      V (edgePt y) * cexp ((y : ℂ) *
        (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 (dirSpec P m n))) :
    ((Real.sqrt m : ℝ) : ℂ) * LSeries.convolution (halfCoeff (dirichletExp (lamLog lam))) P m =
      G 1 := by
  have h := twist_spectral_system hsl hΦd hΦre hid hGc hGd hG2 hm hVc hVd hVs hVl (κ₀ := 1)
    (fun τ hτ => by rw [one_mul]; exact hlock τ hτ) (Aspec := dirSpec P m) hspec
  rwa [one_mul, tsum_term_dirSpec _ _ hm] at h

/-- **The divisor system of a Dirichlet lock.**  If `G(1 − s) = V(s) G(s)` on the lower critical
line, with `V(s) = Σ P(k) k^{−(s−½)}`, then `√m Σ_{n ∣ m} a(n) n^{−1/2} P(m/n) = G(1)` for every
`m ≥ 1`. -/
theorem dirLock_divisor_system {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = dirLock P (lineS τ) * G (lineS τ))
    {m : ℕ} (hm : 1 ≤ m) :
    ((Real.sqrt m : ℝ) : ℂ) * LSeries.convolution (halfCoeff (dirichletExp (lamLog lam))) P m =
      G 1 := by
  set S : ℝ := ∑' k, ‖P k‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => norm_nonneg _
  have hbd : ∀ s, ‖dirLock P s‖ ≤ Real.exp (Real.log (S + 1)) := fun s => by
    rw [Real.exp_log (by linarith)]; linarith [norm_dirLock_le hP s]
  exact divisor_system_of_spec hsl hΦd hΦre hid hGc hGd hG2
    (fun s _ _ _ => (continuous_dirLock hP).continuousAt)
    (fun s hs _ _ => differentiableAt_dirLock hP hs) (fun s _ _ _ => hbd s) (fun t _ => hbd _)
    hlock hm (fun n hn => tendsto_dirLock_abel hP hm hn)

theorem ofReal_sqrt_natCast (n : ℕ) : ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast; ring_nf

/-- **Dirichlet factorization.**  If `√m Σ_{n ∣ m} a(n) n^{−1/2} P(m/n) = G(1)` for every `m ≥ 1`, then
`F(w) Σ_k P(k) k^{−(w−½)} = G(1) ζ(w)` on `Re w > 1`, where `F = exp(Σ lam(n) n^{−s}/log n)` is the
producer's Dirichlet series. -/
theorem dirLock_factorization {lam : ℕ → ℝ} {G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖)
    (hsys : ∀ m : ℕ, 1 ≤ m → ((Real.sqrt m : ℝ) : ℂ) *
      LSeries.convolution (halfCoeff (dirichletExp (lamLog lam))) P m = G 1)
    {w : ℂ} (hw : 1 < w.re) :
    zetaOf lam w * LSeries P (w - 1 / 2) = G 1 * riemannZeta w := by
  set a := dirichletExp (lamLog lam) with ha
  have hLa := LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
    (lseriesSummable_of_le (norm_lamLog_le lam) hsl hw)
  set z : ℂ := w - 1 / 2 with hz
  have hzre : 0 ≤ z.re := by rw [hz, Complex.sub_re]; norm_num; linarith
  have hterm : ∀ n, LSeries.term (halfCoeff a) z n = LSeries.term a w n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, halfCoeff, div_div,
      ← Complex.cpow_add _ _ hn0, hz]
    ring_nf
  have hsumm_b : LSeriesSummable (halfCoeff a) z := by
    unfold LSeriesSummable
    rw [funext hterm]; exact hLa.1
  have hLb : LSeries (halfCoeff a) z = LSeries a w := by
    unfold LSeries; rw [funext hterm]
  have hconv := LSeries_convolution' hsumm_b (lseriesSummable_of_nonneg hP hzre)
  have hval : ∀ {n : ℕ}, n ≠ 0 → LSeries.convolution (halfCoeff a) P n =
      G 1 / (n : ℂ) ^ (1 / 2 : ℂ) := by
    intro n hn
    have h := hsys n (Nat.one_le_iff_ne_zero.mpr hn)
    rw [ofReal_sqrt_natCast] at h
    have hn0 : (n : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))
    rw [← h, ha]; field_simp
  have hRHS : LSeries (LSeries.convolution (halfCoeff a) P) z = G 1 * riemannZeta w := by
    rw [LSeries_congr (fun hn => hval hn) z, ← LSeries_one_eq_riemannZeta hw, LSeries, LSeries,
      ← tsum_mul_left]
    congr 1
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Pi.one_apply, div_div,
      ← Complex.cpow_add _ _ hn0, hz]
    ring_nf
  rw [hconv, hLb, hLa.2] at hRHS
  exact hRHS

/-- `G(w) V(w) = 2 G(1) ξ(w)` on `Re w > 1`. -/
theorem G_mul_dirLock_eq_xi_of_one_lt {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖)
    (hsys : ∀ m : ℕ, 1 ≤ m → ((Real.sqrt m : ℝ) : ℂ) *
      LSeries.convolution (halfCoeff (dirichletExp (lamLog lam))) P m = G 1)
    {w : ℂ} (hw : 1 < w.re) :
    G w * dirLock P w = 2 * G 1 * xi w := by
  have hf := dirLock_factorization hsl hP hsys hw
  have h0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
  have h1 : w ≠ 1 := by intro h; rw [h] at hw; simp at hw
  have hΓ : Complex.Gammaℝ w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΛ : completedRiemannZeta w = Complex.Gammaℝ w * riemannZeta w := by
    rw [riemannZeta_def_of_ne_zero h0]; field_simp
  rw [G_eq_bigG hsl hid hGd hG2 hw, bigG, dirLock_of_le P (by linarith), xi_eq_half_mul h0 h1, hΛ]
  calc w * (w - 1) * Complex.Gammaℝ w * zetaOf lam w * LSeries P (w - 1 / 2)
      = w * (w - 1) * Complex.Gammaℝ w * (zetaOf lam w * LSeries P (w - 1 / 2)) := by ring
    _ = w * (w - 1) * Complex.Gammaℝ w * (G 1 * riemannZeta w) := by rw [hf]
    _ = 2 * G 1 * (w * (w - 1) / 2 * (Complex.Gammaℝ w * riemannZeta w)) := by ring

end

end AbelianTwist

end RHTower
