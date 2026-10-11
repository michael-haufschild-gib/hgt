import GaloisForLFunctions.RHTower.WeilMarginTwistLockRigidity

/-!
# Log-periodic lock densities are impossible

Let `G` be a Herglotz producer.  Suppose that on the lower critical line

`G(1 − s) = κ₀ e^{iθ(x)} G(s)`,  `s = ½ − 2ix`, `x > 0`,  `θ(x) = ηx + a x cos(β log x)`.

The density `θ'(x)/2π = (η + a(cos − β sin)(β log x))/2π` oscillates log-periodically and never
settles; the deviation of `θ` from a line has variation of order `x`.

**Theorem** (`log_periodic_lock_impossible`).  If `η > |a|(1 + |β|)e^{|β|π}`, no Herglotz producer
has this lock.

This places the margin theorem (`margin_twist_lock_impossible`) on a concrete class that the earlier
lock theorems do not reach: the density is not constant (`linear_twist_quantization`), the phase is
not a line plus a sublinear-variation term (`lock_phase_variation_rigidity`), and the twist does not
decay at `Re s = 3/2` (`decaying_twist_lock_impossible`).

**Proof.**  With `z = i(s − ½)/2` and `ℓ = log z = Log(s − ½) + iπ/2 − log 2`, the phase extends to
`L(s) = −(η/2)(s − ½) + i a z cos(βℓ)`.
* `L' = −η/2 − (a/2)(cos βℓ − β sin βℓ)` and `L'' = (aβ/2)(sin βℓ + β cos βℓ)/(s − ½)`.
* On `Re s ≥ ½`, `Im ℓ = arg(s − ½) + π/2 ∈ [0, π]`, so `|cos βℓ|, |sin βℓ| ≤ e^{|β|π}`.  Hence
  `Re L' ≤ −c`, `c = (η − |a|(1 + |β|)e^{|β|π})/2 > 0`, and `L''(3/2 + iy) = O(1/|y|)`.
* `Re L = 0` on the lower line, and `Re L` decreases along horizontal segments (`Re L' < 0`), so
  `Re L ≤ 0` on the lower strip.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- `ℓ(s) = Log(s − ½) + iπ/2 − log 2`, the logarithm of `i(s − ½)/2`. -/
def lpLog (s : ℂ) : ℂ := Complex.log (s - 1 / 2) + ((Real.pi / 2 : ℝ) : ℂ) * I - ((Real.log 2 : ℝ) : ℂ)

/-- The log-periodic lock exponent `L(s) = −(η/2)(s − ½) + i a (i(s − ½)/2) cos(βℓ(s))`. -/
def lpExponent (η a β : ℝ) (s : ℂ) : ℂ :=
  -(((η / 2 : ℝ) : ℂ) * (s - 1 / 2)) +
    I * (a : ℂ) * (I * (s - 1 / 2) / 2 * Complex.cos ((β : ℂ) * lpLog s))

/-- `L'(s) = −η/2 − (a/2)(cos βℓ − β sin βℓ)`. -/
def lpDeriv (η a β : ℝ) (s : ℂ) : ℂ :=
  -((η / 2 : ℝ) : ℂ) - (a : ℂ) / 2 *
    (Complex.cos ((β : ℂ) * lpLog s) - (β : ℂ) * Complex.sin ((β : ℂ) * lpLog s))

/-- `L''(s) = (aβ/2)(sin βℓ + β cos βℓ)/(s − ½)`. -/
def lpDeriv2 (a β : ℝ) (s : ℂ) : ℂ :=
  (a : ℂ) * (β : ℂ) / 2 *
    (Complex.sin ((β : ℂ) * lpLog s) + (β : ℂ) * Complex.cos ((β : ℂ) * lpLog s)) / (s - 1 / 2)

theorem slitPlane_of_half_lt {s : ℂ} (hs : 1 / 2 < s.re) : s - 1 / 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left; simp; linarith

theorem hasDerivAt_lpLog {s : ℂ} (hs : s - 1 / 2 ∈ Complex.slitPlane) :
    HasDerivAt lpLog (1 / (s - 1 / 2)) s := by
  have h1 : HasDerivAt (fun z : ℂ => z - 1 / 2) 1 s := (hasDerivAt_id s).sub_const _
  have h := ((h1.clog hs).add_const (((Real.pi / 2 : ℝ) : ℂ) * I)).sub_const
    ((Real.log 2 : ℝ) : ℂ)
  exact h

theorem hasDerivAt_lpExponent (η a β : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    HasDerivAt (lpExponent η a β) (lpDeriv η a β s) s := by
  have hslit := slitPlane_of_half_lt hs
  have hne : s - 1 / 2 ≠ 0 := Complex.slitPlane_ne_zero hslit
  have h1 : HasDerivAt (fun z : ℂ => z - 1 / 2) 1 s := (hasDerivAt_id s).sub_const _
  have hlin := (h1.const_mul (((η / 2 : ℝ) : ℂ))).neg
  have hz : HasDerivAt (fun z : ℂ => I * (z - 1 / 2) / 2) (I * 1 / 2) s :=
    (h1.const_mul I).div_const 2
  have hcos := ((hasDerivAt_lpLog hslit).const_mul (β : ℂ)).ccos
  have h := hlin.add ((hz.mul hcos).const_mul (I * (a : ℂ)))
  unfold lpExponent
  refine h.congr_deriv ?_
  unfold lpDeriv
  have e : (s - 1 / 2) * (1 / (s - 1 / 2)) = 1 := mul_one_div_cancel hne
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination ((a : ℂ) / 2 * (Complex.cos ((β : ℂ) * lpLog s) -
      (β : ℂ) * Complex.sin ((β : ℂ) * lpLog s) * ((s - 1 / 2) * (1 / (s - 1 / 2))))) * hI +
    ((a : ℂ) / 2 * (β : ℂ) * Complex.sin ((β : ℂ) * lpLog s)) * e


theorem hasDerivAt_lpDeriv (η a β : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    HasDerivAt (lpDeriv η a β) (lpDeriv2 a β s) s := by
  have hslit := slitPlane_of_half_lt hs
  have hl := (hasDerivAt_lpLog hslit).const_mul (β : ℂ)
  have h := (hasDerivAt_const s (-((η / 2 : ℝ) : ℂ))).sub
    ((hl.ccos.sub (hl.csin.const_mul (β : ℂ))).const_mul ((a : ℂ) / 2))
  unfold lpDeriv
  refine h.congr_deriv ?_
  unfold lpDeriv2
  ring

/-! ### Bounds -/

theorem norm_ccos_le_exp_abs_im_twist (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos]
  have h1 : ‖cexp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; refine Real.exp_le_exp.mpr ?_; simp; exact neg_le_abs _
  have h2 : ‖cexp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; refine Real.exp_le_exp.mpr ?_; simp; exact le_abs_self _
  rw [norm_div, Complex.norm_ofNat]
  have := norm_add_le (cexp (w * I)) (cexp (-w * I))
  linarith

theorem norm_csin_le_exp_abs_im_twist (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  rw [Complex.sin]
  have h1 : ‖cexp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; refine Real.exp_le_exp.mpr ?_; simp; exact neg_le_abs _
  have h2 : ‖cexp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; refine Real.exp_le_exp.mpr ?_; simp; exact le_abs_self _
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  have := norm_sub_le (cexp (-w * I)) (cexp (w * I))
  linarith

theorem lpLog_im (s : ℂ) : (lpLog s).im = (s - 1 / 2).arg + Real.pi / 2 := by
  simp [lpLog, Complex.log_im]

theorem im_ofReal_mul' (r : ℝ) (z : ℂ) : ((r : ℂ) * z).im = r * z.im := by
  simp [Complex.mul_im]

theorem abs_im_beta_lpLog_le {β : ℝ} {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    |((β : ℂ) * lpLog s).im| ≤ |β| * Real.pi := by
  rw [im_ofReal_mul', lpLog_im, abs_mul]
  have harg : |(s - 1 / 2).arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (by simp; linarith)
  have h := abs_le.mp harg
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_le]; constructor <;> linarith [Real.pi_pos]

theorem abs_im_beta_lpLog_le' (β : ℝ) (s : ℂ) :
    |((β : ℂ) * lpLog s).im| ≤ |β| * (2 * Real.pi) := by
  rw [im_ofReal_mul', lpLog_im, abs_mul]
  have h := abs_le.mp (Complex.abs_arg_le_pi (s - 1 / 2))
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_le]; constructor <;> linarith [Real.pi_pos]

theorem re_lpDeriv_le (η a β : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    (lpDeriv η a β s).re ≤ -(η / 2) + |a| / 2 * ((1 + |β|) * Real.exp (|β| * Real.pi)) := by
  set C := Complex.cos ((β : ℂ) * lpLog s) with hC
  set S := Complex.sin ((β : ℂ) * lpLog s) with hS
  have hE := Real.exp_le_exp.mpr (abs_im_beta_lpLog_le (β := β) hs)
  have hCn : ‖C‖ ≤ Real.exp (|β| * Real.pi) := (norm_ccos_le_exp_abs_im_twist _).trans hE
  have hSn : ‖S‖ ≤ Real.exp (|β| * Real.pi) := (norm_csin_le_exp_abs_im_twist _).trans hE
  have hW : ‖C - (β : ℂ) * S‖ ≤ (1 + |β|) * Real.exp (|β| * Real.pi) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg β, norm_nonneg S]
  have hre : (lpDeriv η a β s).re = -(η / 2) - a / 2 * (C - (β : ℂ) * S).re := by
    have e : lpDeriv η a β s = -((η / 2 : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ) * (C - (β : ℂ) * S) := by
      unfold lpDeriv; push_cast; ring
    rw [e, Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  rw [hre]
  have h1 : -(a / 2 * (C - (β : ℂ) * S).re) ≤ |a| / 2 * ‖C - (β : ℂ) * S‖ := by
    have := Complex.abs_re_le_norm (C - (β : ℂ) * S)
    have h2 : |a / 2 * (C - (β : ℂ) * S).re| ≤ |a| / 2 * ‖C - (β : ℂ) * S‖ := by
      rw [abs_mul, abs_div, abs_two]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith [neg_abs_le (a / 2 * (C - (β : ℂ) * S).re)]
  have h3 : |a| / 2 * ‖C - (β : ℂ) * S‖ ≤ |a| / 2 * ((1 + |β|) * Real.exp (|β| * Real.pi)) :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  linarith

theorem norm_lpDeriv2_le (a β : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖lpDeriv2 a β s‖ ≤ |a| * |β| / 2 * ((1 + |β|) * Real.exp (|β| * Real.pi)) / ‖s - 1 / 2‖ := by
  set C := Complex.cos ((β : ℂ) * lpLog s) with hC
  set S := Complex.sin ((β : ℂ) * lpLog s) with hS
  have hE := Real.exp_le_exp.mpr (abs_im_beta_lpLog_le (β := β) hs)
  have hCn : ‖C‖ ≤ Real.exp (|β| * Real.pi) := (norm_ccos_le_exp_abs_im_twist _).trans hE
  have hSn : ‖S‖ ≤ Real.exp (|β| * Real.pi) := (norm_csin_le_exp_abs_im_twist _).trans hE
  have hW : ‖S + (β : ℂ) * C‖ ≤ (1 + |β|) * Real.exp (|β| * Real.pi) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg β, norm_nonneg C]
  unfold lpDeriv2
  rw [norm_div, norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_ofNat]
  gcongr

/-! ### Regularity -/

theorem norm_lpExponent_le (η a β : ℝ) (s : ℂ) :
    ‖lpExponent η a β s‖ ≤
      (|η| / 2 + |a| / 2 * Real.exp (|β| * (2 * Real.pi))) * ‖s - 1 / 2‖ := by
  unfold lpExponent
  have hc : ‖Complex.cos ((β : ℂ) * lpLog s)‖ ≤ Real.exp (|β| * (2 * Real.pi)) :=
    (norm_ccos_le_exp_abs_im_twist _).trans (Real.exp_le_exp.mpr (abs_im_beta_lpLog_le' β s))
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖-(((η / 2 : ℝ) : ℂ) * (s - 1 / 2))‖ = |η| / 2 * ‖s - 1 / 2‖ := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
  have h2 : ‖I * (a : ℂ) * (I * (s - 1 / 2) / 2 * Complex.cos ((β : ℂ) * lpLog s))‖ =
      |a| * (‖s - 1 / 2‖ / 2 * ‖Complex.cos ((β : ℂ) * lpLog s)‖) := by
    simp only [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat, one_mul]
  rw [h1, h2]
  have h0 := norm_nonneg (s - 1 / 2)
  have h3 : |a| * (‖s - 1 / 2‖ / 2 * ‖Complex.cos ((β : ℂ) * lpLog s)‖) ≤
      |a| * (‖s - 1 / 2‖ / 2 * Real.exp (|β| * (2 * Real.pi))) := by gcongr
  nlinarith [abs_nonneg a, abs_nonneg η]

theorem lpExponent_half (η a β : ℝ) : lpExponent η a β (1 / 2) = 0 := by
  simp [lpExponent]

theorem continuousAt_lpExponent (η a β : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ContinuousAt (lpExponent η a β) s := by
  by_cases hs0 : s = 1 / 2
  · subst hs0
    rw [ContinuousAt, lpExponent_half]
    refine squeeze_zero_norm (fun w => norm_lpExponent_le η a β w) ?_
    have h : Continuous fun w : ℂ =>
        (|η| / 2 + |a| / 2 * Real.exp (|β| * (2 * Real.pi))) * ‖w - 1 / 2‖ := by fun_prop
    simpa using h.tendsto (1 / 2 : ℂ)
  · have hslit : s - 1 / 2 ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_cases hre : (s - 1 / 2).re = 0
      · right
        intro him
        apply hs0
        have : s - 1 / 2 = 0 := Complex.ext hre him
        linear_combination this
      · left
        have : 0 ≤ (s - 1 / 2).re := by simp; linarith
        exact lt_of_le_of_ne this (Ne.symm hre)
    have hl : ContinuousAt lpLog s := by
      unfold lpLog
      exact (((continuousAt_id.sub continuousAt_const).clog hslit).add continuousAt_const).sub
        continuousAt_const
    unfold lpExponent
    exact ((continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).neg).add
      (continuousAt_const.mul (((continuousAt_const.mul (continuousAt_id.sub
        continuousAt_const)).div_const 2).mul
          (Complex.continuous_cos.continuousAt.comp (continuousAt_const.mul hl))))

/-! ### Values on the lower line and the lower strip -/

theorem lpExponent_lineS (η a β : ℝ) {t : ℝ} (ht : t < 0) :
    lpExponent η a β (lineS t) =
      ((η * (-t) + a * (-t) * Real.cos (β * Real.log (-t)) : ℝ) : ℂ) * I := by
  have hw : lineS t - 1 / 2 = (((-(2 * t)) : ℝ) : ℂ) * (-I) := by
    rw [lineS_eq]; push_cast; ring
  have hpos : (0 : ℝ) < -(2 * t) := by linarith
  have hlog : Complex.log (lineS t - 1 / 2) =
      (Real.log (-(2 * t)) : ℂ) - (Real.pi / 2 : ℝ) * I := by
    rw [hw, Complex.log_ofReal_mul hpos (by simp), Complex.log_neg_I]
    push_cast; ring
  have hl2 : Real.log (-(2 * t)) = Real.log 2 + Real.log (-t) := by
    rw [show -(2 * t) = 2 * (-t) by ring, Real.log_mul (by norm_num) (by linarith)]
  have hlp : lpLog (lineS t) = ((Real.log (-t) : ℝ) : ℂ) := by
    unfold lpLog
    rw [hlog, hl2]
    push_cast; ring
  have hcos : Complex.cos ((β : ℂ) * lpLog (lineS t)) = ((Real.cos (β * Real.log (-t)) : ℝ) : ℂ) := by
    rw [hlp, ← Complex.ofReal_mul, ← Complex.ofReal_cos]
  unfold lpExponent
  rw [hcos, hw]
  have hI : I * I = -1 := Complex.I_mul_I
  push_cast
  linear_combination ((a : ℂ) * (t : ℂ) * Complex.cos ((β : ℂ) * ((Real.log (-t) : ℝ) : ℂ)) * I) * hI

theorem re_lpExponent_lineS (η a β : ℝ) {t : ℝ} (ht : t < 0) :
    (lpExponent η a β (lineS t)).re = 0 := by
  rw [lpExponent_lineS η a β ht, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- `Re L ≤ 0` on the lower strip when the density margin holds. -/
theorem re_lpExponent_strip_le {η a β : ℝ}
    (hη : |a| * (1 + |β|) * Real.exp (|β| * Real.pi) < η) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (him : s.im < 0) : (lpExponent η a β s).re ≤ 0 := by
  set t : ℝ := s.im with ht
  set g : ℝ → ℝ := fun σ => (lpExponent η a β ((σ : ℂ) + (t : ℂ) * I)).re with hg
  have hpt : ∀ σ : ℝ, ((σ : ℂ) + (t : ℂ) * I).re = σ := fun σ => by simp
  have hgc : ContinuousOn g (Icc (1 / 2) s.re) := by
    intro σ hσ
    have hc := continuousAt_lpExponent η a β (s := (σ : ℂ) + (t : ℂ) * I) (by rw [hpt]; exact hσ.1)
    have hinner : ContinuousAt (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * I) σ := by fun_prop
    exact (Complex.continuous_re.continuousAt.comp
      (ContinuousAt.comp (x := σ) hc hinner)).continuousWithinAt
  have hgd : ∀ σ : ℝ, 1 / 2 < σ →
      HasDerivAt g (lpDeriv η a β ((σ : ℂ) + (t : ℂ) * I)).re σ := by
    intro σ hσ
    have hd := hasDerivAt_lpExponent η a β (s := (σ : ℂ) + (t : ℂ) * I) (by rw [hpt]; exact hσ)
    have h2 := hd.comp (σ : ℂ) ((hasDerivAt_id (σ : ℂ)).add_const ((t : ℂ) * I))
    have h3 := h2.real_of_complex
    simpa [hg, Function.comp_def] using h3
  have hanti : AntitoneOn g (Icc (1 / 2) s.re) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hgc ?_ ?_
    · rw [interior_Icc]
      intro σ hσ
      exact (hgd σ hσ.1).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro σ hσ
      rw [(hgd σ hσ.1).deriv]
      have h := re_lpDeriv_le η a β (s := (σ : ℂ) + (t : ℂ) * I) (by rw [hpt]; exact hσ.1.le)
      nlinarith [abs_nonneg a]
  have h := hanti ⟨le_refl _, hs⟩ ⟨hs, le_refl _⟩ hs
  have hs' : s = (s.re : ℂ) + (t : ℂ) * I := (Complex.re_add_im s).symm
  have hval : g (1 / 2) = 0 := by
    have e : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I = lineS (t / 2) := by
      rw [lineS_eq]; push_cast; ring
    simp only [hg]
    rw [e, re_lpExponent_lineS η a β (by linarith)]
  calc (lpExponent η a β s).re = g s.re := by rw [hg]; simp only; rw [← hs']
    _ ≤ g (1 / 2) := h
    _ = 0 := hval


/-! ### The theorem -/

/-- **Log-periodic lock densities are impossible.**  If `η > |a|(1 + |β|)e^{|β|π}`, no Herglotz
producer satisfies `G(1 − s) = κ₀ e^{iθ(−τ)} G(s)` at `s = ½ + 2iτ`, `τ < 0`, with
`θ(x) = ηx + a x cos(β log x)`. -/
theorem log_periodic_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {η a β : ℝ} (hη : |a| * (1 + |β|) * Real.exp (|β| * Real.pi) < η) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ₀ * cexp (((η * (-τ) + a * (-τ) * Real.cos (β * Real.log (-τ)) : ℝ) : ℂ) * I) *
        G (lineS τ)) :
    False := by
  set E : ℝ := Real.exp (|β| * Real.pi) with hE
  set c : ℝ := (η - |a| * (1 + |β|) * E) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ∀ y : ℝ, edgePt y ∈ U := fun y => by
    show (1 / 2 : ℝ) < (edgePt y).re
    rw [edgePt_re]; norm_num
  have hderiv : ∀ y : ℝ, deriv (lpExponent η a β) (edgePt y) = lpDeriv η a β (edgePt y) :=
    fun y => (hasDerivAt_lpExponent η a β (hmem y)).deriv
  have hderiv2 : ∀ y : ℝ, deriv (deriv (lpExponent η a β)) (edgePt y) = lpDeriv2 a β (edgePt y) := by
    intro y
    have hev : deriv (lpExponent η a β) =ᶠ[𝓝 (edgePt y)] lpDeriv η a β :=
      Filter.eventually_of_mem (hUo.mem_nhds (hmem y))
        fun w hw => (hasDerivAt_lpExponent η a β hw).deriv
    rw [hev.deriv_eq]
    exact (hasDerivAt_lpDeriv η a β (hmem y)).deriv
  refine margin_twist_lock_impossible hsl hΦd hΦre hid hGc hGd hG2 (L := lpExponent η a β)
    (fun s hs => continuousAt_lpExponent η a β hs)
    (fun s hs => (hasDerivAt_lpExponent η a β hs).differentiableAt) (A := 0)
    (fun s hs1 _ him => re_lpExponent_strip_le hη hs1 (by linarith))
    (fun t ht => (re_lpExponent_lineS η a β ht).le) hc0 ?_ ?_ (κ₀ := κ₀) (fun τ hτ => ?_)
  · refine Eventually.of_forall fun y => ?_
    rw [hderiv]
    have h := re_lpDeriv_le η a β (s := edgePt y) (by rw [edgePt_re]; norm_num)
    rw [hc]; linarith
  · have hK : Tendsto (fun y : ℝ => |a| * |β| / 2 * ((1 + |β|) * E) / |y|) atBot (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp tendsto_abs_atBot_atTop).const_mul
        (|a| * |β| / 2 * ((1 + |β|) * E))
      rw [mul_zero] at this
      exact this.congr fun y => by simp [div_eq_mul_inv]
    refine squeeze_zero_norm' ?_ hK
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with y hy
    rw [hderiv2]
    refine (norm_lpDeriv2_le a β (s := edgePt y) (by rw [edgePt_re]; norm_num)).trans ?_
    have hy0 : 0 < |y| := by rw [abs_pos]; linarith
    have hn : |y| ≤ ‖edgePt y - 1 / 2‖ := by
      have h := Complex.abs_im_le_norm (edgePt y - 1 / 2)
      have him : (edgePt y - 1 / 2).im = y := by simp [edgePt]
      rwa [him] at h
    exact div_le_div_of_nonneg_left (by positivity) hy0 hn
  · rw [hlock τ hτ, lpExponent_lineS η a β hτ]

end

end AbelianTwist

end RHTower
