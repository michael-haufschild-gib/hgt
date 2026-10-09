import GaloisForLFunctions.RHTower.LeeYangFirstZeroLaw
import GaloisForLFunctions.RHTower.EntireArgumentVariationRectangle

/-!
# Exact zero-count difference for an inner split

Let `a, b` be entire with `a ≠ 0`, `‖b‖ ≤ ‖a‖` below the real axis and `b ≠ 0`, `‖a‖ ≤ ‖b‖`
above it (an *inner split*). For `μ > 0` put `f_μ(z) = a(z) + b(z) e^{−iμz}`. All zeros of `f_μ`
are real.

**Theorem** (`zeroCount_sub_ge`). For `0 < ε < λ` and `T > 0`, the zeros of `f_λ` in `(0, T]`,
counted with multiplicity, outnumber those of `f_ε` by at least `⌊(λ − ε)T/2π⌋`.

**Proof.** Apply the argument principle to `f_λ` and `f_ε` on the same thin rectangle
`[c, d] × [−η, η]`. Below the axis `f_μ = a(1 + w_μ)` with `w_μ = b e^{−iμz}/a`, `‖w_μ‖ < 1`;
above it `f_μ = b e^{−iμz}(1 + w'_μ)` with `w'_μ = a e^{iμz}/b`, `‖w'_μ‖ < 1`. The contributions of
`log a` and `log b` do not depend on `μ`, the factor `e^{−iμz}` contributes `μ(d − c)`, and
`1 + w_μ`, `1 + w'_μ` have principal-logarithm primitives. Letting `η → 0` and using
`arg(1 + u) − arg(1 + ū) = arg u` on the unit circle gives the exact identity
`2π(N_λ − N_ε) = (λ − ε)(d − c) + [arg w_λ − arg w_ε]_c^d`, i.e. a difference of two integer
roundings. The right endpoint contributes at least `⌊(λ − ε)d/2π⌋`. The left endpoint
contributes nothing for a suitable small `c`, because `arg(b/a)` is non-increasing on the real axis
(boundary slope).
-/

open Complex Set Filter Topology MeasureTheory

namespace RHTower.LeeYangSplitCount

noncomputable section

/-- `f_μ(z) = a(z) + b(z) e^{−iμz}`. -/
def splitFn (a b : ℂ → ℂ) (μ : ℝ) (z : ℂ) : ℂ := a z + b z * cexp (-(I * (μ : ℂ) * z))

/-- An inner split: `a ≠ 0`, `‖b‖ ≤ ‖a‖` below the axis and `b ≠ 0`, `‖a‖ ≤ ‖b‖` above it. -/
structure InnerSplit (a b : ℂ → ℂ) : Prop where
  da : Differentiable ℂ a
  db : Differentiable ℂ b
  low : ∀ z : ℂ, z.im < 0 → a z ≠ 0 ∧ ‖b z‖ ≤ ‖a z‖
  up : ∀ z : ℂ, 0 < z.im → b z ≠ 0 ∧ ‖a z‖ ≤ ‖b z‖

variable {a b : ℂ → ℂ}

theorem norm_cexp_split (μ : ℝ) (z : ℂ) :
    ‖cexp (-(I * (μ : ℂ) * z))‖ = Real.exp (μ * z.im) :=
  RHTower.LeeYangFirstZero.norm_cexp_neg_I_mul μ z

theorem differentiable_splitFn (hS : InnerSplit a b) (μ : ℝ) : Differentiable ℂ (splitFn a b μ) :=
  hS.da.add (hS.db.mul (by fun_prop))

theorem splitFn_ne_zero_of_im_neg (hS : InnerSplit a b) {μ : ℝ} (hμ : 0 < μ) {z : ℂ}
    (hz : z.im < 0) : splitFn a b μ z ≠ 0 := by
  obtain ⟨ha, hb⟩ := hS.low z hz
  have hlt : ‖b z * cexp (-(I * (μ : ℂ) * z))‖ < ‖a z‖ := by
    rw [norm_mul, norm_cexp_split]
    have he : Real.exp (μ * z.im) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    rcases eq_or_ne (b z) 0 with h0 | h0
    · rw [h0, norm_zero, zero_mul]; exact norm_pos_iff.mpr ha
    · calc ‖b z‖ * Real.exp (μ * z.im) < ‖b z‖ * 1 :=
            mul_lt_mul_of_pos_left he (norm_pos_iff.mpr h0)
        _ ≤ ‖a z‖ := by rw [mul_one]; exact hb
  intro h
  have : a z = -(b z * cexp (-(I * (μ : ℂ) * z))) := eq_neg_of_add_eq_zero_left h
  rw [this, norm_neg] at hlt
  exact lt_irrefl _ hlt

theorem splitFn_ne_zero_of_im_pos (hS : InnerSplit a b) {μ : ℝ} (hμ : 0 < μ) {z : ℂ}
    (hz : 0 < z.im) : splitFn a b μ z ≠ 0 := by
  obtain ⟨hb, ha⟩ := hS.up z hz
  have hlt : ‖a z‖ < ‖b z * cexp (-(I * (μ : ℂ) * z))‖ := by
    rw [norm_mul, norm_cexp_split]
    have he : 1 < Real.exp (μ * z.im) := Real.one_lt_exp_iff.mpr (by positivity)
    calc ‖a z‖ ≤ ‖b z‖ * 1 := by rw [mul_one]; exact ha
      _ < ‖b z‖ * Real.exp (μ * z.im) := mul_lt_mul_of_pos_left he (norm_pos_iff.mpr hb)
  intro h
  have : a z = -(b z * cexp (-(I * (μ : ℂ) * z))) := eq_neg_of_add_eq_zero_left h
  rw [this, norm_neg] at hlt
  exact lt_irrefl _ hlt

theorem splitFn_ne_zero_of_im_ne_zero (hS : InnerSplit a b) {μ : ℝ} (hμ : 0 < μ) {z : ℂ}
    (hz : z.im ≠ 0) : splitFn a b μ z ≠ 0 := by
  rcases lt_or_gt_of_ne hz with h | h
  · exact splitFn_ne_zero_of_im_neg hS hμ h
  · exact splitFn_ne_zero_of_im_pos hS hμ h

theorem exists_splitFn_ne_zero (hS : InnerSplit a b) {μ : ℝ} (hμ : 0 < μ) :
    ∃ z : ℂ, splitFn a b μ z ≠ 0 :=
  ⟨-I, splitFn_ne_zero_of_im_neg hS hμ (by simp)⟩

/-! ## Unimodularity on the real axis -/

theorem tendsto_norm_comp_sub_I {g : ℂ → ℂ} (hg : Continuous g) (t : ℝ) :
    Tendsto (fun s : ℝ => ‖g ((t : ℂ) - (s : ℂ) * I)‖) (𝓝[>] 0) (𝓝 ‖g t‖) := by
  have hc : Continuous fun s : ℝ => ‖g ((t : ℂ) - (s : ℂ) * I)‖ := by fun_prop
  have h := hc.tendsto 0
  simp only [ofReal_zero, zero_mul, sub_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_norm_comp_add_I {g : ℂ → ℂ} (hg : Continuous g) (t : ℝ) :
    Tendsto (fun s : ℝ => ‖g ((t : ℂ) + (s : ℂ) * I)‖) (𝓝[>] 0) (𝓝 ‖g t‖) := by
  have hc : Continuous fun s : ℝ => ‖g ((t : ℂ) + (s : ℂ) * I)‖ := by fun_prop
  have h := hc.tendsto 0
  simp only [ofReal_zero, zero_mul, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- On the real axis `‖b‖ = ‖a‖`. -/
theorem norm_eq_of_real (hS : InnerSplit a b) (t : ℝ) : ‖b t‖ = ‖a t‖ := by
  apply le_antisymm
  · refine le_of_tendsto_of_tendsto (tendsto_norm_comp_sub_I hS.db.continuous t)
      (tendsto_norm_comp_sub_I hS.da.continuous t) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hS.low _ (by simpa using (show (0 : ℝ) < s from hs))).2
  · refine le_of_tendsto_of_tendsto (tendsto_norm_comp_add_I hS.da.continuous t)
      (tendsto_norm_comp_add_I hS.db.continuous t) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hS.up _ (by simpa using (show (0 : ℝ) < s from hs))).2

/-- A real zero of `a` is a zero of `b` and of every `f_μ`. -/
theorem splitFn_eq_zero_of_a_eq_zero (hS : InnerSplit a b) {t : ℝ} (ht : a t = 0) (μ : ℝ) :
    splitFn a b μ t = 0 := by
  have hb : b t = 0 := by
    have := norm_eq_of_real hS t
    rw [ht, norm_zero] at this
    exact norm_eq_zero.mp this
  simp [splitFn, ht, hb]

theorem a_ne_zero_of_splitFn_ne_zero (hS : InnerSplit a b) {t : ℝ} {μ : ℝ}
    (h : splitFn a b μ t ≠ 0) : a t ≠ 0 := fun ha => h (splitFn_eq_zero_of_a_eq_zero hS ha μ)

theorem b_ne_zero_of_splitFn_ne_zero (hS : InnerSplit a b) {t : ℝ} {μ : ℝ}
    (h : splitFn a b μ t ≠ 0) : b t ≠ 0 := by
  intro hb
  have := norm_eq_of_real hS t
  rw [hb, norm_zero] at this
  exact a_ne_zero_of_splitFn_ne_zero hS h (norm_eq_zero.mp this.symm)

/-! ## The unit circle -/

theorem one_add_cexp_eq (φ : ℝ) :
    1 + cexp ((φ : ℂ) * I) = ((2 * Real.cos (φ / 2) : ℝ) : ℂ) * cexp (((φ / 2 : ℝ) : ℂ) * I) := by
  push_cast
  rw [Complex.cos, show ((φ : ℂ) / 2 * I) = (φ / 2 : ℂ) * I by ring]
  have h1 : cexp ((φ : ℂ) * I) = cexp ((φ : ℂ) / 2 * I) * cexp ((φ : ℂ) / 2 * I) := by
    rw [← Complex.exp_add]; ring_nf
  have h2 : cexp (-((φ : ℂ) / 2) * I) * cexp ((φ : ℂ) / 2 * I) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  rw [h1]
  linear_combination (-1 : ℂ) * h2

theorem arg_cexp_mul_I {ψ : ℝ} (hψ : ψ ∈ Ioc (-Real.pi) Real.pi) : (cexp ((ψ : ℂ) * I)).arg = ψ := by
  rw [Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I hψ

/-- `arg(1 + e^{iφ}) = φ/2` for `|φ| < π`. -/
theorem arg_one_add_cexp {φ : ℝ} (h1 : -Real.pi < φ) (h2 : φ < Real.pi) :
    (1 + cexp ((φ : ℂ) * I)).arg = φ / 2 := by
  rw [one_add_cexp_eq]
  have hcos : 0 < 2 * Real.cos (φ / 2) := by
    have := Real.cos_pos_of_mem_Ioo (x := φ / 2) ⟨by linarith, by linarith⟩
    linarith
  rw [Complex.arg_real_mul _ hcos]
  exact arg_cexp_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem arg_ne_pi_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) (hu1 : u ≠ -1) : u.arg ≠ Real.pi := by
  intro h
  apply hu1
  have := Complex.norm_mul_exp_arg_mul_I u
  rw [hu, h] at this
  rw [← this]
  simp [Complex.exp_mul_I]

/-- On the unit circle, `arg(1 + u) − arg(1 + ū) = arg u` for `u ≠ −1`. -/
theorem arg_one_add_sub_arg_one_add_conj {u : ℂ} (hu : ‖u‖ = 1) (hu1 : u ≠ -1) :
    (1 + u).arg - (1 + (starRingEnd ℂ) u).arg = u.arg := by
  set θ := u.arg with hθ
  have hmem := Complex.arg_mem_Ioc u
  have hne := arg_ne_pi_of_norm_eq_one hu hu1
  have hlt : θ < Real.pi := lt_of_le_of_ne hmem.2 hne
  have hu' : u = cexp ((θ : ℂ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I u
    rw [hu] at this
    simpa using this.symm
  have hconj : (starRingEnd ℂ) u = cexp (((-θ : ℝ) : ℂ) * I) := by
    rw [hu', ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  rw [hconj, hu', arg_one_add_cexp hmem.1 hlt, arg_one_add_cexp (by linarith) (by linarith [hmem.1])]
  ring

theorem one_add_mem_slitPlane_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 + w ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have := Complex.abs_re_le_norm w
  rw [add_re, one_re]
  linarith [neg_abs_le w.re]

theorem one_add_mem_slitPlane_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) (hu1 : u ≠ -1) :
    1 + u ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : u.im = 0
  · left
    have hre : |u.re| = 1 := by
      have h := Complex.norm_eq_sqrt_sq_add_sq u
      rw [hu, him] at h
      have h' : u.re ^ 2 = 1 := by
        have := congrArg (· ^ 2) h
        simp only [one_pow] at this
        rw [this, Real.sq_sqrt (by positivity)]; ring
      have : |u.re| ^ 2 = 1 := by rw [sq_abs]; exact h'
      nlinarith [abs_nonneg u.re]
    rcases abs_eq (zero_le_one) |>.mp hre with h | h
    · rw [add_re, one_re, h]; norm_num
    · exfalso; apply hu1; apply Complex.ext <;> simp [h, him]
  · right; simpa using him

/-! ## The edge identities -/

/-- The lower quotient `w_μ = b e^{−iμz}/a`. -/
def lowQ (a b : ℂ → ℂ) (μ : ℝ) (z : ℂ) : ℂ := b z * cexp (-(I * (μ : ℂ) * z)) / a z

/-- The upper quotient `w'_μ = a e^{iμz}/b`. -/
def upQ (a b : ℂ → ℂ) (μ : ℝ) (z : ℂ) : ℂ := a z * cexp (I * (μ : ℂ) * z) / b z

theorem norm_lowQ_lt_one (hS : InnerSplit a b) {μ : ℝ} (hμ : 0 < μ) {z : ℂ} (hz : z.im < 0) :
    ‖lowQ a b μ z‖ < 1 := by
  obtain ⟨ha, hb⟩ := hS.low z hz
  have hapos : 0 < ‖a z‖ := norm_pos_iff.mpr ha
  rw [lowQ, norm_div, norm_mul, norm_cexp_split, div_lt_one hapos]
  have he : Real.exp (μ * z.im) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  rcases eq_or_ne (b z) 0 with h0 | h0
  · rw [h0, norm_zero, zero_mul]; exact hapos
  · calc ‖b z‖ * Real.exp (μ * z.im) < ‖b z‖ * 1 :=
          mul_lt_mul_of_pos_left he (norm_pos_iff.mpr h0)
      _ ≤ ‖a z‖ := by rw [mul_one]; exact hb

theorem norm_upQ_lt_one (hS : InnerSplit a b) {μ : ℝ} (hμ : 0 < μ) {z : ℂ} (hz : 0 < z.im) :
    ‖upQ a b μ z‖ < 1 := by
  obtain ⟨hb, ha⟩ := hS.up z hz
  have hbpos : 0 < ‖b z‖ := norm_pos_iff.mpr hb
  have hnorm : ‖cexp (I * (μ : ℂ) * z)‖ = Real.exp (-(μ * z.im)) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]
  rw [upQ, norm_div, norm_mul, hnorm, div_lt_one hbpos]
  have he : Real.exp (-(μ * z.im)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  rcases eq_or_ne (a z) 0 with h0 | h0
  · rw [h0, norm_zero, zero_mul]; exact hbpos
  · calc ‖a z‖ * Real.exp (-(μ * z.im)) < ‖a z‖ * 1 :=
          mul_lt_mul_of_pos_left he (norm_pos_iff.mpr h0)
      _ ≤ ‖b z‖ := by rw [mul_one]; exact ha

theorem differentiableAt_lowQ (hS : InnerSplit a b) (μ : ℝ) {z : ℂ} (ha : a z ≠ 0) :
    DifferentiableAt ℂ (lowQ a b μ) z :=
  ((hS.db z).mul (by fun_prop)).div (hS.da z) ha

theorem differentiableAt_upQ (hS : InnerSplit a b) (μ : ℝ) {z : ℂ} (hb : b z ≠ 0) :
    DifferentiableAt ℂ (upQ a b μ) z :=
  ((hS.da z).mul (by fun_prop)).div (hS.db z) hb

theorem logDeriv_eq_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    logDeriv f z = logDeriv g z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

theorem splitFn_eventuallyEq_low {μ : ℝ} {z : ℂ} (hz : ∀ᶠ y in 𝓝 z, a y ≠ 0) :
    splitFn a b μ =ᶠ[𝓝 z] fun y => a y * (1 + lowQ a b μ y) := by
  filter_upwards [hz] with y hy
  simp only [splitFn, lowQ]
  field_simp

theorem splitFn_eventuallyEq_up {μ : ℝ} {z : ℂ} (hz : ∀ᶠ y in 𝓝 z, b y ≠ 0) :
    splitFn a b μ =ᶠ[𝓝 z] fun y => (b y * cexp (-(I * (μ : ℂ) * y))) * (1 + upQ a b μ y) := by
  filter_upwards [hz] with y hy
  simp only [splitFn, upQ]
  have he : cexp (-(I * (μ : ℂ) * y)) * cexp (I * (μ : ℂ) * y) = 1 := by
    rw [← Complex.exp_add]; simp
  have h2 : b y * cexp (-(I * (μ : ℂ) * y)) * (a y * cexp (I * (μ : ℂ) * y) / b y) = a y := by
    rw [show b y * cexp (-(I * (μ : ℂ) * y)) * (a y * cexp (I * (μ : ℂ) * y) / b y) =
      a y * (cexp (-(I * (μ : ℂ) * y)) * cexp (I * (μ : ℂ) * y)) * (b y / b y) by ring,
      div_self hy, he, mul_one, mul_one]
  rw [mul_add, mul_one, h2, add_comm]

theorem eventually_a_ne_zero_of_im_neg (hS : InnerSplit a b) {z : ℂ} (hz : z.im < 0) :
    ∀ᶠ y in 𝓝 z, a y ≠ 0 := by
  have hopen : IsOpen {y : ℂ | y.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  filter_upwards [hopen.mem_nhds hz] with y hy using (hS.low y hy).1

theorem eventually_b_ne_zero_of_im_pos (hS : InnerSplit a b) {z : ℂ} (hz : 0 < z.im) :
    ∀ᶠ y in 𝓝 z, b y ≠ 0 := by
  have hopen : IsOpen {y : ℂ | 0 < y.im} := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [hopen.mem_nhds hz] with y hy using (hS.up y hy).1

/-- Below the axis `log f_μ = log a + log(1 + w_μ)` at the level of logarithmic derivatives. -/
theorem logDeriv_splitFn_low (hS : InnerSplit a b) {μ : ℝ} (hμ : 0 < μ) {z : ℂ} (hz : z.im < 0) :
    logDeriv (splitFn a b μ) z = logDeriv a z + logDeriv (fun y => 1 + lowQ a b μ y) z := by
  have ha := (hS.low z hz).1
  rw [logDeriv_eq_of_eventuallyEq (splitFn_eventuallyEq_low (eventually_a_ne_zero_of_im_neg hS hz))]
  have h1 : 1 + lowQ a b μ z ≠ 0 := by
    intro h
    have := norm_lowQ_lt_one hS hμ hz
    rw [show lowQ a b μ z = -1 by linear_combination h, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  exact logDeriv_mul z ha h1 (hS.da z) ((differentiableAt_lowQ hS μ ha).const_add 1)

theorem logDeriv_cexp_split (μ : ℝ) (z : ℂ) :
    logDeriv (fun y => cexp (-(I * (μ : ℂ) * y))) z = -(I * (μ : ℂ)) := by
  have h : HasDerivAt (fun y => cexp (-(I * (μ : ℂ) * y))) (cexp (-(I * (μ : ℂ) * z)) * -(I * μ)) z := by
    have h1 : HasDerivAt (fun y : ℂ => -(I * (μ : ℂ) * y)) (-(I * μ)) z := by
      simpa using (hasDerivAt_id z).const_mul (-(I * (μ : ℂ)))
    exact h1.cexp
  rw [logDeriv_apply, h.deriv]
  field_simp [Complex.exp_ne_zero]

/-- Above the axis `log f_μ = log b − iμz + log(1 + w'_μ)` at the level of logarithmic derivatives. -/
theorem logDeriv_splitFn_up (hS : InnerSplit a b) {μ : ℝ} (hμ : 0 < μ) {z : ℂ} (hz : 0 < z.im) :
    logDeriv (splitFn a b μ) z =
      logDeriv b z - I * (μ : ℂ) + logDeriv (fun y => 1 + upQ a b μ y) z := by
  have hb := (hS.up z hz).1
  rw [logDeriv_eq_of_eventuallyEq (splitFn_eventuallyEq_up (eventually_b_ne_zero_of_im_pos hS hz))]
  have h1 : 1 + upQ a b μ z ≠ 0 := by
    intro h
    have := norm_upQ_lt_one hS hμ hz
    rw [show upQ a b μ z = -1 by linear_combination h, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  have he : cexp (-(I * (μ : ℂ) * z)) ≠ 0 := Complex.exp_ne_zero _
  have hde : DifferentiableAt ℂ (fun y => cexp (-(I * (μ : ℂ) * y))) z := by fun_prop
  rw [logDeriv_mul (f := fun y => b y * cexp (-(I * (μ : ℂ) * y)))
    (g := fun y => 1 + upQ a b μ y) z (mul_ne_zero hb he) h1 ((hS.db z).mul hde)
    ((differentiableAt_upQ hS μ hb).const_add 1),
    logDeriv_mul (f := b) (g := fun y => cexp (-(I * (μ : ℂ) * y))) z hb he (hS.db z) hde,
    logDeriv_cexp_split]
  ring

theorem continuous_deriv_of_differentiable {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Continuous (deriv g) :=
  (hg.contDiff (n := 1)).continuous_deriv le_rfl

/-- The primitive of `Im (log(1 + w))′` along a horizontal line. -/
theorem integral_im_logDeriv_one_add {g : ℂ → ℂ} {c d s : ℝ}
    (hg : ∀ x : ℝ, DifferentiableAt ℂ g ((x : ℂ) + (s : ℂ) * I))
    (hslit : ∀ x : ℝ, 1 + g ((x : ℂ) + (s : ℂ) * I) ∈ slitPlane)
    (hcont : Continuous fun x : ℝ => (logDeriv (fun y => 1 + g y) ((x : ℂ) + (s : ℂ) * I)).im) :
    ∫ x in c..d, (logDeriv (fun y => 1 + g y) ((x : ℂ) + (s : ℂ) * I)).im =
      (1 + g ((d : ℂ) + (s : ℂ) * I)).arg - (1 + g ((c : ℂ) + (s : ℂ) * I)).arg := by
  have hder : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (1 + g ((x : ℂ) + (s : ℂ) * I)).arg)
      (logDeriv (fun y => 1 + g y) ((x : ℂ) + (s : ℂ) * I)).im x := by
    intro x
    have h1 : HasDerivAt (fun y => 1 + g y) (deriv g ((x : ℂ) + (s : ℂ) * I))
        ((x : ℂ) + (s : ℂ) * I) := (hg x).hasDerivAt.const_add 1
    have h2 := h1.clog (hslit x)
    have h3 : HasDerivAt (fun y : ℂ => y + (s : ℂ) * I) 1 (x : ℂ) := (hasDerivAt_id _).add_const _
    have h4 := (h2.comp (x : ℂ) h3).comp_ofReal
    have h5 := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt x h4
    have hval : logDeriv (fun y => 1 + g y) ((x : ℂ) + (s : ℂ) * I) =
        deriv g ((x : ℂ) + (s : ℂ) * I) / (1 + g ((x : ℂ) + (s : ℂ) * I)) := by
      rw [logDeriv_apply, h1.deriv]
    have h6 : HasDerivAt (fun x : ℝ => (1 + g ((x : ℂ) + (s : ℂ) * I)).arg)
        ((deriv g ((x : ℂ) + (s : ℂ) * I) / (1 + g ((x : ℂ) + (s : ℂ) * I))).im) x := by
      simpa [Function.comp_def, Complex.log_im] using h5
    rw [hval]
    exact h6
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
    (hcont.intervalIntegrable _ _)

theorem continuous_im_logDeriv_line {f : ℂ → ℂ} (hf : Differentiable ℂ f) (s : ℝ)
    (hne : ∀ x : ℝ, f ((x : ℂ) + (s : ℂ) * I) ≠ 0) :
    Continuous fun x : ℝ => (logDeriv f ((x : ℂ) + (s : ℂ) * I)).im := by
  have hpath : Continuous fun x : ℝ => (x : ℂ) + (s : ℂ) * I := by fun_prop
  have h1 := (continuous_deriv_of_differentiable hf).comp hpath
  have h2 := hf.continuous.comp hpath
  have h3 : Continuous fun x : ℝ => deriv f ((x : ℂ) + (s : ℂ) * I) / f ((x : ℂ) + (s : ℂ) * I) :=
    h1.div h2 hne
  refine Complex.continuous_im.comp (h3.congr fun x => ?_)
  rw [logDeriv_apply]

/-- **Lower edge.** -/
theorem integral_lower_edge (hS : InnerSplit a b) {μ : ℝ} (hμ : 0 < μ) {η : ℝ} (hη : 0 < η)
    (c d : ℝ) :
    ∫ x in c..d, (logDeriv (splitFn a b μ) ((x : ℂ) + ((-η : ℝ) : ℂ) * I)).im =
      (∫ x in c..d, (logDeriv a ((x : ℂ) + ((-η : ℝ) : ℂ) * I)).im) +
        ((1 + lowQ a b μ ((d : ℂ) + ((-η : ℝ) : ℂ) * I)).arg -
          (1 + lowQ a b μ ((c : ℂ) + ((-η : ℝ) : ℂ) * I)).arg) := by
  have him : ∀ x : ℝ, ((x : ℂ) + ((-η : ℝ) : ℂ) * I).im < 0 := fun x => by simp; linarith
  have hf := continuous_im_logDeriv_line (differentiable_splitFn hS μ) (-η)
    fun x => splitFn_ne_zero_of_im_neg hS hμ (him x)
  have ha := continuous_im_logDeriv_line hS.da (-η) fun x => (hS.low _ (him x)).1
  have hpt : ∀ x : ℝ, (logDeriv (fun y => 1 + lowQ a b μ y) ((x : ℂ) + ((-η : ℝ) : ℂ) * I)).im =
      (logDeriv (splitFn a b μ) ((x : ℂ) + ((-η : ℝ) : ℂ) * I)).im -
        (logDeriv a ((x : ℂ) + ((-η : ℝ) : ℂ) * I)).im := by
    intro x
    rw [logDeriv_splitFn_low hS hμ (him x), add_im]
    ring
  have hq : Continuous fun x : ℝ =>
      (logDeriv (fun y => 1 + lowQ a b μ y) ((x : ℂ) + ((-η : ℝ) : ℂ) * I)).im :=
    (hf.sub ha).congr fun x => (hpt x).symm
  have hprim := integral_im_logDeriv_one_add (g := lowQ a b μ) (c := c) (d := d) (s := -η)
    (fun x => differentiableAt_lowQ hS μ (hS.low _ (him x)).1)
    (fun x => one_add_mem_slitPlane_of_norm_lt_one (norm_lowQ_lt_one hS hμ (him x))) hq
  rw [← hprim, ← intervalIntegral.integral_add (ha.intervalIntegrable _ _)
    (hq.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun x _ => ?_
  show _ = _ + _
  rw [hpt x]
  ring

/-- **Upper edge.** -/
theorem integral_upper_edge (hS : InnerSplit a b) {μ : ℝ} (hμ : 0 < μ) {η : ℝ} (hη : 0 < η)
    (c d : ℝ) :
    ∫ x in c..d, (logDeriv (splitFn a b μ) ((x : ℂ) + (η : ℂ) * I)).im =
      (∫ x in c..d, (logDeriv b ((x : ℂ) + (η : ℂ) * I)).im) - μ * (d - c) +
        ((1 + upQ a b μ ((d : ℂ) + (η : ℂ) * I)).arg -
          (1 + upQ a b μ ((c : ℂ) + (η : ℂ) * I)).arg) := by
  have him : ∀ x : ℝ, 0 < ((x : ℂ) + (η : ℂ) * I).im := fun x => by simp; linarith
  have hf := continuous_im_logDeriv_line (differentiable_splitFn hS μ) η
    fun x => splitFn_ne_zero_of_im_pos hS hμ (him x)
  have hb := continuous_im_logDeriv_line hS.db η fun x => (hS.up _ (him x)).1
  have hpt : ∀ x : ℝ, (logDeriv (fun y => 1 + upQ a b μ y) ((x : ℂ) + (η : ℂ) * I)).im =
      (logDeriv (splitFn a b μ) ((x : ℂ) + (η : ℂ) * I)).im -
        (logDeriv b ((x : ℂ) + (η : ℂ) * I)).im + μ := by
    intro x
    rw [logDeriv_splitFn_up hS hμ (him x), add_im, sub_im]
    simp
    ring
  have hq : Continuous fun x : ℝ =>
      (logDeriv (fun y => 1 + upQ a b μ y) ((x : ℂ) + (η : ℂ) * I)).im :=
    ((hf.sub hb).add continuous_const).congr fun x => (hpt x).symm
  have hprim := integral_im_logDeriv_one_add (g := upQ a b μ) (c := c) (d := d) (s := η)
    (fun x => differentiableAt_upQ hS μ (hS.up _ (him x)).1)
    (fun x => one_add_mem_slitPlane_of_norm_lt_one (norm_upQ_lt_one hS hμ (him x))) hq
  have hsplit : ∫ x in c..d, (logDeriv (splitFn a b μ) ((x : ℂ) + (η : ℂ) * I)).im =
      ∫ x in c..d, ((logDeriv b ((x : ℂ) + (η : ℂ) * I)).im - μ +
        (logDeriv (fun y => 1 + upQ a b μ y) ((x : ℂ) + (η : ℂ) * I)).im) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    show _ = _
    rw [hpt x]
    ring
  have hi1 : IntervalIntegrable (fun x : ℝ => (logDeriv b ((x : ℂ) + (η : ℂ) * I)).im - μ)
      volume c d := (hb.sub continuous_const).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x : ℝ => (logDeriv b ((x : ℂ) + (η : ℂ) * I)).im)
      volume c d := hb.intervalIntegrable _ _
  rw [hsplit, intervalIntegral.integral_add hi1 (hq.intervalIntegrable _ _),
    intervalIntegral.integral_sub hi2 intervalIntegrable_const, hprim,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-! ## Vertical edges and edge limits -/

/-- Short vertical segments through a non-zero carry vanishing argument variation. -/
theorem tendsto_vertical_integral {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x₀ : ℝ}
    (h : f x₀ ≠ 0) :
    Tendsto (fun η : ℝ => ∫ t in (-η)..η, (logDeriv f ((x₀ : ℂ) + (t : ℂ) * I)).re)
      (𝓝[>] 0) (𝓝 0) := by
  have hcont : ContinuousAt (logDeriv f) (x₀ : ℂ) := by
    have hfun : logDeriv f = fun z => deriv f z / f z := funext fun z => logDeriv_apply _ _
    rw [hfun]
    exact (continuous_deriv_of_differentiable hf).continuousAt.div hf.continuous.continuousAt h
  set M : ℝ := ‖logDeriv f (x₀ : ℂ)‖ + 1 with hM
  have hMpos : 0 < M := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min (δ / 2) (ε / (4 * M)), by positivity, fun η hη hηd => ?_⟩
  have hη0 : 0 < η := hη
  have hηle : η < min (δ / 2) (ε / (4 * M)) := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hη0] at hηd; exact hηd
  have hbound : ∀ y ∈ Set.uIoc (-η) η, ‖(logDeriv f ((x₀ : ℂ) + (y : ℂ) * I)).re‖ ≤ M := by
    intro y hy
    have hy' : |y| ≤ η := by
      rw [uIoc_of_le (by linarith)] at hy
      exact abs_le.mpr ⟨hy.1.le, hy.2⟩
    have hdist : dist ((x₀ : ℂ) + (y : ℂ) * I) (x₀ : ℂ) < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      have : η ≤ δ / 2 := hηle.le.trans (min_le_left _ _)
      linarith
    have hclose := hball hdist
    rw [dist_eq_norm] at hclose
    calc ‖(logDeriv f ((x₀ : ℂ) + (y : ℂ) * I)).re‖
        ≤ ‖logDeriv f ((x₀ : ℂ) + (y : ℂ) * I)‖ := by
          rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
      _ ≤ ‖logDeriv f (x₀ : ℂ)‖ + ‖logDeriv f ((x₀ : ℂ) + (y : ℂ) * I) -
            logDeriv f (x₀ : ℂ)‖ := by
          have := norm_add_le (logDeriv f (x₀ : ℂ))
            (logDeriv f ((x₀ : ℂ) + (y : ℂ) * I) - logDeriv f (x₀ : ℂ))
          rwa [add_sub_cancel] at this
      _ ≤ M := by rw [hM]; linarith
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.dist_eq, sub_zero]
  rw [Real.norm_eq_abs] at hnorm
  refine lt_of_le_of_lt hnorm ?_
  have h2 : |η - -η| = 2 * η := by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]
  rw [h2]
  have : η < ε / (4 * M) := hηle.trans_le (min_le_right _ _)
  calc M * (2 * η) < M * (2 * (ε / (4 * M))) := by gcongr
    _ = ε / 2 := by field_simp; ring
    _ < ε := by linarith

theorem tendsto_arg_one_add {g : ℂ → ℂ} {x₀ : ℝ} (hg : ContinuousAt g (x₀ : ℂ))
    (hslit : 1 + g x₀ ∈ slitPlane) {p : ℝ → ℂ} (hp : Tendsto p (𝓝[>] 0) (𝓝 (x₀ : ℂ))) :
    Tendsto (fun η : ℝ => (1 + g (p η)).arg) (𝓝[>] 0) (𝓝 (1 + g x₀).arg) :=
  (Complex.continuousAt_arg hslit).tendsto.comp ((hg.tendsto.comp hp).const_add 1)

theorem tendsto_lower_path (x₀ : ℝ) :
    Tendsto (fun η : ℝ => (x₀ : ℂ) + ((-η : ℝ) : ℂ) * I) (𝓝[>] 0) (𝓝 (x₀ : ℂ)) := by
  have hc : Continuous fun η : ℝ => (x₀ : ℂ) + ((-η : ℝ) : ℂ) * I := by fun_prop
  have := hc.tendsto 0
  simp only [neg_zero, ofReal_zero, zero_mul, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem tendsto_upper_path (x₀ : ℝ) :
    Tendsto (fun η : ℝ => (x₀ : ℂ) + (η : ℂ) * I) (𝓝[>] 0) (𝓝 (x₀ : ℂ)) := by
  have hc : Continuous fun η : ℝ => (x₀ : ℂ) + (η : ℂ) * I := by fun_prop
  have := hc.tendsto 0
  simp only [ofReal_zero, zero_mul, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-! ## Real-axis values of the quotients -/

theorem norm_lowQ_real (hS : InnerSplit a b) (μ : ℝ) {x : ℝ} (ha : a x ≠ 0) :
    ‖lowQ a b μ x‖ = 1 := by
  rw [lowQ, norm_div, norm_mul, norm_cexp_split, norm_eq_of_real hS x]
  simp only [ofReal_im, mul_zero, Real.exp_zero, mul_one]
  exact div_self (norm_ne_zero_iff.mpr ha)

theorem lowQ_ne_neg_one {μ : ℝ} {x : ℝ} (ha : a x ≠ 0) (hf : splitFn a b μ x ≠ 0) :
    lowQ a b μ x ≠ -1 := by
  intro h
  apply hf
  have : b x * cexp (-(I * (μ : ℂ) * x)) = -a x := by
    have h' := h
    rw [lowQ, div_eq_iff ha] at h'
    linear_combination h'
  simp only [splitFn]
  rw [this]; ring

theorem upQ_eq_conj_lowQ (hS : InnerSplit a b) (μ : ℝ) {x : ℝ} (ha : a x ≠ 0) (hb : b x ≠ 0) :
    upQ a b μ x = (starRingEnd ℂ) (lowQ a b μ x) := by
  have hn := norm_lowQ_real hS μ ha
  have hmul : lowQ a b μ x * upQ a b μ x = 1 := by
    have he : cexp (-(I * (μ : ℂ) * x)) * cexp (I * (μ : ℂ) * x) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [lowQ, upQ, div_mul_div_comm,
      show b x * cexp (-(I * (μ : ℂ) * x)) * (a x * cexp (I * (μ : ℂ) * x)) =
        (a x * b x) * (cexp (-(I * (μ : ℂ) * x)) * cexp (I * (μ : ℂ) * x)) by ring,
      he, mul_one, div_self (mul_ne_zero ha hb)]
  have hne : lowQ a b μ x ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have hinv : upQ a b μ x = (lowQ a b μ x)⁻¹ := eq_inv_of_mul_eq_one_right hmul
  rw [hinv, Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

theorem one_add_lowQ_mem_slitPlane (hS : InnerSplit a b) {μ : ℝ} {x : ℝ}
    (hf : splitFn a b μ x ≠ 0) : 1 + lowQ a b μ x ∈ slitPlane := by
  have ha := a_ne_zero_of_splitFn_ne_zero hS hf
  exact one_add_mem_slitPlane_of_norm_eq_one (norm_lowQ_real hS μ ha) (lowQ_ne_neg_one ha hf)

theorem one_add_upQ_mem_slitPlane (hS : InnerSplit a b) {μ : ℝ} {x : ℝ}
    (hf : splitFn a b μ x ≠ 0) : 1 + upQ a b μ x ∈ slitPlane := by
  have ha := a_ne_zero_of_splitFn_ne_zero hS hf
  have hb := b_ne_zero_of_splitFn_ne_zero hS hf
  rw [upQ_eq_conj_lowQ hS μ ha hb]
  have hu := norm_lowQ_real hS μ ha
  have hu1 := lowQ_ne_neg_one ha hf
  apply one_add_mem_slitPlane_of_norm_eq_one
  · rw [Complex.norm_conj]; exact hu
  · intro h
    apply hu1
    have := congrArg (starRingEnd ℂ) h
    simpa using this

/-- At a real point where `f_μ ≠ 0`, `arg(1 + w_μ) − arg(1 + w'_μ) = arg w_μ`. -/
theorem arg_one_add_lowQ_sub_arg_one_add_upQ (hS : InnerSplit a b) {μ : ℝ} {x : ℝ}
    (hf : splitFn a b μ x ≠ 0) :
    (1 + lowQ a b μ x).arg - (1 + upQ a b μ x).arg = (lowQ a b μ x).arg := by
  have ha := a_ne_zero_of_splitFn_ne_zero hS hf
  have hb := b_ne_zero_of_splitFn_ne_zero hS hf
  rw [upQ_eq_conj_lowQ hS μ ha hb]
  exact arg_one_add_sub_arg_one_add_conj (norm_lowQ_real hS μ ha) (lowQ_ne_neg_one ha hf)

/-! ## The count identity on a thin rectangle -/

/-- **Count identity.** For a thin rectangle `[c, d] × [−η, η]` whose vertical sides avoid the
zeros, `2πN` is the vertical variation plus the two edge expressions. -/
theorem two_pi_mul_zeroCount_eq (hS : InnerSplit a b) {μ : ℝ} (hμ : 0 < μ) {c d : ℝ}
    (hcd : c < d) (hc : splitFn a b μ c ≠ 0) (hd : splitFn a b μ d ≠ 0) (Z : Finset ℂ)
    (hZ : ∀ z, z ∈ Z ↔ z ∈ (uIcc c d ×ℂ uIcc (-1 : ℝ) 1) ∧ splitFn a b μ z = 0)
    {η : ℝ} (hη : 0 < η) :
    2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt (splitFn a b μ) w).toNat : ℝ) =
      ((∫ t in (-η)..η, (logDeriv (splitFn a b μ) ((d : ℂ) + (t : ℂ) * I)).re) -
        ∫ t in (-η)..η, (logDeriv (splitFn a b μ) ((c : ℂ) + (t : ℂ) * I)).re) +
      ((∫ x in c..d, (logDeriv a ((x : ℂ) + ((-η : ℝ) : ℂ) * I)).im) -
        ∫ x in c..d, (logDeriv b ((x : ℂ) + (η : ℂ) * I)).im) + μ * (d - c) +
      ((1 + lowQ a b μ ((d : ℂ) + ((-η : ℝ) : ℂ) * I)).arg -
        (1 + lowQ a b μ ((c : ℂ) + ((-η : ℝ) : ℂ) * I)).arg) -
      ((1 + upQ a b μ ((d : ℂ) + (η : ℂ) * I)).arg -
        (1 + upQ a b μ ((c : ℂ) + (η : ℂ) * I)).arg) := by
  have hf := differentiable_splitFn hS μ
  have hside : ∀ {x : ℝ}, splitFn a b μ x ≠ 0 → ∀ t : ℝ,
      splitFn a b μ ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro x hx t
    by_cases ht : t = 0
    · simpa [ht] using hx
    · exact splitFn_ne_zero_of_im_ne_zero hS hμ (by simpa using ht)
  obtain ⟨Z', hZ', hident⟩ := RHTower.exists_entire_argument_variation_rectangle
    (f := splitFn a b μ) (fun z _ => hf.analyticAt z) (exists_splitFn_ne_zero hS hμ) hcd
    (show -η < η by linarith)
    (fun x _ => splitFn_ne_zero_of_im_neg hS hμ (by simp; linarith))
    (fun x _ => splitFn_ne_zero_of_im_pos hS hμ (by simp; linarith))
    (fun t _ => hside hd t) (fun t _ => hside hc t)
  have hZZ : Z' = Z := by
    ext z
    rw [hZ', hZ]
    simp only [Complex.mem_reProdIm]
    constructor
    · rintro ⟨⟨hre, _⟩, hz⟩
      have him : z.im = 0 := by
        by_contra h; exact splitFn_ne_zero_of_im_ne_zero hS hμ h hz
      refine ⟨⟨hre, ?_⟩, hz⟩
      rw [him, uIcc_of_le (by norm_num)]
      exact ⟨by norm_num, by norm_num⟩
    · rintro ⟨⟨hre, _⟩, hz⟩
      have him : z.im = 0 := by
        by_contra h; exact splitFn_ne_zero_of_im_ne_zero hS hμ h hz
      refine ⟨⟨hre, ?_⟩, hz⟩
      rw [him, uIcc_of_le (by linarith)]
      exact ⟨by linarith, by linarith⟩
  rw [hZZ] at hident
  have hlow := integral_lower_edge hS hμ hη c d
  have hup := integral_upper_edge hS hμ hη c d
  push_cast at hident hlow hup ⊢
  rw [hlow, hup] at hident
  linarith

/-! ## The exact difference -/

/-- **Exact difference.** With the zeros of `f_λ` and `f_ε` in `[c, d]` (endpoints not zeros),
`2π(N_λ − N_ε) = (λ − ε)(d − c) + [arg w_λ]_c^d − [arg w_ε]_c^d`. -/
theorem two_pi_mul_zeroCount_sub_eq (hS : InnerSplit a b) {lam eps : ℝ} (hlam : 0 < lam)
    (heps : 0 < eps) {c d : ℝ} (hcd : c < d)
    (hlc : splitFn a b lam c ≠ 0) (hld : splitFn a b lam d ≠ 0)
    (hec : splitFn a b eps c ≠ 0) (hed : splitFn a b eps d ≠ 0)
    (Zl Ze : Finset ℂ)
    (hZl : ∀ z, z ∈ Zl ↔ z ∈ (uIcc c d ×ℂ uIcc (-1 : ℝ) 1) ∧ splitFn a b lam z = 0)
    (hZe : ∀ z, z ∈ Ze ↔ z ∈ (uIcc c d ×ℂ uIcc (-1 : ℝ) 1) ∧ splitFn a b eps z = 0) :
    2 * Real.pi * ((∑ w ∈ Zl, ((analyticOrderAt (splitFn a b lam) w).toNat : ℝ)) -
        ∑ w ∈ Ze, ((analyticOrderAt (splitFn a b eps) w).toNat : ℝ)) =
      (lam - eps) * (d - c) + ((lowQ a b lam d).arg - (lowQ a b lam c).arg) -
        ((lowQ a b eps d).arg - (lowQ a b eps c).arg) := by
  -- the right-hand side as a function of `η`
  let R : ℝ → ℝ := fun η =>
    (((∫ t in (-η)..η, (logDeriv (splitFn a b lam) ((d : ℂ) + (t : ℂ) * I)).re) -
        ∫ t in (-η)..η, (logDeriv (splitFn a b lam) ((c : ℂ) + (t : ℂ) * I)).re) -
      ((∫ t in (-η)..η, (logDeriv (splitFn a b eps) ((d : ℂ) + (t : ℂ) * I)).re) -
        ∫ t in (-η)..η, (logDeriv (splitFn a b eps) ((c : ℂ) + (t : ℂ) * I)).re)) +
    (lam - eps) * (d - c) +
    (((1 + lowQ a b lam ((d : ℂ) + ((-η : ℝ) : ℂ) * I)).arg -
        (1 + lowQ a b lam ((c : ℂ) + ((-η : ℝ) : ℂ) * I)).arg) -
      ((1 + lowQ a b eps ((d : ℂ) + ((-η : ℝ) : ℂ) * I)).arg -
        (1 + lowQ a b eps ((c : ℂ) + ((-η : ℝ) : ℂ) * I)).arg)) -
    (((1 + upQ a b lam ((d : ℂ) + (η : ℂ) * I)).arg -
        (1 + upQ a b lam ((c : ℂ) + (η : ℂ) * I)).arg) -
      ((1 + upQ a b eps ((d : ℂ) + (η : ℂ) * I)).arg -
        (1 + upQ a b eps ((c : ℂ) + (η : ℂ) * I)).arg))
  have hkey : ∀ η : ℝ, 0 < η →
      2 * Real.pi * ((∑ w ∈ Zl, ((analyticOrderAt (splitFn a b lam) w).toNat : ℝ)) -
        ∑ w ∈ Ze, ((analyticOrderAt (splitFn a b eps) w).toNat : ℝ)) = R η := by
    intro η hη
    have h1 := two_pi_mul_zeroCount_eq hS hlam hcd hlc hld Zl hZl hη
    have h2 := two_pi_mul_zeroCount_eq hS heps hcd hec hed Ze hZe hη
    simp only [R]
    linarith
  -- limits of the pieces
  have hlcA := a_ne_zero_of_splitFn_ne_zero hS hlc
  have hldA := a_ne_zero_of_splitFn_ne_zero hS hld
  have hecA := a_ne_zero_of_splitFn_ne_zero hS hec
  have hedA := a_ne_zero_of_splitFn_ne_zero hS hed
  have hlcB := b_ne_zero_of_splitFn_ne_zero hS hlc
  have hldB := b_ne_zero_of_splitFn_ne_zero hS hld
  have hecB := b_ne_zero_of_splitFn_ne_zero hS hec
  have hedB := b_ne_zero_of_splitFn_ne_zero hS hed
  have tV := fun (μ : ℝ) (x : ℝ) (h : splitFn a b μ x ≠ 0) =>
    tendsto_vertical_integral (differentiable_splitFn hS μ) h
  have tL := fun (μ : ℝ) (x : ℝ) (h : splitFn a b μ x ≠ 0) =>
    tendsto_arg_one_add (differentiableAt_lowQ hS μ (a_ne_zero_of_splitFn_ne_zero hS h)).continuousAt
      (one_add_lowQ_mem_slitPlane hS h) (tendsto_lower_path x)
  have tU := fun (μ : ℝ) (x : ℝ) (h : splitFn a b μ x ≠ 0) =>
    tendsto_arg_one_add (differentiableAt_upQ hS μ (b_ne_zero_of_splitFn_ne_zero hS h)).continuousAt
      (one_add_upQ_mem_slitPlane hS h) (tendsto_upper_path x)
  have hT : Tendsto R (𝓝[>] 0) (𝓝 (((0 - 0) - (0 - 0)) + (lam - eps) * (d - c) +
      (((1 + lowQ a b lam d).arg - (1 + lowQ a b lam c).arg) -
        ((1 + lowQ a b eps d).arg - (1 + lowQ a b eps c).arg)) -
      (((1 + upQ a b lam d).arg - (1 + upQ a b lam c).arg) -
        ((1 + upQ a b eps d).arg - (1 + upQ a b eps c).arg)))) := by
    refine ((((((tV lam d hld).sub (tV lam c hlc)).sub ((tV eps d hed).sub (tV eps c hec))).add
      tendsto_const_nhds).add (((tL lam d hld).sub (tL lam c hlc)).sub
      ((tL eps d hed).sub (tL eps c hec)))).sub (((tU lam d hld).sub (tU lam c hlc)).sub
      ((tU eps d hed).sub (tU eps c hec))))
  have hconst : Tendsto R (𝓝[>] 0)
      (𝓝 (2 * Real.pi * ((∑ w ∈ Zl, ((analyticOrderAt (splitFn a b lam) w).toNat : ℝ)) -
        ∑ w ∈ Ze, ((analyticOrderAt (splitFn a b eps) w).toNat : ℝ)))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hkey η hη
  rw [tendsto_nhds_unique hconst hT]
  have e1 := arg_one_add_lowQ_sub_arg_one_add_upQ hS hld
  have e2 := arg_one_add_lowQ_sub_arg_one_add_upQ hS hlc
  have e3 := arg_one_add_lowQ_sub_arg_one_add_upQ hS hed
  have e4 := arg_one_add_lowQ_sub_arg_one_add_upQ hS hec
  linarith

/-! ## Rounding -/

/-- The winding index `k(y) = ⌈(y − π)/2π⌉`, so that `arg e^{iy} = y − 2πk(y)`. -/
def windIdx (y : ℝ) : ℤ := ⌈(y - Real.pi) / (2 * Real.pi)⌉

theorem arg_cexp_eq_sub_windIdx (y : ℝ) :
    (cexp ((y : ℂ) * I)).arg = y - 2 * Real.pi * windIdx y := by
  have hπ := Real.pi_pos
  set k := windIdx y with hk
  have h1 : (y - Real.pi) / (2 * Real.pi) ≤ k := Int.le_ceil _
  have h2 : (k : ℝ) < (y - Real.pi) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
  have h1' : y - Real.pi ≤ 2 * Real.pi * k := by
    rw [div_le_iff₀ (by positivity)] at h1; linarith
  have h2' : 2 * Real.pi * k < y + Real.pi := by
    have h := mul_lt_mul_of_pos_left h2 (show (0 : ℝ) < 2 * Real.pi by positivity)
    have e : 2 * Real.pi * ((y - Real.pi) / (2 * Real.pi) + 1) = y + Real.pi := by
      field_simp; ring
    linarith
  have hmem : y - 2 * Real.pi * k ∈ Ioc (-Real.pi) Real.pi := ⟨by linarith, by linarith⟩
  have hexp : cexp ((y : ℂ) * I) = cexp (((y - 2 * Real.pi * k : ℝ) : ℂ) * I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨k, by push_cast; ring⟩
  rw [hexp, arg_cexp_mul_I hmem]

theorem windIdx_sub_windIdx_ge (y D : ℝ) :
    ⌊D / (2 * Real.pi)⌋ ≤ windIdx y - windIdx (y - D) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  unfold windIdx
  set x := (y - Real.pi) / (2 * Real.pi)
  have hx : (y - D - Real.pi) / (2 * Real.pi) = x - D / (2 * Real.pi) := by
    simp only [x]; field_simp; ring
  rw [hx]
  have h1 := Int.le_ceil x
  have h2 : (⌈x - D / (2 * Real.pi)⌉ : ℝ) < x - D / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
  have h3 := Int.floor_le (D / (2 * Real.pi))
  have h4 : ⌊D / (2 * Real.pi)⌋ + ⌈x - D / (2 * Real.pi)⌉ ≤ ⌈x⌉ := by
    rw [← Int.lt_add_one_iff]
    exact_mod_cast (show ((⌊D / (2 * Real.pi)⌋ + ⌈x - D / (2 * Real.pi)⌉ : ℤ) : ℝ) < ⌈x⌉ + 1 by
      push_cast; linarith)
  omega

/-- On the real axis `w_μ(x) = e^{i(θ − μx)}` with `θ = arg(b/a)`. -/
theorem lowQ_real_eq (hS : InnerSplit a b) (μ : ℝ) {x : ℝ} (ha : a x ≠ 0) :
    lowQ a b μ x = cexp ((((b x / a x).arg - μ * x : ℝ) : ℂ) * I) := by
  have hG : ‖b x / a x‖ = 1 := by
    rw [norm_div, norm_eq_of_real hS x]; exact div_self (norm_ne_zero_iff.mpr ha)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (b x / a x).arg := ⟨_, rfl⟩
  have hGexp : b x / a x = cexp ((θ : ℂ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I (b x / a x)
    rw [hG, ← hθ] at this
    simpa using this.symm
  rw [← hθ, lowQ, mul_div_right_comm, hGexp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem arg_lowQ_real (hS : InnerSplit a b) (μ : ℝ) {x : ℝ} (ha : a x ≠ 0) :
    (lowQ a b μ x).arg = ((b x / a x).arg - μ * x) -
      2 * Real.pi * windIdx ((b x / a x).arg - μ * x) := by
  rw [lowQ_real_eq hS μ ha, arg_cexp_eq_sub_windIdx]

/-- **Integer form of the exact difference.** -/
theorem zeroCount_sub_eq_windIdx (hS : InnerSplit a b) {lam eps : ℝ} (hlam : 0 < lam)
    (heps : 0 < eps) {c d : ℝ} (hcd : c < d)
    (hlc : splitFn a b lam c ≠ 0) (hld : splitFn a b lam d ≠ 0)
    (hec : splitFn a b eps c ≠ 0) (hed : splitFn a b eps d ≠ 0)
    (Zl Ze : Finset ℂ)
    (hZl : ∀ z, z ∈ Zl ↔ z ∈ (uIcc c d ×ℂ uIcc (-1 : ℝ) 1) ∧ splitFn a b lam z = 0)
    (hZe : ∀ z, z ∈ Ze ↔ z ∈ (uIcc c d ×ℂ uIcc (-1 : ℝ) 1) ∧ splitFn a b eps z = 0) :
    ((∑ w ∈ Zl, ((analyticOrderAt (splitFn a b lam) w).toNat : ℝ)) -
        ∑ w ∈ Ze, ((analyticOrderAt (splitFn a b eps) w).toNat : ℝ)) =
      ((windIdx ((b d / a d).arg - eps * d) - windIdx ((b d / a d).arg - lam * d) : ℤ) : ℝ) -
        ((windIdx ((b c / a c).arg - eps * c) - windIdx ((b c / a c).arg - lam * c) : ℤ) : ℝ) := by
  have h := two_pi_mul_zeroCount_sub_eq hS hlam heps hcd hlc hld hec hed Zl Ze hZl hZe
  rw [arg_lowQ_real hS lam (a_ne_zero_of_splitFn_ne_zero hS hld),
    arg_lowQ_real hS lam (a_ne_zero_of_splitFn_ne_zero hS hlc),
    arg_lowQ_real hS eps (a_ne_zero_of_splitFn_ne_zero hS hed),
    arg_lowQ_real hS eps (a_ne_zero_of_splitFn_ne_zero hS hec)] at h
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  push_cast
  apply mul_left_cancel₀ hπ.ne'
  rw [h]
  ring

/-! ## Monotonicity of the boundary phase -/

theorem hasDerivAt_arg_quot (hS : InnerSplit a b) {x : ℝ} (ha : a x ≠ 0)
    (hslit : b x / a x ∈ slitPlane) :
    HasDerivAt (fun x : ℝ => (b x / a x).arg)
      ((deriv (fun z => b z / a z) (x : ℂ) / (b x / a x)).im) x := by
  have hG : DifferentiableAt ℂ (fun z => b z / a z) (x : ℂ) := (hS.db x).div (hS.da x) ha
  have h1 := hG.hasDerivAt.clog hslit
  have h2 := h1.comp_ofReal
  have h3 := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt x h2
  simpa [Function.comp_def, Complex.log_im] using h3

theorem deriv_arg_quot_nonpos (hS : InnerSplit a b) {x : ℝ} (ha : a x ≠ 0) :
    (deriv (fun z => b z / a z) (x : ℂ) / (b x / a x)).im ≤ 0 := by
  have hG : DifferentiableAt ℂ (fun z => b z / a z) (x : ℂ) := (hS.db x).div (hS.da x) ha
  have hone : ‖(fun z => b z / a z) (x : ℂ)‖ = 1 := by
    simp only [norm_div, norm_eq_of_real hS x]; exact div_self (norm_ne_zero_iff.mpr ha)
  have h := RHTower.LeeYangFirstZero.im_deriv_div_le (lam := 0) hG hone (fun s hs => by
    have him : ((x : ℂ) - (s : ℂ) * I).im < 0 := by simp; linarith
    obtain ⟨ha', hb'⟩ := hS.low _ him
    simp only [zero_mul, neg_zero, Real.exp_zero, norm_div]
    exact (div_le_one (norm_pos_iff.mpr ha')).mpr hb')
  simpa using h

/-- `arg(b/a)` is non-increasing on an interval of the real axis avoiding the zeros of `a` and
the cut. -/
theorem antitoneOn_arg_quot (hS : InnerSplit a b) {p q : ℝ}
    (ha : ∀ x ∈ Icc p q, a x ≠ 0) (hslit : ∀ x ∈ Icc p q, b x / a x ∈ slitPlane) :
    AntitoneOn (fun x : ℝ => (b x / a x).arg) (Icc p q) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc p q)
  · intro x hx
    exact (hasDerivAt_arg_quot hS (ha x hx) (hslit x hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact (hasDerivAt_arg_quot hS (ha x hx') (hslit x hx')).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' := interior_subset hx
    rw [(hasDerivAt_arg_quot hS (ha x hx') (hslit x hx')).deriv]
    exact deriv_arg_quot_nonpos hS (ha x hx')

/-! ## Endpoint choices -/

/-- Real zeros of a non-trivial entire function are isolated from the right. -/
theorem eventually_ne_zero_right {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0)
    (x₀ : ℝ) : ∀ᶠ x : ℝ in 𝓝[>] x₀, f x ≠ 0 := by
  rcases (hf.analyticAt (x₀ : ℂ)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨z, hz⟩ := hne
    have hA : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
    have hzero := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ (x₀ : ℂ)) h
    exact hz (hzero (Set.mem_univ z))
  · have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] x₀) (𝓝[≠] (x₀ : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (Complex.continuous_ofReal.tendsto x₀).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        intro h'
        have : x = x₀ := Complex.ofReal_injective h'
        exact (lt_irrefl x₀) (this ▸ hx)
    exact ht.eventually h

theorem exists_Ioo_ne_zero {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfne : ∃ z, f z ≠ 0) (hgne : ∃ z, g z ≠ 0) (x₀ : ℝ) :
    ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), f x ≠ 0 ∧ g x ≠ 0 := by
  have h := (eventually_ne_zero_right hf hfne x₀).and (eventually_ne_zero_right hg hgne x₀)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hball⟩ := h
  refine ⟨δ, hδ, fun x hx => hball ?_ hx.1⟩
  rw [Real.dist_eq, abs_of_pos (by linarith [hx.1])]
  linarith [hx.2]

theorem windIdx_eq_zero_or_neg_one {θ μ c : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) (hc : 0 < c)
    (hμ : 0 < μ) (hμc : μ * c < Real.pi) :
    (windIdx (θ - μ * c) = 0 ↔ μ * c - Real.pi < θ) ∧
      (windIdx (θ - μ * c) = -1 ↔ θ ≤ μ * c - Real.pi) := by
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  unfold windIdx
  have hlo : -1 - 1 < (θ - μ * c - Real.pi) / (2 * Real.pi) := by
    rw [lt_div_iff₀ h2π]; nlinarith [hθ.1]
  have hhi : (θ - μ * c - Real.pi) / (2 * Real.pi) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ h2π.le; nlinarith [hθ.2]
  constructor
  · rw [Int.ceil_eq_iff]
    constructor
    · rintro ⟨h1, _⟩
      have : (-1 : ℝ) < (θ - μ * c - Real.pi) / (2 * Real.pi) := by exact_mod_cast (by simpa using h1)
      rw [lt_div_iff₀ h2π] at this; linarith
    · intro h
      refine ⟨?_, by exact_mod_cast hhi⟩
      have : (-1 : ℝ) < (θ - μ * c - Real.pi) / (2 * Real.pi) := by
        rw [lt_div_iff₀ h2π]; linarith
      push_cast; linarith
  · rw [Int.ceil_eq_iff]
    constructor
    · rintro ⟨_, h2⟩
      have : (θ - μ * c - Real.pi) / (2 * Real.pi) ≤ -1 := by exact_mod_cast h2
      rw [div_le_iff₀ h2π] at this; linarith
    · intro h
      refine ⟨by push_cast; linarith, ?_⟩
      push_cast
      rw [div_le_iff₀ h2π]; linarith

/-- The left endpoint can be chosen so that it contributes nothing. -/
theorem exists_left_endpoint (hS : InnerSplit a b) {lam eps c₁ : ℝ} (heps : 0 < eps)
    (hle : eps < lam) (hc₁ : 0 < c₁) (hlc₁ : lam * c₁ < Real.pi)
    (ha : ∀ x ∈ Ioo 0 c₁, a x ≠ 0) :
    ∃ c ∈ Ioo 0 c₁, windIdx ((b c / a c).arg - eps * c) = windIdx ((b c / a c).arg - lam * c) := by
  by_contra hcon
  push Not at hcon
  have hlam : 0 < lam := heps.trans hle
  -- on `(0, c₁)` the phase lies in `(εc − π, λc − π]`
  have hwin : ∀ c ∈ Ioo 0 c₁, eps * c - Real.pi < (b c / a c).arg ∧
      (b c / a c).arg ≤ lam * c - Real.pi := by
    intro c hc
    have hθ := Complex.arg_mem_Ioc (b c / a c)
    have hepsc : eps * c < Real.pi := by nlinarith [hc.1, hc.2]
    have hlamc : lam * c < Real.pi := by nlinarith [hc.1, hc.2]
    have he := windIdx_eq_zero_or_neg_one hθ hc.1 heps hepsc
    have hl := windIdx_eq_zero_or_neg_one hθ hc.1 hlam hlamc
    have hne := hcon c hc
    by_cases h1 : eps * c - Real.pi < (b c / a c).arg
    · refine ⟨h1, ?_⟩
      by_contra h2
      push Not at h2
      exact hne ((he.1.mpr h1).trans (hl.1.mpr h2).symm)
    · push Not at h1
      exfalso
      have h2 : (b c / a c).arg ≤ lam * c - Real.pi := by nlinarith [hc.1]
      exact hne ((he.2.mpr h1).trans (hl.2.mpr h2).symm)
  set c' := c₁ / 2 with hc'
  have hc'mem : c' ∈ Ioo 0 c₁ := ⟨by positivity, by linarith⟩
  set c := min (c' / 2) (eps * c' / (2 * lam)) with hcdef
  have hcpos : 0 < c := lt_min (by positivity) (by positivity)
  have hcc' : c < c' := lt_of_le_of_lt (min_le_left _ _) (by linarith [hc'mem.1])
  have hcmem : c ∈ Ioo 0 c₁ := ⟨hcpos, by linarith [hc'mem.2]⟩
  have hlamc : lam * c < eps * c' := by
    have : c ≤ eps * c' / (2 * lam) := min_le_right _ _
    have h2 : lam * c ≤ eps * c' / 2 := by
      rw [le_div_iff₀ (by positivity)] at this; nlinarith
    nlinarith [hc'mem.1]
  -- antitonicity on `[c, c']`
  have hsub : Icc c c' ⊆ Ioo 0 c₁ := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, hc'mem.2]⟩
  have hslit : ∀ x ∈ Icc c c', b x / a x ∈ slitPlane := by
    intro x hx
    have hw := hwin x (hsub hx)
    have hneg : (b x / a x).arg < 0 := by
      have : lam * x < Real.pi := by nlinarith [(hsub hx).1, (hsub hx).2]
      linarith [hw.2]
    rw [Complex.mem_slitPlane_iff]
    right
    intro him
    have hθ := Complex.arg_mem_Ioc (b x / a x)
    have hpos : 0 ≤ (b x / a x).arg := by
      rw [Complex.arg_nonneg_iff]; exact him.symm ▸ le_refl 0
    linarith
  have hanti := antitoneOn_arg_quot hS (fun x hx => ha x (hsub hx)) hslit
  have hmono := hanti ⟨le_refl c, hcc'.le⟩ ⟨hcc'.le, le_refl c'⟩ hcc'.le
  have h1 := (hwin c hcmem).2
  have h2 := (hwin c' hc'mem).1
  simp only at hmono
  linarith

/-! ## The count difference on `(0, T]` -/

/-- **Count difference.** For an inner split, `0 < ε < λ` and `T > 0`, the zeros of `f_λ` in
`(0, T]` outnumber those of `f_ε` by at least `⌊(λ − ε)T/2π⌋`, with multiplicity. -/
theorem zeroCount_sub_ge (hS : InnerSplit a b) {lam eps T : ℝ} (heps : 0 < eps) (hle : eps < lam)
    (hT : 0 < T) (Zl Ze : Finset ℂ)
    (hZl : ∀ z, z ∈ Zl ↔ z.im = 0 ∧ z.re ∈ Ioc 0 T ∧ splitFn a b lam z = 0)
    (hZe : ∀ z, z ∈ Ze ↔ z.im = 0 ∧ z.re ∈ Ioc 0 T ∧ splitFn a b eps z = 0) :
    (∑ w ∈ Ze, ((analyticOrderAt (splitFn a b eps) w).toNat : ℝ)) +
        (⌊(lam - eps) * T / (2 * Real.pi)⌋ : ℝ) ≤
      ∑ w ∈ Zl, ((analyticOrderAt (splitFn a b lam) w).toNat : ℝ) := by
  have hlam : 0 < lam := heps.trans hle
  have hπ := Real.pi_pos
  have hfl := differentiable_splitFn hS lam
  have hfe := differentiable_splitFn hS eps
  obtain ⟨δ₀, hδ₀, h0⟩ := exists_Ioo_ne_zero hfl hfe (exists_splitFn_ne_zero hS hlam)
    (exists_splitFn_ne_zero hS heps) 0
  obtain ⟨δ₁, hδ₁, h1⟩ := exists_Ioo_ne_zero hfl hfe (exists_splitFn_ne_zero hS hlam)
    (exists_splitFn_ne_zero hS heps) T
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = min δ₀ (min T (Real.pi / (2 * lam))) := ⟨_, rfl⟩
  have hc₁pos : 0 < c₁ := by rw [hc₁]; exact lt_min hδ₀ (lt_min hT (by positivity))
  have hc₁δ : c₁ ≤ δ₀ := by rw [hc₁]; exact min_le_left _ _
  have hc₁T : c₁ ≤ T := by rw [hc₁]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hlc₁ : lam * c₁ < Real.pi := by
    have : c₁ ≤ Real.pi / (2 * lam) := by rw [hc₁]; exact (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hsmall : ∀ x ∈ Ioo 0 c₁, splitFn a b lam x ≠ 0 ∧ splitFn a b eps x ≠ 0 := fun x hx =>
    h0 x ⟨hx.1, by linarith [hx.2]⟩
  obtain ⟨c, hc, hwind⟩ := exists_left_endpoint hS heps hle hc₁pos hlc₁
    (fun x hx => a_ne_zero_of_splitFn_ne_zero hS (hsmall x hx).1)
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = T + δ₁ / 2 := ⟨_, rfl⟩
  have hdmem : d ∈ Ioo T (T + δ₁) := ⟨by rw [hd]; linarith, by rw [hd]; linarith⟩
  have hcd : c < d := by linarith [hc.2, hdmem.1]
  -- the zero sets on `[c, d]`
  have hreal : ∀ {μ : ℝ}, 0 < μ → ∀ z : ℂ, splitFn a b μ z = 0 → z = (z.re : ℂ) := by
    intro μ hμ z hz
    have him : z.im = 0 := by
      by_contra h; exact splitFn_ne_zero_of_im_ne_zero hS hμ h hz
    exact Complex.ext (by simp) (by simp [him])
  have hchar : ∀ {μ : ℝ}, 0 < μ → (∀ x ∈ Ioo 0 c₁, splitFn a b μ x ≠ 0) →
      (∀ x ∈ Ioo T (T + δ₁), splitFn a b μ x ≠ 0) → ∀ z : ℂ,
      (z.im = 0 ∧ z.re ∈ Ioc 0 T ∧ splitFn a b μ z = 0) ↔
        (z ∈ (uIcc c d ×ℂ uIcc (-1 : ℝ) 1) ∧ splitFn a b μ z = 0) := by
    intro μ hμ hlow hhigh z
    rw [Complex.mem_reProdIm, uIcc_of_le hcd.le, uIcc_of_le (by norm_num)]
    constructor
    · rintro ⟨him, ⟨hre0, hreT⟩, hz⟩
      refine ⟨⟨⟨?_, by linarith [hdmem.1]⟩, ⟨by rw [him]; norm_num, by rw [him]; norm_num⟩⟩, hz⟩
      by_contra hlt
      push Not at hlt
      apply hlow z.re ⟨hre0, by linarith [hc.2]⟩
      rw [← hreal hμ z hz]; exact hz
    · rintro ⟨⟨⟨hcre, hred⟩, _⟩, hz⟩
      have him : z.im = 0 := by
        by_contra h; exact splitFn_ne_zero_of_im_ne_zero hS hμ h hz
      refine ⟨him, ⟨by linarith [hc.1], ?_⟩, hz⟩
      by_contra hgt
      push Not at hgt
      apply hhigh z.re ⟨hgt, by linarith [hdmem.2]⟩
      rw [← hreal hμ z hz]; exact hz
  have hZl' : ∀ z, z ∈ Zl ↔ z ∈ (uIcc c d ×ℂ uIcc (-1 : ℝ) 1) ∧ splitFn a b lam z = 0 :=
    fun z => (hZl z).trans (hchar hlam (fun x hx => (hsmall x hx).1) (fun x hx => (h1 x hx).1) z)
  have hZe' : ∀ z, z ∈ Ze ↔ z ∈ (uIcc c d ×ℂ uIcc (-1 : ℝ) 1) ∧ splitFn a b eps z = 0 :=
    fun z => (hZe z).trans (hchar heps (fun x hx => (hsmall x hx).2) (fun x hx => (h1 x hx).2) z)
  have hcl := (hsmall c hc).1
  have hce := (hsmall c hc).2
  have hdl := (h1 d hdmem).1
  have hde := (h1 d hdmem).2
  have hdiff := zeroCount_sub_eq_windIdx hS hlam heps hcd hcl hdl hce hde Zl Ze hZl' hZe'
  rw [hwind, sub_self, Int.cast_zero, sub_zero] at hdiff
  have hbound := windIdx_sub_windIdx_ge ((b d / a d).arg - eps * d) ((lam - eps) * d)
  rw [show (b d / a d).arg - eps * d - (lam - eps) * d = (b d / a d).arg - lam * d by ring]
    at hbound
  have hfloor : ⌊(lam - eps) * T / (2 * Real.pi)⌋ ≤ ⌊(lam - eps) * d / (2 * Real.pi)⌋ := by
    apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hdmem.1.le (by linarith)
  have hcast : (⌊(lam - eps) * T / (2 * Real.pi)⌋ : ℝ) ≤
      ((windIdx ((b d / a d).arg - eps * d) - windIdx ((b d / a d).arg - lam * d) : ℤ) : ℝ) := by
    exact_mod_cast hfloor.trans hbound
  linarith

end

end RHTower.LeeYangSplitCount
