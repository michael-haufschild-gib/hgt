import Mathlib

/-!
# Phase rigidity of the lower Pólya class

`LowerPolyaClass G` means `G` is a locally uniform limit of polynomials whose roots all lie in the
closed lower half-plane `Im ≤ 0`. For `h > 0` the phase speed of `t ↦ G(t + ih)` is

  `ω(t) = −Im (G'/G)(t + ih)`.

For a polynomial it is the Poisson sum `Σ_r (h − Im r)/((t − Re r)² + (h − Im r)²)` over the roots
(`neg_im_logDeriv_eval_eq_sum`). Every term has depth `h − Im r ≥ h`, so it changes by at most
the factor `e^{2|s−t|/h}` between `t` and `s` (`poissonTerm_le_exp_mul`).

**Theorem** (`LowerPolyaClass.phaseSpeed_le_exp_mul`). If `G` is in the class and `G(t + ih) ≠ 0`
on the line, then `ω(s) ≤ e^{2|s−t|/h} ω(t)` for all real `s, t`. The phase speed of a lower Pólya
function is log-Lipschitz with constant `2/h`. The inequality passes to the limit because the
derivatives of the approximants converge locally uniformly.
-/

open Complex Filter Topology Set Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The lower Pólya class: locally uniform limits of polynomials with roots in `Im ≤ 0`. -/
def LowerPolyaClass (G : ℂ → ℂ) : Prop :=
  ∃ p : ℕ → ℂ[X], (∀ m, ∀ r ∈ (p m).roots, r.im ≤ 0) ∧
    TendstoLocallyUniformly (fun m z => (p m).eval z) G atTop

/-- The Poisson term `b/((t − a)² + b²)` of a root at depth `b`. -/
def poissonTerm (a b t : ℝ) : ℝ := b / ((t - a) ^ 2 + b ^ 2)

/-- `u² + b² ≤ e^{2d/b}(v² + b²)` when `|u| ≤ |v| + d`, `b > 0`, `d ≥ 0`. -/
theorem sq_add_sq_le_exp_mul {u v b d : ℝ} (hb0 : 0 < b) (hd0 : 0 ≤ d) (huv : |u| ≤ |v| + d) :
    u ^ 2 + b ^ 2 ≤ Real.exp (2 * d / b) * (v ^ 2 + b ^ 2) := by
  have hexp := Real.quadratic_le_exp_of_nonneg (x := 2 * d / b) (by positivity)
  have h1 : u ^ 2 ≤ (|v| + d) ^ 2 := by
    rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg _) huv 2
  have hv2 : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
  have f1 : 2 * |v| * d ≤ (2 * d / b) * (|v| ^ 2 + b ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hb0]
    nlinarith [sq_nonneg (|v| - b), abs_nonneg v]
  have f2 : d ^ 2 ≤ ((2 * d / b) ^ 2 / 2) * (|v| ^ 2 + b ^ 2) := by
    have e : ((2 * d / b) ^ 2 / 2) * (|v| ^ 2 + b ^ 2) = 2 * d ^ 2 * (|v| ^ 2 + b ^ 2) / b ^ 2 := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|v|), sq_nonneg d, mul_nonneg (sq_nonneg d) (sq_nonneg |v|)]
  have h2 : (|v| + d) ^ 2 + b ^ 2 ≤ (1 + 2 * d / b + (2 * d / b) ^ 2 / 2) * (|v| ^ 2 + b ^ 2) := by
    nlinarith
  have h3 := mul_le_mul_of_nonneg_right hexp (show 0 ≤ |v| ^ 2 + b ^ 2 by positivity)
  rw [hv2]
  linarith

/-- **The Poisson term is log-Lipschitz.** For depth `b ≥ h > 0`,
`poissonTerm a b s ≤ e^{2|s − t|/h} poissonTerm a b t`. -/
theorem poissonTerm_le_exp_mul {a b h : ℝ} (hh : 0 < h) (hb : h ≤ b) (s t : ℝ) :
    poissonTerm a b s ≤ Real.exp (2 * |s - t| / h) * poissonTerm a b t := by
  have hb0 : 0 < b := lt_of_lt_of_le hh hb
  have huv : |t - a| ≤ |s - a| + |s - t| := by
    have : t - a = (s - a) - (s - t) := by ring
    rw [this]; exact abs_sub _ _
  have hkey := sq_add_sq_le_exp_mul hb0 (abs_nonneg (s - t)) huv
  have hmono : Real.exp (2 * |s - t| / b) ≤ Real.exp (2 * |s - t| / h) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) hh hb)
  have hkey' : (t - a) ^ 2 + b ^ 2 ≤ Real.exp (2 * |s - t| / h) * ((s - a) ^ 2 + b ^ 2) :=
    hkey.trans (mul_le_mul_of_nonneg_right hmono (by positivity))
  unfold poissonTerm
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey', hb0]

/-- **The phase speed of a polynomial is a Poisson sum over its roots.** -/
theorem neg_im_logDeriv_eval_eq_sum {p : ℂ[X]} {h t : ℝ}
    (hz : p.eval ((t : ℂ) + h * I) ≠ 0) :
    -((p.derivative.eval ((t : ℂ) + h * I)) / (p.eval ((t : ℂ) + h * I))).im =
      (p.roots.map (fun r => poissonTerm r.re (h - r.im) t)).sum := by
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hz]
  have him : ((p.roots.map fun z => 1 / ((t : ℂ) + h * I - z)).sum).im =
      (p.roots.map fun z => (1 / ((t : ℂ) + h * I - z)).im).sum := by
    rw [show (fun z => (1 / ((t : ℂ) + h * I - z)).im) =
      (Complex.imAddGroupHom ∘ fun z => 1 / ((t : ℂ) + h * I - z)) from rfl, ← Multiset.map_map,
      ← map_multiset_sum]
    rfl
  rw [him, ← Multiset.sum_map_neg]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  rw [one_div, Complex.inv_im, Complex.normSq_apply, poissonTerm]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring

/-- Poisson sums over roots in `Im ≤ 0` are nonnegative and log-Lipschitz. -/
theorem rootPoissonSum_le_exp_mul {p : ℂ[X]} (hroots : ∀ r ∈ p.roots, r.im ≤ 0) {h : ℝ}
    (hh : 0 < h) (s t : ℝ) :
    (p.roots.map (fun r => poissonTerm r.re (h - r.im) s)).sum ≤
      Real.exp (2 * |s - t| / h) * (p.roots.map (fun r => poissonTerm r.re (h - r.im) t)).sum := by
  rw [← Multiset.sum_map_mul_left]
  refine Multiset.sum_map_le_sum_map _ _ fun r hr => ?_
  exact poissonTerm_le_exp_mul hh (by linarith [hroots r hr]) s t

theorem rootPoissonSum_nonneg {p : ℂ[X]} (hroots : ∀ r ∈ p.roots, r.im ≤ 0) {h : ℝ}
    (hh : 0 < h) (t : ℝ) : 0 ≤ (p.roots.map (fun r => poissonTerm r.re (h - r.im) t)).sum := by
  refine Multiset.sum_nonneg fun x hx => ?_
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
  unfold poissonTerm
  have : 0 < h - r.im := by linarith [hroots r hr]
  positivity

/-- The phase speed `−Im (G'/G)(t + ih)` of `t ↦ G(t + ih)`. -/
def phaseSpeed (G : ℂ → ℂ) (h t : ℝ) : ℝ :=
  -((deriv G ((t : ℂ) + h * I)) / (G ((t : ℂ) + h * I))).im

/-- A lower Pólya function is entire. -/
theorem LowerPolyaClass.differentiable {G : ℂ → ℂ} (hG : LowerPolyaClass G) :
    Differentiable ℂ G := by
  obtain ⟨p, -, hconv⟩ := hG
  have := (tendstoLocallyUniformlyOn_univ.mpr hconv).differentiableOn
    (Eventually.of_forall fun m => (Polynomial.differentiable (p m)).differentiableOn) isOpen_univ
  exact differentiableOn_univ.mp this

/-- **Phase rigidity of the lower Pólya class.** If `G` is a lower Pólya function with no zero on
the line `Im z = h > 0`, its phase speed there is nonnegative and log-Lipschitz:
`ω(s) ≤ e^{2|s − t|/h} ω(t)`. -/
theorem LowerPolyaClass.phaseSpeed_le_exp_mul {G : ℂ → ℂ} (hG : LowerPolyaClass G) {h : ℝ}
    (hh : 0 < h) (hne : ∀ t : ℝ, G ((t : ℂ) + h * I) ≠ 0) (s t : ℝ) :
    0 ≤ phaseSpeed G h t ∧ phaseSpeed G h s ≤ Real.exp (2 * |s - t| / h) * phaseSpeed G h t := by
  obtain ⟨p, hroots, hconv⟩ := hG
  have hU := tendstoLocallyUniformlyOn_univ.mpr hconv
  have hD := hU.deriv (Eventually.of_forall fun m =>
    (Polynomial.differentiable (p m)).differentiableOn) isOpen_univ
  have hval : ∀ z : ℂ, Tendsto (fun m => (p m).eval z) atTop (𝓝 (G z)) := fun z =>
    hU.tendsto_at (mem_univ z)
  have hder : ∀ z : ℂ, Tendsto (fun m => (p m).derivative.eval z) atTop (𝓝 (deriv G z)) := by
    intro z
    have := hD.tendsto_at (mem_univ z)
    simp only [Function.comp_def, Polynomial.deriv] at this
    exact this
  -- the polynomial phase speeds converge
  have hω : ∀ u : ℝ, Tendsto (fun m => -(((p m).derivative.eval ((u : ℂ) + h * I)) /
      ((p m).eval ((u : ℂ) + h * I))).im) atTop (𝓝 (phaseSpeed G h u)) := by
    intro u
    have := ((hder ((u : ℂ) + h * I)).div (hval ((u : ℂ) + h * I)) (hne u))
    exact (Complex.continuous_im.tendsto _).comp this |>.neg
  -- eventually the evaluations are nonzero, and the Poisson formula applies
  have hev : ∀ u : ℝ, ∀ᶠ m in atTop, (p m).eval ((u : ℂ) + h * I) ≠ 0 := fun u =>
    (hval ((u : ℂ) + h * I)).eventually_ne (hne u)
  constructor
  · refine ge_of_tendsto (hω t) ?_
    filter_upwards [hev t] with m hm
    rw [neg_im_logDeriv_eval_eq_sum hm]
    exact rootPoissonSum_nonneg (hroots m) hh t
  · refine le_of_tendsto_of_tendsto (hω s) ((hω t).const_mul _) ?_
    filter_upwards [hev s, hev t] with m hms hmt
    rw [neg_im_logDeriv_eval_eq_sum hms, neg_im_logDeriv_eval_eq_sum hmt]
    exact rootPoissonSum_le_exp_mul (hroots m) hh s t


/-- **Continuous phase.** If `G` is entire and has no zero on the line `Im z = h`, then
`Re G(t + ih) = A(t) cos φ(t)` with `A > 0` and `φ' = −ω`, `ω` the phase speed. -/
theorem exists_phase_rep {G : ℂ → ℂ} (hG : Differentiable ℂ G) {h : ℝ}
    (hne : ∀ t : ℝ, G ((t : ℂ) + h * I) ≠ 0) :
    ∃ A φ : ℝ → ℝ, (∀ t : ℝ, 0 < A t) ∧ (∀ t : ℝ, HasDerivAt φ (-phaseSpeed G h t) t) ∧
      ∀ t : ℝ, (G ((t : ℂ) + h * I)).re = A t * Real.cos (φ t) := by
  set E : ℝ → ℂ := fun t => G ((t : ℂ) + h * I) with hE
  set q : ℝ → ℂ := fun t => deriv G ((t : ℂ) + h * I) / G ((t : ℂ) + h * I) with hq
  have hEder : ∀ t : ℝ, HasDerivAt E (deriv G ((t : ℂ) + h * I)) t := by
    intro t
    have h1 : HasDerivAt (fun z : ℂ => G (z + h * I)) (deriv G ((t : ℂ) + h * I)) (t : ℂ) :=
      ((hG ((t : ℂ) + h * I)).hasDerivAt).comp_add_const (t : ℂ) (h * I)
    exact h1.comp_ofReal
  have hdG : Continuous (deriv G) :=
    continuous_iff_continuousAt.mpr fun z => ((hG.analyticAt z).deriv).continuousAt
  have hline : Continuous (fun t : ℝ => (t : ℂ) + h * I) := by fun_prop
  have hqcont : Continuous q :=
    (hdG.comp hline).div (hG.continuous.comp hline) hne
  set L : ℝ → ℂ := fun u => ∫ x in (0 : ℝ)..u, q x with hLdef
  have hL : ∀ t : ℝ, HasDerivAt L (q t) t := fun t =>
    (hqcont.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hK : ∀ t : ℝ, E t * Complex.exp (-L t) = E 0 := by
    have hd : ∀ t : ℝ, HasDerivAt (fun t => E t * Complex.exp (-L t)) 0 t := by
      intro t
      have h1 := (hEder t).mul ((hL t).neg.cexp)
      have hEt : G ((t : ℂ) + h * I) ≠ 0 := hne t
      have e : deriv G ((t : ℂ) + h * I) * Complex.exp (-L t) + G ((t : ℂ) + h * I) *
          (Complex.exp (-L t) * -(deriv G ((t : ℂ) + h * I) / G ((t : ℂ) + h * I))) = 0 := by
        field_simp; ring
      exact h1.congr_deriv e
    have hdiff : Differentiable ℝ (fun t => E t * Complex.exp (-L t)) :=
      fun t => (hd t).differentiableAt
    intro t
    have := is_const_of_deriv_eq_zero hdiff (fun t => (hd t).deriv) t 0
    simpa [hLdef] using this
  have hE0 : E 0 ≠ 0 := hne 0
  refine ⟨fun t => ‖E 0‖ * Real.exp (L t).re, fun t => (E 0).arg + (L t).im,
    fun t => by have := norm_pos_iff.mpr hE0; positivity, fun t => ?_, fun t => ?_⟩
  · have hi : HasDerivAt (fun t => (L t).im) (q t).im t := by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hL t)
      exact this
    have hq' : (q t).im = -phaseSpeed G h t := by simp [phaseSpeed, hq]
    rw [← hq']
    exact hi.const_add _
  · have hEt : E t = E 0 * Complex.exp (L t) := by
      have := hK t
      calc E t = E t * Complex.exp (-L t) * Complex.exp (L t) := by
            rw [mul_assoc, ← Complex.exp_add]; simp
        _ = E 0 * Complex.exp (L t) := by rw [this]
    have hpolar := Complex.norm_mul_exp_arg_mul_I (E 0)
    have : E t = (‖E 0‖ : ℂ) * Complex.exp ((E 0).arg * I + L t) := by
      rw [hEt, Complex.exp_add, ← mul_assoc, hpolar]
    show (E t).re = _
    rw [this, Complex.re_ofReal_mul, Complex.exp_re]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf

/-- **Consecutive zeros enclose phase `π`.** Let `φ` be continuous with `φ(b) < φ(a)`, `a < b`.
If `cos φ(a) = cos φ(b) = 0` and `A cos φ` has no zero in `(a, b)`, then `φ(a) − φ(b) = π`. -/
theorem phase_drop_eq_pi_of_lt {A φ : ℝ → ℝ} (hφc : Continuous φ) {a b : ℝ} (hab : a < b)
    (hlt : φ b < φ a) (ha : Real.cos (φ a) = 0) (hb : Real.cos (φ b) = 0)
    (hno : ∀ c ∈ Ioo a b, A c * Real.cos (φ c) ≠ 0) :
    φ a - φ b = Real.pi := by
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp ha
  obtain ⟨k', hk'⟩ := Real.cos_eq_zero_iff.mp hb
  have hkk : k' < k := by
    rw [hk, hk'] at hlt
    have hpi := Real.pi_pos
    have : ((2 * (k' : ℝ) + 1) * Real.pi / 2) < ((2 * (k : ℝ) + 1) * Real.pi / 2) := hlt
    have : (k' : ℝ) < k := by nlinarith
    exact_mod_cast this
  by_contra hne
  have hk2 : k' ≤ k - 2 := by
    by_contra hcon
    push Not at hcon
    have : k' = k - 1 := by omega
    apply hne
    rw [hk, hk', this]; push_cast; ring
  -- the intermediate level `(2(k − 1) + 1)π/2`
  set v : ℝ := (2 * ((k - 1 : ℤ) : ℝ) + 1) * Real.pi / 2 with hv
  have hpi := Real.pi_pos
  have hv1 : φ b < v := by
    rw [hk', hv]
    have : (k' : ℝ) ≤ k - 2 := by exact_mod_cast hk2
    push_cast; nlinarith
  have hv2 : v < φ a := by rw [hk, hv]; push_cast; nlinarith
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Ioo' hab.le hφc.continuousOn ⟨hv1, hv2⟩
  apply hno c hc
  rw [hcv, hv, Real.cos_eq_zero_iff.mpr ⟨k - 1, rfl⟩, mul_zero]

/-- **Consecutive zeros enclose phase `π`.** Let `F = A cos φ` with `A > 0` and `φ` strictly
decreasing and continuous. If `F(a) = F(b) = 0`, `a < b`, and `F` has no zero in `(a, b)`, then
`φ(a) − φ(b) = π`. -/
theorem phase_drop_eq_pi {A φ : ℝ → ℝ} (hφ : StrictAnti φ)
    (hφc : Continuous φ) {a b : ℝ} (hab : a < b) (ha : Real.cos (φ a) = 0)
    (hb : Real.cos (φ b) = 0) (hno : ∀ c ∈ Ioo a b, A c * Real.cos (φ c) ≠ 0) :
    φ a - φ b = Real.pi :=
  phase_drop_eq_pi_of_lt hφc hab (hφ hab) ha hb hno

/-- **Gap rigidity from a log-Lipschitz phase speed.** Let `F = A cos φ` with `A > 0`,
`φ' = −ω`, `ω > 0`, and `ω(s) ≤ e^{2|s−t|/h} ω(t)`. Then any three consecutive zeros `a < b < c`
of `F` satisfy `c − b ≤ (b − a) e^{2(c−a)/h}` and `b − a ≤ (c − b) e^{2(c−a)/h}`. -/
theorem gap_rigidity_of_phase {A φ ω : ℝ → ℝ} {h : ℝ} (hh : 0 < h) (hA : ∀ t, 0 < A t)
    (hφ : ∀ t, HasDerivAt φ (-ω t) t) (hω : ∀ t, 0 < ω t)
    (hLL : ∀ s t, ω s ≤ Real.exp (2 * |s - t| / h) * ω t)
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (ha : A a * Real.cos (φ a) = 0) (hb : A b * Real.cos (φ b) = 0)
    (hc : A c * Real.cos (φ c) = 0)
    (hno1 : ∀ x ∈ Ioo a b, A x * Real.cos (φ x) ≠ 0)
    (hno2 : ∀ x ∈ Ioo b c, A x * Real.cos (φ x) ≠ 0) :
    c - b ≤ (b - a) * Real.exp (2 * (c - a) / h) ∧
      b - a ≤ (c - b) * Real.exp (2 * (c - a) / h) := by
  have hcos : ∀ {x}, A x * Real.cos (φ x) = 0 → Real.cos (φ x) = 0 := fun hx =>
    (mul_eq_zero.mp hx).resolve_left (hA _).ne'
  have hanti : StrictAnti φ := by
    apply strictAnti_of_deriv_neg
    intro x; rw [(hφ x).deriv]; linarith [hω x]
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have h1 := phase_drop_eq_pi hanti hφc hab (hcos ha) (hcos hb) hno1
  have h2 := phase_drop_eq_pi hanti hφc hbc (hcos hb) (hcos hc) hno2
  -- mean values
  obtain ⟨ξ₁, hξ₁, hm1⟩ := exists_hasDerivAt_eq_slope φ (fun t => -ω t) hab hφc.continuousOn
    fun x _ => hφ x
  obtain ⟨ξ₂, hξ₂, hm2⟩ := exists_hasDerivAt_eq_slope φ (fun t => -ω t) hbc hφc.continuousOn
    fun x _ => hφ x
  have hba : 0 < b - a := by linarith
  have hcb : 0 < c - b := by linarith
  have hw1 : ω ξ₁ * (b - a) = Real.pi := by
    have : -ω ξ₁ = (φ b - φ a) / (b - a) := hm1
    field_simp at this; linarith
  have hw2 : ω ξ₂ * (c - b) = Real.pi := by
    have : -ω ξ₂ = (φ c - φ b) / (c - b) := hm2
    field_simp at this; linarith
  have hdist : |ξ₂ - ξ₁| ≤ c - a := by
    rw [abs_le]; constructor <;> linarith [hξ₁.1, hξ₁.2, hξ₂.1, hξ₂.2]
  set K := Real.exp (2 * (c - a) / h) with hK
  have hE21 : Real.exp (2 * |ξ₂ - ξ₁| / h) ≤ K :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hE12 : Real.exp (2 * |ξ₁ - ξ₂| / h) ≤ K := by rw [abs_sub_comm]; exact hE21
  have hL21 : ω ξ₂ ≤ K * ω ξ₁ :=
    (hLL ξ₂ ξ₁).trans (mul_le_mul_of_nonneg_right hE21 (hω ξ₁).le)
  have hL12 : ω ξ₁ ≤ K * ω ξ₂ :=
    (hLL ξ₁ ξ₂).trans (mul_le_mul_of_nonneg_right hE12 (hω ξ₂).le)
  have hw1p := hω ξ₁
  have hw2p := hω ξ₂
  constructor
  · -- `(c − b) ω ξ₂ = (b − a) ω ξ₁ ≤ (b − a) K ω ξ₂`
    have : (c - b) * ω ξ₂ ≤ ((b - a) * K) * ω ξ₂ := by
      have := mul_le_mul_of_nonneg_left hL12 hba.le
      nlinarith
    exact le_of_mul_le_mul_right this hw2p
  · have : (b - a) * ω ξ₁ ≤ ((c - b) * K) * ω ξ₁ := by
      have := mul_le_mul_of_nonneg_left hL21 hcb.le
      nlinarith
    exact le_of_mul_le_mul_right this hw1p


/-- Far from its root, a Poisson term of any depth is log-Lipschitz: for `s, t ≥ a + c`, `c > 0`,
`poissonTerm a b s ≤ e^{2|s − t|/c} poissonTerm a b t`. -/
theorem poissonTerm_le_exp_mul_of_far {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) {s t : ℝ}
    (hs : a + c ≤ s) (ht : a + c ≤ t) :
    poissonTerm a b s ≤ Real.exp (2 * |s - t| / c) * poissonTerm a b t := by
  set d := |s - t|
  have hv : c ≤ s - a := by linarith
  have hu : c ≤ t - a := by linarith
  -- `(t − a)² ≤ e^{2d/c} (s − a)²`
  have hratio : t - a ≤ (s - a) * Real.exp (d / c) := by
    have h1 : t - a ≤ (s - a) + d := by have := le_abs_self (t - s); rw [abs_sub_comm] at this; linarith
    have h2 : (s - a) + d ≤ (s - a) * (1 + d / c) := by
      have : d ≤ (s - a) * (d / c) := by
        rw [mul_div_assoc', le_div_iff₀ hc]
        nlinarith [abs_nonneg (s - t)]
      linarith
    have h3 : 1 + d / c ≤ Real.exp (d / c) := by linarith [Real.add_one_le_exp (d / c)]
    nlinarith
  have hsq : (t - a) ^ 2 ≤ Real.exp (2 * d / c) * (s - a) ^ 2 := by
    have he : Real.exp (2 * d / c) = Real.exp (d / c) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [he]
    have h0 : 0 ≤ t - a := by linarith
    nlinarith [pow_le_pow_left₀ h0 hratio 2]
  have hb2 : b ^ 2 ≤ Real.exp (2 * d / c) * b ^ 2 := by
    have := Real.one_le_exp (show 0 ≤ 2 * d / c by positivity); nlinarith [sq_nonneg b]
  unfold poissonTerm
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Gap rigidity on a half-line.** As `gap_rigidity_of_phase`, with the log-Lipschitz bound only
on `[T₀, ∞)` and the three zeros in `[T₀, ∞)`. -/
theorem gap_rigidity_of_phase_on {A φ ω : ℝ → ℝ} {h T₀ : ℝ} (hh : 0 < h)
    (hA : ∀ t, 0 < A t) (hφ : ∀ t, HasDerivAt φ (-ω t) t) (hω : ∀ t, 0 < ω t)
    (hLL : ∀ s t, T₀ ≤ s → T₀ ≤ t → ω s ≤ Real.exp (2 * |s - t| / h) * ω t)
    {a b c : ℝ} (haT : T₀ ≤ a) (hab : a < b) (hbc : b < c)
    (ha : A a * Real.cos (φ a) = 0) (hb : A b * Real.cos (φ b) = 0)
    (hc : A c * Real.cos (φ c) = 0)
    (hno1 : ∀ x ∈ Ioo a b, A x * Real.cos (φ x) ≠ 0)
    (hno2 : ∀ x ∈ Ioo b c, A x * Real.cos (φ x) ≠ 0) :
    c - b ≤ (b - a) * Real.exp (2 * (c - a) / h) ∧
      b - a ≤ (c - b) * Real.exp (2 * (c - a) / h) := by
  have hcos : ∀ {x}, A x * Real.cos (φ x) = 0 → Real.cos (φ x) = 0 := fun hx =>
    (mul_eq_zero.mp hx).resolve_left (hA _).ne'
  have hanti : StrictAnti φ := by
    apply strictAnti_of_deriv_neg
    intro x; rw [(hφ x).deriv]; linarith [hω x]
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have h1 := phase_drop_eq_pi hanti hφc hab (hcos ha) (hcos hb) hno1
  have h2 := phase_drop_eq_pi hanti hφc hbc (hcos hb) (hcos hc) hno2
  obtain ⟨ξ₁, hξ₁, hm1⟩ := exists_hasDerivAt_eq_slope φ (fun t => -ω t) hab hφc.continuousOn
    fun x _ => hφ x
  obtain ⟨ξ₂, hξ₂, hm2⟩ := exists_hasDerivAt_eq_slope φ (fun t => -ω t) hbc hφc.continuousOn
    fun x _ => hφ x
  have hba : 0 < b - a := by linarith
  have hcb : 0 < c - b := by linarith
  have hw1 : ω ξ₁ * (b - a) = Real.pi := by
    have : -ω ξ₁ = (φ b - φ a) / (b - a) := hm1
    field_simp at this; linarith
  have hw2 : ω ξ₂ * (c - b) = Real.pi := by
    have : -ω ξ₂ = (φ c - φ b) / (c - b) := hm2
    field_simp at this; linarith
  have hdist : |ξ₂ - ξ₁| ≤ c - a := by
    rw [abs_le]; constructor <;> linarith [hξ₁.1, hξ₁.2, hξ₂.1, hξ₂.2]
  have hT1 : T₀ ≤ ξ₁ := by linarith [hξ₁.1]
  have hT2 : T₀ ≤ ξ₂ := by linarith [hξ₂.1, hξ₁.2]
  set K := Real.exp (2 * (c - a) / h) with hK
  have hE21 : Real.exp (2 * |ξ₂ - ξ₁| / h) ≤ K :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hE12 : Real.exp (2 * |ξ₁ - ξ₂| / h) ≤ K := by rw [abs_sub_comm]; exact hE21
  have hL21 : ω ξ₂ ≤ K * ω ξ₁ :=
    (hLL ξ₂ ξ₁ hT2 hT1).trans (mul_le_mul_of_nonneg_right hE21 (hω ξ₁).le)
  have hL12 : ω ξ₁ ≤ K * ω ξ₂ :=
    (hLL ξ₁ ξ₂ hT1 hT2).trans (mul_le_mul_of_nonneg_right hE12 (hω ξ₂).le)
  have hw1p := hω ξ₁
  have hw2p := hω ξ₂
  constructor
  · have : (c - b) * ω ξ₂ ≤ ((b - a) * K) * ω ξ₂ := by
      have := mul_le_mul_of_nonneg_left hL12 hba.le
      nlinarith
    exact le_of_mul_le_mul_right this hw2p
  · have : (b - a) * ω ξ₁ ≤ ((c - b) * K) * ω ξ₁ := by
      have := mul_le_mul_of_nonneg_left hL21 hcb.le
      nlinarith
    exact le_of_mul_le_mul_right this hw1p


/-- Far to the left of its root, a Poisson term of any depth is log-Lipschitz: for `s, t ≤ a − c`,
`c > 0`, `poissonTerm a b s ≤ e^{2|s − t|/c} poissonTerm a b t`. -/
theorem poissonTerm_le_exp_mul_of_far_left {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) {s t : ℝ}
    (hs : s ≤ a - c) (ht : t ≤ a - c) :
    poissonTerm a b s ≤ Real.exp (2 * |s - t| / c) * poissonTerm a b t := by
  have hsym : ∀ u, poissonTerm a b u = poissonTerm (-a) b (-u) := fun u => by
    unfold poissonTerm; ring_nf
  rw [hsym s, hsym t]
  have := poissonTerm_le_exp_mul_of_far (a := -a) hb hc (s := -s) (t := -t) (by linarith)
    (by linarith)
  rwa [show -s - -t = -(s - t) by ring, abs_neg] at this

/-- **Gap rigidity on a window.** As `gap_rigidity_of_phase`, with `ω > 0` and the log-Lipschitz
bound only on `[X, Y]`, and the three zeros in `[X, Y]`. -/
theorem gap_rigidity_of_phase_window {A φ ω : ℝ → ℝ} {h X Y : ℝ} (hh : 0 < h)
    (hA : ∀ t, 0 < A t) (hφ : ∀ t, HasDerivAt φ (-ω t) t) (hω : ∀ t ∈ Icc X Y, 0 < ω t)
    (hLL : ∀ s ∈ Icc X Y, ∀ t ∈ Icc X Y, ω s ≤ Real.exp (2 * |s - t| / h) * ω t)
    {a b c : ℝ} (haX : X ≤ a) (hcY : c ≤ Y) (hab : a < b) (hbc : b < c)
    (ha : A a * Real.cos (φ a) = 0) (hb : A b * Real.cos (φ b) = 0)
    (hc : A c * Real.cos (φ c) = 0)
    (hno1 : ∀ x ∈ Ioo a b, A x * Real.cos (φ x) ≠ 0)
    (hno2 : ∀ x ∈ Ioo b c, A x * Real.cos (φ x) ≠ 0) :
    c - b ≤ (b - a) * Real.exp (2 * (c - a) / h) ∧
      b - a ≤ (c - b) * Real.exp (2 * (c - a) / h) := by
  have hcos : ∀ {x}, A x * Real.cos (φ x) = 0 → Real.cos (φ x) = 0 := fun hx =>
    (mul_eq_zero.mp hx).resolve_left (hA _).ne'
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have hanti : StrictAntiOn φ (Icc X Y) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc X Y) hφc.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hφ x).deriv]
    linarith [hω x (Ioo_subset_Icc_self hx)]
  have hmem : ∀ x, a ≤ x → x ≤ c → x ∈ Icc X Y := fun x h1 h2 =>
    ⟨by linarith, by linarith⟩
  have hma := hmem a le_rfl (by linarith)
  have hmb := hmem b hab.le hbc.le
  have hmc := hmem c (by linarith) le_rfl
  have h1 := phase_drop_eq_pi_of_lt hφc hab (hanti hma hmb hab) (hcos ha) (hcos hb) hno1
  have h2 := phase_drop_eq_pi_of_lt hφc hbc (hanti hmb hmc hbc) (hcos hb) (hcos hc) hno2
  obtain ⟨ξ₁, hξ₁, hm1⟩ := exists_hasDerivAt_eq_slope φ (fun t => -ω t) hab hφc.continuousOn
    fun x _ => hφ x
  obtain ⟨ξ₂, hξ₂, hm2⟩ := exists_hasDerivAt_eq_slope φ (fun t => -ω t) hbc hφc.continuousOn
    fun x _ => hφ x
  have hM1 := hmem ξ₁ hξ₁.1.le (by linarith [hξ₁.2])
  have hM2 := hmem ξ₂ (by linarith [hξ₂.1]) hξ₂.2.le
  have hba : 0 < b - a := by linarith
  have hcb : 0 < c - b := by linarith
  have hw1 : ω ξ₁ * (b - a) = Real.pi := by
    have : -ω ξ₁ = (φ b - φ a) / (b - a) := hm1
    field_simp at this; linarith
  have hw2 : ω ξ₂ * (c - b) = Real.pi := by
    have : -ω ξ₂ = (φ c - φ b) / (c - b) := hm2
    field_simp at this; linarith
  have hdist : |ξ₂ - ξ₁| ≤ c - a := by
    rw [abs_le]; constructor <;> linarith [hξ₁.1, hξ₁.2, hξ₂.1, hξ₂.2]
  set K := Real.exp (2 * (c - a) / h) with hK
  have hE21 : Real.exp (2 * |ξ₂ - ξ₁| / h) ≤ K :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hE12 : Real.exp (2 * |ξ₁ - ξ₂| / h) ≤ K := by rw [abs_sub_comm]; exact hE21
  have hw1p := hω ξ₁ hM1
  have hw2p := hω ξ₂ hM2
  have hL21 : ω ξ₂ ≤ K * ω ξ₁ :=
    (hLL ξ₂ hM2 ξ₁ hM1).trans (mul_le_mul_of_nonneg_right hE21 hw1p.le)
  have hL12 : ω ξ₁ ≤ K * ω ξ₂ :=
    (hLL ξ₁ hM1 ξ₂ hM2).trans (mul_le_mul_of_nonneg_right hE12 hw2p.le)
  constructor
  · have : (c - b) * ω ξ₂ ≤ ((b - a) * K) * ω ξ₂ := by
      have := mul_le_mul_of_nonneg_left hL12 hba.le
      nlinarith
    exact le_of_mul_le_mul_right this hw2p
  · have : (b - a) * ω ξ₁ ≤ ((c - b) * K) * ω ξ₁ := by
      have := mul_le_mul_of_nonneg_left hL21 hcb.le
      nlinarith
    exact le_of_mul_le_mul_right this hw1p

end

end GaloisForLFunctions.HTGeometry
