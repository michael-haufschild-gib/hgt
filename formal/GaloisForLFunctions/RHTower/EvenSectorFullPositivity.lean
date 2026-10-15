import GaloisForLFunctions.RHTower.EvenSectorTwistedArcNull
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion
import GaloisForLFunctions.RHTower.SelbergSymbolCriticalStrip
import GaloisForLFunctions.RHTower.WeilPositivityMajorantRigidity

/-!
# Even positivity is full positivity

**Theorem** (`weilPositiveFull_of_weilPositiveEvenAt`).  If real weights `lam` make the Weil
functional (pole weight `1`) nonnegative on the autocorrelations of all even compactly supported
`C²` tests, then they make it nonnegative on the autocorrelations of all compactly supported `C²`
tests.  Hence (`weilPositiveEvenAt_one_iff`) even positivity holds exactly for `lam = Λ` under RH,
and (`riemannHypothesis_iff_primeBlindPositiveEvenAt`) RH is prime-blind positivity on the even
cone.

Proof.  Real tests suffice (`weilPositiveFull_of_real`).  For a real compactly supported `C²` test
`f` with transform `F`, `Re W(f ⋆ f̃) = L(F F^#)`
(`re_weilFullFunctional_ofReal_eq_evenWeilDensity`).
The Gaussian smoothings `F_ε(z) = F(z) e^{−εz²}` make `F_ε F_ε^# cosh²(z/2)` a multiplier, so
`L(F_ε F_ε^#) ≥ 0` (`evenWeilDensity_specSq_nonneg_of_multiplier_sechWeight`).  As `ε → 0`,
`L(F_ε F_ε^#) → L(F F^#)` (`tendsto_evenWeilDensity_gaussDamped`):
* the pole terms converge, since `F_ε F_ε^#(±i/2) = e^{ε/2} F F^#(±i/2)`;
* the archimedean terms converge by dominated convergence, with `|F(z)| ≤ N/(1 + |z|²)` on
  strips (two integrations by parts, `exists_norm_paperFT_le_of_compact`);
* the prime terms converge by dominated convergence for series.  A contour shift to
  `Im z = ±5/4` with an integrable majorant uniform in `ε ≤ 1`
  (`norm_stripInvFT_le_of_majorant`) bounds the `n`-th term by `C (1 + log n) n^{−5/4}`.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate Nat

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry

/-! ## Transforms of compactly supported tests -/

theorem norm_cexp_I_mul_le_of_abs_im_le {z : ℂ} {b : ℝ} (hz : |z.im| ≤ b) (u : ℝ) :
    ‖cexp (I * z * u)‖ ≤ Real.exp (b * |u|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (I * z * u).re = -(z.im * u) := by simp [Complex.mul_re]
  rw [hre]
  calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
    _ = |z.im| * |u| := abs_mul _ _
    _ ≤ b * |u| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)

theorem integrable_mul_cexp_of_hasCompactSupport {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (w : ℂ) : Integrable fun u : ℝ => g u * cexp (w * u) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right

/-- Integration by parts: `F_{g'}(z) = −iz F_g(z)` for every `z`. -/
theorem paperFT_deriv_of_compact {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (z : ℂ) : paperFT (deriv g) z = -(I * z) * paperFT g z := by
  have hd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => cexp (I * z * y)) (cexp (I * z * x) * (I * z))
      x := fun x => by
    have h := ((hasDerivAt_id (x : ℂ)).const_mul (I * z)).cexp.comp_ofReal
    refine h.congr_deriv ?_
    simp
  have h1 := integrable_mul_cexp_of_hasCompactSupport hg.continuous hgc (I * z)
  have h2 := integrable_mul_cexp_of_hasCompactSupport hdc hgc.deriv (I * z)
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := g)
    (v := fun y : ℝ => cexp (I * z * y)) (u' := deriv g)
    (v' := fun x => cexp (I * z * x) * (I * z)) (fun x _ => (hd x).hasDerivAt)
    (fun x _ => hv x)
    (by
      refine (h1.mul_const (I * z)).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]
      ring)
    h2 h1
  unfold paperFT
  have e : (∫ x : ℝ, g x * (cexp (I * z * x) * (I * z))) =
      (∫ x : ℝ, g x * cexp (I * z * x)) * (I * z) := by
    rw [← integral_mul_const]
    congr 1
    funext x
    ring
  rw [e] at hibp
  linear_combination hibp

theorem paperFT_deriv_deriv_of_compact {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (deriv (deriv g)) z = -(z ^ 2) * paperFT g z := by
  have h1 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) g from hg)
  rw [paperFT_deriv_of_compact h1.2.2 hgc.deriv,
    paperFT_deriv_of_compact (hg.of_le (by norm_num)) hgc]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_paperFT_le_of_compact {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {b : ℝ} {z : ℂ} (hz : |z.im| ≤ b) :
    ‖paperFT g z‖ ≤ ∫ u, ‖g u‖ * Real.exp (b * |u|) := by
  unfold paperFT
  refine norm_integral_le_of_norm_le
    ((hg.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.norm.mul_right)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_of_abs_im_le hz u) (norm_nonneg _)

/-- `|F(z)| ≤ N/(1 + |z|²)` on every horizontal strip. -/
theorem exists_norm_paperFT_le_of_compact {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (b : ℝ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ z : ℂ, |z.im| ≤ b → ‖paperFT g z‖ ≤ N / (1 + ‖z‖ ^ 2) := by
  have h1 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) g from hg)
  have h2 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv g) from h1.2.2)
  have hc2 : Continuous (deriv (deriv g)) := h2.2.2.continuous
  refine ⟨(∫ u, ‖g u‖ * Real.exp (b * |u|)) + ∫ u, ‖deriv (deriv g) u‖ * Real.exp (b * |u|),
    add_nonneg (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity),
    fun z hz => ?_⟩
  have e0 := norm_paperFT_le_of_compact hg.continuous hgc hz
  have e2 := norm_paperFT_le_of_compact hc2 hgc.deriv.deriv hz
  rw [paperFT_deriv_deriv_of_compact hg hgc, norm_mul, norm_neg, norm_pow] at e2
  rw [le_div_iff₀ (by positivity)]
  calc ‖paperFT g z‖ * (1 + ‖z‖ ^ 2) = ‖paperFT g z‖ + ‖z‖ ^ 2 * ‖paperFT g z‖ := by ring
    _ ≤ _ := add_le_add e0 e2

/-- The transform of a compactly supported continuous function is entire. -/
theorem differentiable_paperFT_of_compact {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Differentiable ℂ (paperFT g) := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  intro z
  set b := |z.im| + 1
  have hb : 0 ≤ b := by positivity
  refine differentiableAt_paperFT_of_expDecay hg (K := M * Real.exp (b * |R|)) (b := b)
    (fun u => ?_) (by simp only [b]; linarith)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  by_cases hu : u ∈ tsupport g
  · have hu' : |u| ≤ |R| := by
      have := hR hu
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact this.trans (le_abs_self R)
    have h1 : 1 ≤ Real.exp (b * |R|) * Real.exp (-(b * |u|)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]; nlinarith
    calc ‖g u‖ ≤ M := hM u
      _ ≤ M * (Real.exp (b * |R|) * Real.exp (-(b * |u|))) := le_mul_of_one_le_right hM0 h1
      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport hu, norm_zero]
    positivity

/-- For a real test, `F(−z) = conj F(z̄)`. -/
theorem paperFT_ofReal_neg_conj (f : ℝ → ℝ) (z : ℂ) :
    paperFT (fun u => (f u : ℂ)) (-z) = conj (paperFT (fun u => (f u : ℂ)) (conj z)) := by
  unfold paperFT
  rw [← integral_conj]
  congr 1
  funext u
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  ring


/-! ## Gaussian smoothing -/

/-- The Gaussian smoothing `F(z) e^{−εz²}`. -/
def gaussDamped (F : ℂ → ℂ) (ε : ℝ) (z : ℂ) : ℂ := F z * cexp (-(ε : ℂ) * z ^ 2)

theorem specSq_gaussDamped (F : ℂ → ℂ) (ε : ℝ) (z : ℂ) :
    specSq (gaussDamped F ε) z = specSq F z * cexp (-((2 * ε : ℝ) : ℂ) * z ^ 2) := by
  unfold specSq gaussDamped
  have h : conj (cexp (-(ε : ℂ) * conj z ^ 2)) = cexp (-(ε : ℂ) * z ^ 2) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [map_mul, map_neg, map_pow, Complex.conj_ofReal]
  rw [map_mul, h, show -(((2 * ε : ℝ)) : ℂ) * z ^ 2 = -(ε : ℂ) * z ^ 2 + -(ε : ℂ) * z ^ 2 by
    push_cast; ring, Complex.exp_add]
  ring

theorem gaussDamped_neg_conj {F : ℂ → ℂ} (hF : ∀ z, F (-z) = conj (F (conj z))) (ε : ℝ)
    (z : ℂ) : gaussDamped F ε (-z) = conj (gaussDamped F ε (conj z)) := by
  unfold gaussDamped
  rw [hF, map_mul, ← Complex.exp_conj]
  congr 2
  simp [map_mul, map_neg, map_pow, Complex.conj_ofReal]

theorem norm_cexp_neg_mul_sq_le {ε : ℝ} (hε : 0 < ε) {b : ℝ} {z : ℂ} (hz : |z.im| ≤ b) :
    ‖cexp (-(ε : ℂ) * z ^ 2)‖ ≤ Real.exp (ε * b ^ 2 + 1 / (4 * ε)) * Real.exp (-|z.re|) := by
  rw [Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
  have hre : (-(ε : ℂ) * z ^ 2).re = -(ε * (z.re ^ 2 - z.im ^ 2)) := by
    simp [sq, Complex.mul_re]
  rw [hre]
  have h1 : z.im ^ 2 ≤ b ^ 2 := by
    have := sq_abs z.im
    nlinarith [abs_nonneg z.im]
  have h3 : z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
  have key : 0 ≤ ε * |z.re| ^ 2 - |z.re| + 1 / (4 * ε) := by
    have e : ε * |z.re| ^ 2 - |z.re| + 1 / (4 * ε) = (2 * ε * |z.re| - 1) ^ 2 / (4 * ε) := by
      field_simp; ring
    rw [e]; positivity
  nlinarith

theorem stripDecay_gaussDamped {F : ℂ → ℂ} (hFd : Differentiable ℂ F) {N : ℝ} (hN : 0 ≤ N)
    (hFb : ∀ z : ℂ, |z.im| ≤ 9 / 4 → ‖F z‖ ≤ N) {ε : ℝ} (hε : 0 < ε) :
    StripDecay (gaussDamped F ε) (9 / 4) 1
      (N * Real.exp (ε * (9 / 4) ^ 2 + 1 / (4 * ε))) := by
  refine ⟨fun z _ => (hFd z).mul (by fun_prop), fun z hz => ?_⟩
  unfold gaussDamped
  rw [norm_mul, one_mul]
  calc ‖F z‖ * ‖cexp (-(ε : ℂ) * z ^ 2)‖ ≤
      N * (Real.exp (ε * (9 / 4) ^ 2 + 1 / (4 * ε)) * Real.exp (-|z.re|)) :=
        mul_le_mul (hFb z hz) (norm_cexp_neg_mul_sq_le hε hz) (norm_nonneg _) hN
    _ = _ := by ring


/-! ## A contour bound with an integrable majorant -/

/-- If `|Φ| ≤ g` on the two lines `Im z = ±b`, then `|F̌Φ(x)| ≤ (∫ g)/(2π) e^{−b|x|}`. -/
theorem norm_stripInvFT_le_of_majorant {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) {g : ℝ → ℝ} (hg : Integrable g)
    (hgb : ∀ r : ℝ, ‖Φ ((r : ℂ) + (b : ℂ) * I)‖ ≤ g r ∧
      ‖Φ ((r : ℂ) + ((-b : ℝ) : ℂ) * I)‖ ≤ g r) (x : ℝ) :
    ‖stripInvFT Φ x‖ ≤ (∫ r, g r) / (2 * Real.pi) * Real.exp (-(b * |x|)) := by
  have hC := hΦ.const_nonneg hb
  set G : ℂ → ℂ := fun z => Φ z * cexp (-(I * z * x)) with hGdef
  have hGd : ∀ z : ℂ, |z.im| ≤ b → DifferentiableAt ℂ G z := fun z hz =>
    (hΦ.diff z hz).mul (by fun_prop)
  have hGb : ∀ z : ℂ, |z.im| ≤ b →
      ‖G z‖ ≤ (C * Real.exp (b * |x|)) * Real.exp (-(ε * |z.re|)) := by
    intro z hz
    rw [hGdef]
    simp only
    rw [norm_mul, norm_cexp_neg_I_mul]
    have h1 : Real.exp (z.im * x) ≤ Real.exp (b * |x|) := by
      apply Real.exp_le_exp.mpr
      calc z.im * x ≤ |z.im * x| := le_abs_self _
        _ = |z.im| * |x| := abs_mul _ _
        _ ≤ b * |x| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
    calc ‖Φ z‖ * Real.exp (z.im * x) ≤ (C * Real.exp (-(ε * |z.re|))) * Real.exp (b * |x|) :=
          mul_le_mul (hΦ.bound z hz) h1 (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hline : ∀ y : ℝ, (∀ r : ℝ, ‖Φ ((r : ℂ) + (y : ℂ) * I)‖ ≤ g r) →
      ∀ r : ℝ, ‖G ((r : ℂ) + (y : ℂ) * I)‖ ≤ g r * Real.exp (y * x) := by
    intro y hy r
    rw [hGdef]
    simp only
    rw [norm_mul, norm_cexp_neg_I_mul]
    have him : ((r : ℂ) + (y : ℂ) * I).im = y := by simp
    rw [him]
    exact mul_le_mul_of_nonneg_right (hy r) (Real.exp_pos _).le
  have hnorm : ∀ y : ℝ, (∀ r : ℝ, ‖Φ ((r : ℂ) + (y : ℂ) * I)‖ ≤ g r) →
      y * x = -(b * |x|) →
      ‖∫ r : ℝ, G ((r : ℂ) + (y : ℂ) * I)‖ ≤ (∫ r, g r) * Real.exp (-(b * |x|)) := by
    intro y hy hyx
    refine (norm_integral_le_of_norm_le (hg.mul_const (Real.exp (y * x)))
      (Eventually.of_forall (hline y hy))).trans (le_of_eq ?_)
    rw [integral_mul_const, hyx]
  have hval : ‖∫ r : ℝ, Φ r * cexp (-(I * r * x))‖ ≤
      (∫ r, g r) * Real.exp (-(b * |x|)) := by
    rcases le_total 0 x with hx | hx
    · have hs := integral_horizontal_shift_lower hb hε hGd hGb
      have e : (∫ r : ℝ, Φ r * cexp (-(I * r * x))) =
          ∫ r : ℝ, G ((r : ℂ) + ((-b : ℝ) : ℂ) * I) := by
        rw [← hs]
        refine integral_congr_ae (Eventually.of_forall fun r => ?_)
        simp only [hGdef]
        push_cast
        ring_nf
      rw [e]
      exact hnorm (-b) (fun r => (hgb r).2) (by rw [abs_of_nonneg hx]; ring)
    · have hs := RHTower.integral_horizontal_shift_of_decay hb hε hGd hGb
      have e : (∫ r : ℝ, Φ r * cexp (-(I * r * x))) = ∫ r : ℝ, G ((r : ℂ) + (b : ℂ) * I) := by
        rw [hs]
      rw [e]
      exact hnorm b (fun r => (hgb r).1) (by rw [abs_of_nonpos hx]; ring)
  unfold stripInvFT
  rw [norm_mul]
  have h2 : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h2]
  calc 1 / (2 * Real.pi) * ‖∫ r : ℝ, Φ r * cexp (-(I * r * x))‖ ≤
      1 / (2 * Real.pi) * ((∫ r, g r) * Real.exp (-(b * |x|))) :=
        mul_le_mul_of_nonneg_left hval (by positivity)
    _ = _ := by ring


/-! ## The smoothed functionals and their limit -/

theorem contDiff_ofReal_comp {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 fun u => (f u : ℂ) :=
  Complex.ofRealCLM.contDiff.comp hf

theorem norm_le_of_norm_le_div_one_add_sq {F : ℂ → ℂ} {N b : ℝ} (hN : 0 ≤ N)
    (hb : ∀ z : ℂ, |z.im| ≤ b → ‖F z‖ ≤ N / (1 + ‖z‖ ^ 2)) {z : ℂ} (hz : |z.im| ≤ b) :
    ‖F z‖ ≤ N * (1 + z.re ^ 2)⁻¹ := by
  refine (hb z hz).trans ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ hN
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  have := Complex.abs_re_le_norm z
  have h2 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  linarith

theorem multiplier_sechWeight_gaussDamped {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    Multiplier (sechWeight (gaussDamped (paperFT fun u => (f u : ℂ)) ε)) := by
  have hcc : HasCompactSupport fun u => (f u : ℂ) := hfc.comp_left Complex.ofReal_zero
  obtain ⟨N, hN, hb⟩ := exists_norm_paperFT_le_of_compact (contDiff_ofReal_comp hf) hcc (9 / 4)
  have hFb : ∀ z : ℂ, |z.im| ≤ 9 / 4 → ‖paperFT (fun u => (f u : ℂ)) z‖ ≤ N := fun z hz =>
    (hb z hz).trans (div_le_self hN (by nlinarith [sq_nonneg ‖z‖]))
  exact multiplier_sechWeight (by norm_num : (1 / 2 : ℝ) < 1)
    (stripDecay_gaussDamped (differentiable_paperFT_of_compact
      (contDiff_ofReal_comp hf).continuous hcc) hN hFb hε)
    (specSq_neg_of_neg_conj (gaussDamped_neg_conj (paperFT_ofReal_neg_conj f) ε))

theorem norm_cexp_neg_mul_sq_le_of_im {c b : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : |z.im| ≤ b) :
    ‖cexp (-(c : ℂ) * z ^ 2)‖ ≤ Real.exp (c * b ^ 2) := by
  rw [Complex.norm_exp, Real.exp_le_exp]
  have hre : (-(c : ℂ) * z ^ 2).re = -(c * (z.re ^ 2 - z.im ^ 2)) := by
    simp [sq, Complex.mul_re]
  rw [hre]
  have h1 : z.im ^ 2 ≤ b ^ 2 := by
    have := sq_abs z.im
    nlinarith [abs_nonneg z.im]
  nlinarith [sq_nonneg z.re, mul_nonneg hc (sq_nonneg z.re)]

theorem cexp_neg_mul_sq_ofReal (c r : ℝ) :
    cexp (-(c : ℂ) * (r : ℂ) ^ 2) = ((Real.exp (-(c * r ^ 2)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]; push_cast; ring_nf

theorem inv_one_add_sq_sq_le (r : ℝ) : ((1 + r ^ 2)⁻¹) ^ 2 ≤ (1 + r ^ 2)⁻¹ := by
  have h0 : 0 ≤ (1 + r ^ 2)⁻¹ := by positivity
  have h1 : (1 + r ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg r])
  nlinarith

theorem one_add_abs_mul_inv_sq_le (r : ℝ) :
    (1 + |r|) * ((1 + r ^ 2)⁻¹) ^ 2 ≤ 2 * (1 + r ^ 2)⁻¹ := by
  have hp : 0 < 1 + r ^ 2 := by positivity
  have h1 : 1 + |r| ≤ 2 * (1 + r ^ 2) := by nlinarith [abs_nonneg r, sq_abs r, sq_nonneg (|r| - 1)]
  rw [sq, ← mul_assoc]
  calc (1 + |r|) * (1 + r ^ 2)⁻¹ * (1 + r ^ 2)⁻¹ ≤ 2 * (1 + r ^ 2) * (1 + r ^ 2)⁻¹ *
        (1 + r ^ 2)⁻¹ := by gcongr
    _ = 2 * (1 + r ^ 2)⁻¹ := by rw [mul_assoc 2, mul_inv_cancel₀ hp.ne', mul_one]

/-- **The smoothed functionals converge.** -/
theorem tendsto_evenWeilDensity_gaussDamped {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun k : ℕ => evenWeilDensity lam
      (specSq (gaussDamped (paperFT fun u => (f u : ℂ)) (1 / ((k : ℝ) + 1)))))
      atTop (𝓝 (evenWeilDensity lam (specSq (paperFT fun u => (f u : ℂ))))) := by
  set fc : ℝ → ℂ := fun u => (f u : ℂ) with hfcdef
  have hcc : HasCompactSupport fc := hfc.comp_left Complex.ofReal_zero
  set F := paperFT fc with hFdef
  have hFd : Differentiable ℂ F :=
    differentiable_paperFT_of_compact (contDiff_ofReal_comp hf).continuous hcc
  obtain ⟨N, hN, hNb⟩ := exists_norm_paperFT_le_of_compact (contDiff_ofReal_comp hf) hcc (9 / 4)
  have hFr : ∀ z : ℂ, |z.im| ≤ 9 / 4 → ‖F z‖ ≤ N * (1 + z.re ^ 2)⁻¹ := fun z hz =>
    norm_le_of_norm_le_div_one_add_sq hN hNb hz
  have hFsym := paperFT_ofReal_neg_conj f
  set K₀ := specSq F with hK₀
  set εk : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεk
  have hεpos : ∀ k, 0 < εk k := fun k => by simp only [hεk]; positivity
  have hεle : ∀ k, εk k ≤ 1 := fun k => by
    simp only [hεk]
    rw [div_le_one (by positivity)]
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have hεt : Tendsto εk atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hK : ∀ k, specSq (gaussDamped F (εk k)) =
      fun z => K₀ z * cexp (-((2 * εk k : ℝ) : ℂ) * z ^ 2) := fun k =>
    funext (specSq_gaussDamped F (εk k))
  -- bounds
  have hK₀n : ∀ z : ℂ, |z.im| ≤ 9 / 4 → ‖K₀ z‖ ≤ N ^ 2 * ((1 + z.re ^ 2)⁻¹) ^ 2 :=
    fun z hz => by
      simp only [hK₀, specSq]
      rw [norm_mul, Complex.norm_conj]
      have h2 := hFr (conj z) (by simpa using hz)
      rw [Complex.conj_re] at h2
      calc ‖F z‖ * ‖F (conj z)‖ ≤ (N * (1 + z.re ^ 2)⁻¹) * (N * (1 + z.re ^ 2)⁻¹) :=
            mul_le_mul (hFr z hz) h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring
  have hK₀c : Continuous fun r : ℝ => K₀ r := by
    simp only [hK₀, specSq, Complex.conj_ofReal]
    exact (hFd.continuous.comp continuous_ofReal).mul
      (continuous_conj.comp (hFd.continuous.comp continuous_ofReal))
  have hK₀r : ∀ r : ℝ, ‖K₀ r‖ ≤ N ^ 2 * ((1 + r ^ 2)⁻¹) ^ 2 := fun r => by
    have h := hK₀n r (by norm_num)
    simpa using h
  have hK₀i : Integrable fun r : ℝ => ‖K₀ r‖ :=
    (integrable_inv_one_add_sq.const_mul (N ^ 2)).mono' hK₀c.norm.aestronglyMeasurable
      (Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_norm]
        exact (hK₀r r).trans (mul_le_mul_of_nonneg_left (inv_one_add_sq_sq_le r)
          (sq_nonneg _)))
  -- the three parts
  show Tendsto (fun k : ℕ => evenWeilDensity lam (specSq (gaussDamped F (εk k)))) atTop _
  simp_rw [hK, evenWeilDensity_eq_parts]
  refine Tendsto.sub (Tendsto.add ?_ (Tendsto.const_mul _ ?_)) ?_
  · -- pole part
    set P : ℝ → ℝ := fun ε => (K₀ (I / 2) * cexp (-((2 * ε : ℝ) : ℂ) * (I / 2) ^ 2) +
      K₀ (-I / 2) * cexp (-((2 * ε : ℝ) : ℂ) * (-I / 2) ^ 2)).re with hP
    have hPc : Continuous P := by simp only [hP]; fun_prop
    have hP0 : P 0 = evenPolePart K₀ := by simp [hP, evenPolePart]
    rw [← hP0]
    exact (hPc.tendsto 0).comp hεt
  · -- archimedean part
    unfold evenArchPart
    refine tendsto_integral_of_dominated_convergence (fun r => ‖K₀ r‖ * |EF.gammaBracket r|)
      (fun k => ?_) ?_ (fun k => Eventually.of_forall fun r => ?_)
      (Eventually.of_forall fun r => ?_)
    · exact ((Complex.continuous_re.comp (hK₀c.mul (by fun_prop))).mul
        WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
    · refine (integrable_inv_one_add_sq.const_mul (N ^ 2 * ((|gammaLogConst| + 2) * 2))).mono'
        (hK₀c.norm.mul
          (continuous_abs.comp WeilHerglotz.continuous_gammaBracket)).aestronglyMeasurable
        (Eventually.of_forall fun r => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_norm, abs_abs]
      have h1 := hK₀r r
      have h2 := abs_abs_gammaBracket_le_linear r
      rw [abs_abs] at h2
      have h3 := one_add_abs_mul_inv_sq_le r
      have hM : 0 ≤ |gammaLogConst| + 2 := by positivity
      calc ‖K₀ r‖ * |EF.gammaBracket r| ≤ (N ^ 2 * ((1 + r ^ 2)⁻¹) ^ 2) *
            ((|gammaLogConst| + 2) * (1 + |r|)) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = N ^ 2 * (|gammaLogConst| + 2) * ((1 + |r|) * ((1 + r ^ 2)⁻¹) ^ 2) := by ring
        _ ≤ N ^ 2 * (|gammaLogConst| + 2) * (2 * (1 + r ^ 2)⁻¹) := by gcongr
        _ = _ := by ring
    · beta_reduce
      rw [cexp_neg_mul_sq_ofReal, Complex.re_mul_ofReal, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      have h1 : Real.exp (-(2 * εk k * r ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have := hεpos k; nlinarith [sq_nonneg r])
      have h2 := Complex.abs_re_le_norm (K₀ r)
      calc |(K₀ r).re| * Real.exp (-(2 * εk k * r ^ 2)) * |EF.gammaBracket r|
          ≤ ‖K₀ r‖ * 1 * |EF.gammaBracket r| := by gcongr
        _ = _ := by ring
    · have hc : Tendsto (fun k => Real.exp (-(2 * εk k * r ^ 2))) atTop (𝓝 1) := by
        have h0 : Tendsto (fun k => -(2 * εk k * r ^ 2)) atTop (𝓝 0) := by
          have := ((hεt.const_mul 2).mul_const (r ^ 2)).neg
          rwa [mul_zero, zero_mul, neg_zero] at this
        rw [← Real.exp_zero]
        exact (Real.continuous_exp.tendsto 0).comp h0
      have := (hc.const_mul (K₀ r).re).mul_const (EF.gammaBracket r)
      simp only [mul_one] at this
      refine this.congr fun k => ?_
      beta_reduce
      rw [cexp_neg_mul_sq_ofReal, Complex.re_mul_ofReal]
  · -- prime part
    unfold evenPrimePart
    set g : ℝ → ℝ := fun r => N ^ 2 * Real.exp (25 / 8) * ((1 + r ^ 2)⁻¹) ^ 2 with hgdef
    have hgi : Integrable g :=
      (integrable_inv_one_add_sq.const_mul (N ^ 2 * Real.exp (25 / 8))).mono'
        ((continuous_const.mul (((by fun_prop : Continuous fun r : ℝ => 1 + r ^ 2).inv₀
          fun r => by positivity).pow 2)).aestronglyMeasurable)
        (Eventually.of_forall fun r => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (inv_one_add_sq_sq_le r) (by positivity))
    have hCg := growthConst_nonneg hg
    set D := Cg * (2 * ((∫ r, g r) / (2 * Real.pi))) with hD
    have hgD : 0 ≤ ∫ r, g r := integral_nonneg fun r => by simp only [hgdef]; positivity
    have hD0 : 0 ≤ D := by positivity
    refine tendsto_tsum_of_dominated_convergence (bound := fun n : ℕ =>
      D * ((1 + Real.log n) * (n : ℝ) ^ (-(5 / 4 : ℝ))))
      ((summable_one_add_log_mul_rpow (b₁ := 5 / 4) (by norm_num)).mul_left D)
      (fun n => ?_) (Eventually.of_forall fun k n => ?_)
    · -- termwise convergence
      refine Tendsto.const_mul _ (Tendsto.const_mul _ ?_)
      refine tendsto_integral_of_dominated_convergence (fun r => ‖K₀ r‖) (fun k => ?_) hK₀i
        (fun k => Eventually.of_forall fun r => ?_) (Eventually.of_forall fun r => ?_)
      · exact ((Complex.continuous_re.comp (hK₀c.mul (by fun_prop))).mul
          (by fun_prop)).aestronglyMeasurable
      · beta_reduce
        rw [cexp_neg_mul_sq_ofReal, Complex.re_mul_ofReal, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_pos (Real.exp_pos _)]
        have h1 : Real.exp (-(2 * εk k * r ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
          have := hεpos k; nlinarith [sq_nonneg r])
        have h2 := Complex.abs_re_le_norm (K₀ r)
        have h3 := Real.abs_cos_le_one (r * Real.log n)
        calc |(K₀ r).re| * Real.exp (-(2 * εk k * r ^ 2)) * |Real.cos (r * Real.log n)|
            ≤ ‖K₀ r‖ * 1 * 1 := by gcongr
          _ = _ := by ring
      · have hc : Tendsto (fun k => Real.exp (-(2 * εk k * r ^ 2))) atTop (𝓝 1) := by
          have h0 : Tendsto (fun k => -(2 * εk k * r ^ 2)) atTop (𝓝 0) := by
            have := ((hεt.const_mul 2).mul_const (r ^ 2)).neg
            rwa [mul_zero, zero_mul, neg_zero] at this
          rw [← Real.exp_zero]
          exact (Real.continuous_exp.tendsto 0).comp h0
        have := (hc.const_mul (K₀ r).re).mul_const (Real.cos (r * Real.log n))
        simp only [mul_one] at this
        refine this.congr fun k => ?_
        beta_reduce
        rw [cexp_neg_mul_sq_ofReal, Complex.re_mul_ofReal]
    · -- the uniform bound
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      have hsd : StripDecay (gaussDamped F (εk k)) (5 / 4) 1
          (N * Real.exp (εk k * (9 / 4) ^ 2 + 1 / (4 * εk k))) := by
        have h9 := stripDecay_gaussDamped hFd hN (fun z hz => (hFr z hz).trans
          (mul_le_of_le_one_right hN (inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg z.re]))))
          (hεpos k)
        exact ⟨fun z hz => h9.diff z (by linarith), fun z hz => h9.bound z (by linarith)⟩
      have hgood := goodDensity_specSq_of_neg_conj one_pos hsd (gaussDamped_neg_conj hFsym _)
      have hsK : StripDecay (specSq (gaussDamped F (εk k))) (5 / 4) (2 * 1)
          ((N * Real.exp (εk k * (9 / 4) ^ 2 + 1 / (4 * εk k))) ^ 2) :=
        ⟨fun z hz => differentiableAt_specSq hsd hz, fun z hz => norm_specSq_le hsd hz⟩
      have hmaj : ∀ r : ℝ,
          ‖specSq (gaussDamped F (εk k)) ((r : ℂ) + ((5 / 4 : ℝ) : ℂ) * I)‖ ≤ g r ∧
          ‖specSq (gaussDamped F (εk k)) ((r : ℂ) + ((-(5 / 4) : ℝ) : ℂ) * I)‖ ≤ g r := by
        intro r
        have hw : ∀ w : ℂ, |w.im| ≤ 5 / 4 → w.re = r →
            ‖specSq (gaussDamped F (εk k)) w‖ ≤ g r := by
          intro w hw hre
          rw [specSq_gaussDamped, norm_mul]
          have h1 := hK₀n w (by linarith)
          rw [hre] at h1
          have h2 := norm_cexp_neg_mul_sq_le_of_im (c := 2 * εk k) (by
            have := hεpos k; positivity) hw
          have h3 : Real.exp (2 * εk k * (5 / 4) ^ 2) ≤ Real.exp (25 / 8) :=
            Real.exp_le_exp.mpr (by have := hεle k; nlinarith)
          simp only [hgdef]
          calc ‖K₀ w‖ * ‖cexp (-((2 * εk k : ℝ) : ℂ) * w ^ 2)‖ ≤
              (N ^ 2 * ((1 + r ^ 2)⁻¹) ^ 2) * Real.exp (25 / 8) :=
                mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by positivity)
            _ = _ := by ring
        exact ⟨hw _ (by simp [abs_of_pos]) (by simp), hw _ (by simp [abs_of_pos]) (by simp)⟩
      have hinv := norm_stripInvFT_le_of_majorant (by norm_num) (by norm_num) hsK hgi hmaj
        (Real.log n)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hexp : Real.exp (-(5 / 4 * |Real.log n|)) = (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
        rw [abs_of_nonneg (Real.log_natCast_nonneg n), Real.rpow_def_of_pos hn0]; ring_nf
      rw [hexp] at hinv
      have hX : |1 / Real.pi * ∫ r : ℝ, (specSq (gaussDamped F (εk k)) r).re *
          Real.cos (r * Real.log n)| ≤
          2 * ((∫ r, g r) / (2 * Real.pi)) * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
        rw [hgood.integral_cos_eq, abs_mul, abs_two]
        have := (Complex.abs_re_le_norm _).trans hinv
        nlinarith
      rw [← hK k, Real.norm_eq_abs, abs_mul]
      calc |(if 2 ≤ n then lam n / Real.sqrt n else 0)| *
            |1 / Real.pi * ∫ r : ℝ, (specSq (gaussDamped F (εk k)) r).re *
              Real.cos (r * Real.log n)|
          ≤ (Cg * (1 + Real.log n)) *
            (2 * ((∫ r, g r) / (2 * Real.pi)) * (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
            mul_le_mul (abs_weight_le hg n) hX (abs_nonneg _)
              (by have := Real.log_natCast_nonneg n; positivity)
        _ = _ := by simp only [hD]; ring


/-! ## The Weil functional of a compactly supported real test -/

/-- `Re W(f ⋆ f̃) = L(F F^#)` for a real compactly supported `C²` test. -/
theorem re_weilFullFunctional_ofReal_eq_evenWeilDensity (lam : ℕ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      evenWeilDensity lam (specSq (paperFT fun u => (f u : ℂ))) := by
  set fc : ℝ → ℂ := fun u => (f u : ℂ) with hfcdef
  have hfc2 := contDiff_ofReal_comp hf
  have hcc : HasCompactSupport fc := hfc.comp_left Complex.ofReal_zero
  set F := paperFT fc with hFdef
  set k := EF.weilTest fc fc with hkdef
  have hk : ∀ z, paperFT k z = specSq F z := fun z =>
    EF.paperFT_weilTest hfc2.continuous hfc2.continuous hcc hcc z
  have hk' : paperFT (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) = specSq F :=
    funext hk
  obtain ⟨R, hR⟩ := hcc.isCompact.isBounded.subset_closedBall 0
  have hRs : tsupport fc ⊆ Icc (-|R|) |R| := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.mp (this.trans (le_abs_self R))
  obtain ⟨-, hkd, -, hki, hFk⟩ := weilTest_self_data hfc2 hRs
  obtain ⟨N, hN, hNb⟩ := exists_norm_paperFT_le_of_compact hfc2 hcc (9 / 4)
  have hFd : Differentiable ℂ F := differentiable_paperFT_of_compact hfc2.continuous hcc
  have hKc : Continuous fun r : ℝ => specSq F r := by
    simp only [specSq, Complex.conj_ofReal]
    exact (hFd.continuous.comp continuous_ofReal).mul
      (continuous_conj.comp (hFd.continuous.comp continuous_ofReal))
  have hKr : ∀ r : ℝ, ‖specSq F r‖ ≤ N ^ 2 * ((1 + r ^ 2)⁻¹) ^ 2 := fun r => by
    have h1 := norm_le_of_norm_le_div_one_add_sq hN hNb (z := (r : ℂ)) (by norm_num)
    simp only [Complex.ofReal_re] at h1
    unfold specSq
    rw [norm_mul, Complex.norm_conj, Complex.conj_ofReal]
    calc ‖F r‖ * ‖F r‖ ≤ (N * (1 + r ^ 2)⁻¹) * (N * (1 + r ^ 2)⁻¹) :=
          mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hKi : Integrable fun r : ℝ => ‖specSq F r‖ :=
    (integrable_inv_one_add_sq.const_mul (N ^ 2)).mono' hKc.norm.aestronglyMeasurable
      (Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_norm]
        exact (hKr r).trans (mul_le_mul_of_nonneg_left (inv_one_add_sq_sq_le r)
          (sq_nonneg _)))
  have hgi : Integrable fun r : ℝ => specSq F r * (EF.gammaBracket r : ℂ) := by
    refine (integrable_inv_one_add_sq.const_mul (N ^ 2 * ((|gammaLogConst| + 2) * 2))).mono'
      (hKc.mul (Complex.continuous_ofReal.comp
        WeilHerglotz.continuous_gammaBracket)).aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := abs_abs_gammaBracket_le_linear r
    rw [abs_abs] at h2
    have h3 := one_add_abs_mul_inv_sq_le r
    calc ‖specSq F r‖ * |EF.gammaBracket r| ≤ (N ^ 2 * ((1 + r ^ 2)⁻¹) ^ 2) *
          ((|gammaLogConst| + 2) * (1 + |r|)) :=
          mul_le_mul (hKr r) h2 (abs_nonneg _) (by positivity)
      _ = N ^ 2 * (|gammaLogConst| + 2) * ((1 + |r|) * ((1 + r ^ 2)⁻¹) ^ 2) := by ring
      _ ≤ N ^ 2 * (|gammaLogConst| + 2) * (2 * (1 + r ^ 2)⁻¹) := by gcongr
      _ = _ := by ring
  rw [re_weilFullFunctional_ofReal]
  unfold weilArchRe evenWeilDensity
  congr 1
  · rw [hk']
    have h1 := integral_re hgi
    simp only [RCLike.re_to_complex] at h1
    rw [Complex.add_re, show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by
      push_cast; ring, Complex.re_ofReal_mul, ← h1]
    congr 2
    exact integral_congr_ae (Eventually.of_forall fun r => by
      simp only [Complex.re_mul_ofReal])
  · unfold atomPairing
    refine tsum_congr fun n => ?_
    congr 1
    have hinv := EF.k_add_k_neg hkd.continuous hki hFk (Real.log n)
    rw [hk', weilTest_ofReal_eq, weilTest_ofReal_eq] at hinv
    have hci : Integrable fun τ : ℝ => specSq F τ * (Real.cos (τ * Real.log n) : ℂ) := by
      refine hKi.mono' (hKc.mul (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun τ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := Real.abs_cos_le_one (τ * Real.log n)
      have := norm_nonneg (specSq F τ)
      nlinarith
    have h1 := congrArg Complex.re hinv
    rw [Complex.add_re, Complex.ofReal_re, Complex.ofReal_re,
      show (1 / Real.pi : ℂ) = ((1 / Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul] at h1
    have h2 := integral_re hci
    simp only [RCLike.re_to_complex] at h2
    rw [← h2] at h1
    unfold crossCorr
    rw [h1]
    congr 2
    funext τ
    rw [Complex.re_mul_ofReal]


/-! ## Even positivity is full positivity -/

theorem re_weilFullFunctional_nonneg_of_weilPositiveEvenAt {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt 1 lam) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    0 ≤ (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  obtain ⟨Cg, -, hg⟩ := exists_abs_le_of_weilPositiveEvenAt h
  rw [re_weilFullFunctional_ofReal_eq_evenWeilDensity lam hf hfc]
  refine ge_of_tendsto (tendsto_evenWeilDensity_gaussDamped hg hf hfc)
    (Eventually.of_forall fun k => ?_)
  exact evenWeilDensity_specSq_nonneg_of_multiplier_sechWeight h
    (multiplier_sechWeight_gaussDamped hf hfc (by positivity))

/-- **Even positivity is full positivity.** -/
theorem weilPositiveFull_of_weilPositiveEvenAt {lam : ℕ → ℝ} (h : WeilPositiveEvenAt 1 lam) :
    WeilPositiveFull lam :=
  weilPositiveFull_of_real fun _ hg hgc =>
    re_weilFullFunctional_nonneg_of_weilPositiveEvenAt h hg hgc

theorem weilPositiveEvenAt_of_weilPositiveFull {lam : ℕ → ℝ} (h : WeilPositiveFull lam) :
    WeilPositiveEvenAt 1 lam := fun f hf hfc _ => by
  rw [weilPoleWeightFunctional_one]; exact h f hf hfc

/-- **The even Weil cone is `{Λ}` under RH and empty otherwise.** -/
theorem weilPositiveEvenAt_one_iff {lam : ℕ → ℝ} :
    WeilPositiveEvenAt 1 lam ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  ⟨fun h => weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp
      (weilPositiveFull_of_weilPositiveEvenAt h),
    fun h => weilPositiveEvenAt_of_weilPositiveFull
      (weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mpr h)⟩

/-- **RH is prime-blind positivity on the even cone.** -/
theorem riemannHypothesis_iff_primeBlindPositiveEvenAt :
    RiemannHypothesis ↔ PrimeBlindPositiveEvenAt 1 :=
  ⟨fun hRH => primeBlindPositiveEvenAt_of_riemannHypothesis hRH le_rfl, fun hP => by
    obtain ⟨lam, h⟩ := (exists_weilPositiveEvenAt_iff 1).mpr hP
    exact (weilPositiveEvenAt_one_iff.mp h).1⟩

end RHTower.EvenSector

end
