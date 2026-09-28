import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Oscillatory packets on a horizontal line

Riemann–Lebesgue along the positive frequency ray, and the high-frequency limits of the evaluations
`E_u(b) = ∫ e^{-i(u + iv)x} b(x) dx` of the packets `φ(x) cos(ux)` and `φ(x) sin(ux)`:
`E_u(φ cos(u·)) → ½ ∫ e^{vx} φ`, `E_u(φ sin(u·)) → -(i/2) ∫ e^{vx} φ`, while a fixed profile has
`E_u(φ) → 0`. One complex equation `α a + β b = w` in two real unknowns is solved explicitly, with a
uniform bound near a nondegenerate limit pair. Packet derivatives grow at most like `(1 + |u|)^n`.
-/

open Complex Filter Topology MeasureTheory
open scoped ComplexConjugate ContDiff

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Riemann–Lebesgue along the positive frequency ray -/

/-- `∫ e^{-iux} f(x) dx → 0` as `u → +∞`. -/
theorem tendsto_integral_cexp_neg_mul_I (f : ℝ → ℂ) :
    Tendsto (fun u : ℝ => ∫ x : ℝ, cexp (-((u : ℂ) * (x : ℂ) * I)) * f x) atTop (𝓝 0) := by
  have h := (Real.tendsto_integral_exp_smul_cocompact f).comp
    ((tendsto_id.atTop_div_const (by positivity : (0 : ℝ) < 2 * Real.pi)).mono_right
      atTop_le_cocompact)
  refine h.congr fun u => ?_
  simp only [Function.comp_apply, id]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 1
  congr 1
  push_cast
  field_simp

/-- `∫ e^{iux} f(x) dx → 0` as `u → +∞`. -/
theorem tendsto_integral_cexp_mul_I (f : ℝ → ℂ) :
    Tendsto (fun u : ℝ => ∫ x : ℝ, cexp ((u : ℂ) * (x : ℂ) * I) * f x) atTop (𝓝 0) := by
  have h := tendsto_integral_cexp_neg_mul_I (fun x => f (-x))
  refine h.congr fun u => ?_
  rw [← integral_neg_eq_self (fun x : ℝ => cexp ((u : ℂ) * (x : ℂ) * I) * f x)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ofReal_neg]
  ring_nf

theorem cexp_neg_mul_I_add_cexp_mul_I (θ : ℝ) :
    cexp (-((θ : ℂ) * I)) + cexp ((θ : ℂ) * I) = ((2 * Real.cos θ : ℝ) : ℂ) := by
  rw [← Complex.cos_add_sin_I, show -((θ : ℂ) * I) = (-(θ : ℂ)) * I by ring,
    ← Complex.cos_add_sin_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  push_cast; ring

theorem cexp_mul_I_sub_cexp_neg_mul_I (θ : ℝ) :
    cexp ((θ : ℂ) * I) - cexp (-((θ : ℂ) * I)) = ((2 * Real.sin θ : ℝ) : ℂ) * I := by
  rw [← Complex.cos_add_sin_I, show -((θ : ℂ) * I) = (-(θ : ℂ)) * I by ring,
    ← Complex.cos_add_sin_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_sin]
  push_cast; ring

theorem tendsto_integral_mul_cos {w : ℝ → ℝ} (hw : Integrable w) :
    Tendsto (fun u : ℝ => ∫ x, w x * Real.cos (u * x)) atTop (𝓝 0) := by
  have h := (tendsto_integral_cexp_neg_mul_I (fun x => (w x : ℂ))).add
    (tendsto_integral_cexp_mul_I (fun x => (w x : ℂ)))
  rw [add_zero] at h
  have h2 := (Complex.continuous_re.tendsto _).comp (h.div_const 2)
  simp only [zero_div, Complex.zero_re] at h2
  refine h2.congr fun u => ?_
  simp only [Function.comp_apply]
  have hi1 : Integrable fun x : ℝ => cexp (-((u : ℂ) * x * I)) * (w x : ℂ) := by
    refine (hw.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp]; simp
  have hi2 : Integrable fun x : ℝ => cexp ((u : ℂ) * x * I) * (w x : ℂ) := by
    refine (hw.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp]; simp
  rw [← integral_add hi1 hi2, ← integral_div]
  have hfun : (fun a : ℝ => (cexp (-((u : ℂ) * (a : ℂ) * I)) * (w a : ℂ) +
      cexp ((u : ℂ) * (a : ℂ) * I) * (w a : ℂ)) / 2) =
      fun a => ((w a * Real.cos (u * a) : ℝ) : ℂ) := by
    funext a
    rw [← add_mul, show (u : ℂ) * (a : ℂ) = ((u * a : ℝ) : ℂ) by push_cast; ring,
      cexp_neg_mul_I_add_cexp_mul_I]
    push_cast; ring
  rw [hfun, integral_complex_ofReal, Complex.ofReal_re]

theorem tendsto_integral_mul_sin {w : ℝ → ℝ} (hw : Integrable w) :
    Tendsto (fun u : ℝ => ∫ x, w x * Real.sin (u * x)) atTop (𝓝 0) := by
  have h := (tendsto_integral_cexp_mul_I (fun x => (w x : ℂ))).sub
    (tendsto_integral_cexp_neg_mul_I (fun x => (w x : ℂ)))
  rw [sub_zero] at h
  have h2 := (Complex.continuous_im.tendsto _).comp (h.div_const 2)
  simp only [zero_div, Complex.zero_im] at h2
  refine h2.congr fun u => ?_
  simp only [Function.comp_apply]
  have hi1 : Integrable fun x : ℝ => cexp (-((u : ℂ) * x * I)) * (w x : ℂ) := by
    refine (hw.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp]; simp
  have hi2 : Integrable fun x : ℝ => cexp ((u : ℂ) * x * I) * (w x : ℂ) := by
    refine (hw.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp]; simp
  rw [← integral_sub hi2 hi1, ← integral_div]
  have hfun : (fun a : ℝ => (cexp ((u : ℂ) * (a : ℂ) * I) * (w a : ℂ) -
      cexp (-((u : ℂ) * (a : ℂ) * I)) * (w a : ℂ)) / 2) =
      fun a => ((w a * Real.sin (u * a) : ℝ) : ℂ) * I := by
    funext a
    rw [← sub_mul, show (u : ℂ) * (a : ℂ) = ((u * a : ℝ) : ℂ) by push_cast; ring,
      cexp_mul_I_sub_cexp_neg_mul_I]
    push_cast; ring
  rw [hfun, integral_mul_const, integral_complex_ofReal]
  simp

/-! ## Oscillatory packets on a horizontal line -/

theorem cexp_packet (u v x : ℝ) :
    cexp (-I * ((u : ℂ) + v * I) * x) = cexp (-((u : ℂ) * x * I)) * cexp ((v : ℂ) * x) := by
  rw [← Complex.exp_add]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

theorem integrable_cexp_mul_ofReal {g : ℝ → ℝ} (hg : Integrable g) (c : ℝ) :
    Integrable fun x : ℝ => cexp (-((c : ℂ) * (x : ℂ) * I)) * (g x : ℂ) := by
  refine (hg.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Complex.norm_exp]; simp

/-- A fixed profile is invisible at high frequency: `E_u(φ) → 0`. -/
theorem tendsto_packet_fixed (v : ℝ) {φ : ℝ → ℝ} :
    Tendsto (fun u : ℝ => ∫ x : ℝ, cexp (-I * ((u : ℂ) + v * I) * x) * (φ x : ℂ)) atTop (𝓝 0) := by
  refine (tendsto_integral_cexp_neg_mul_I fun x => ((Real.exp (v * x) * φ x : ℝ) : ℂ)).congr
    fun u => integral_congr_ae (Eventually.of_forall fun x => ?_)
  show _ = cexp (-I * ((u : ℂ) + v * I) * x) * (φ x : ℂ)
  rw [cexp_packet]; push_cast; ring

/-- **The cosine packet.** `E_u(φ cos(u·)) → ½ ∫ e^{vx} φ`. -/
theorem tendsto_packet_cos (v : ℝ) {φ : ℝ → ℝ} (hφ : Integrable fun x => Real.exp (v * x) * φ x) :
    Tendsto (fun u : ℝ => ∫ x : ℝ, cexp (-I * ((u : ℂ) + v * I) * x) *
      ((φ x * Real.cos (u * x) : ℝ) : ℂ)) atTop
      (𝓝 ((1 / 2 : ℂ) * ((∫ x, Real.exp (v * x) * φ x : ℝ) : ℂ))) := by
  set g : ℝ → ℝ := fun x => Real.exp (v * x) * φ x
  have hosc := (tendsto_integral_cexp_neg_mul_I fun x => (g x : ℂ)).comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have h := (hosc.const_mul (1 / 2 : ℂ)).const_add ((1 / 2 : ℂ) * ((∫ x, g x : ℝ) : ℂ))
  rw [mul_zero, add_zero] at h
  refine h.congr fun u => ?_
  simp only [Function.comp_apply, id]
  have h1 : Integrable (fun x : ℝ => (1 / 2 : ℂ) * ((g x : ℝ) : ℂ)) :=
    (hφ.ofReal (𝕜 := ℂ)).const_mul _
  have h2 : Integrable (fun x : ℝ => (1 / 2 : ℂ) *
      (cexp (-(((2 * u : ℝ) : ℂ) * (x : ℂ) * I)) * ((g x : ℝ) : ℂ))) :=
    (integrable_cexp_mul_ofReal hφ _).const_mul _
  have hpt : ∀ x : ℝ, cexp (-I * ((u : ℂ) + v * I) * x) * ((φ x * Real.cos (u * x) : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ((g x : ℝ) : ℂ) +
        (1 / 2 : ℂ) * (cexp (-(((2 * u : ℝ) : ℂ) * (x : ℂ) * I)) * ((g x : ℝ) : ℂ)) := by
    intro x
    have hc := cexp_neg_mul_I_add_cexp_mul_I (u * x)
    have h2 : cexp (-(((2 * u : ℝ) : ℂ) * x * I)) = cexp (-(((u * x : ℝ) : ℂ) * I)) ^ 2 := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have h1 : cexp (-(((u * x : ℝ) : ℂ) * I)) * cexp (((u * x : ℝ) : ℂ) * I) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [cexp_packet, h2]
    simp only [g]
    push_cast at hc h1 ⊢
    linear_combination (-(1 / 2 : ℂ)) * cexp (-((u : ℂ) * x * I)) *
      (cexp ((v : ℂ) * x) * (φ x : ℂ)) * hc +
        (1 / 2 : ℂ) * (cexp ((v : ℂ) * x) * (φ x : ℂ)) * h1
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add h1 h2, integral_const_mul,
    integral_const_mul, integral_complex_ofReal]

/-- **The sine packet.** `E_u(φ sin(u·)) → (1/2i) ∫ e^{vx} φ = -(i/2) ∫ e^{vx} φ`. -/
theorem tendsto_packet_sin (v : ℝ) {φ : ℝ → ℝ} (hφ : Integrable fun x => Real.exp (v * x) * φ x) :
    Tendsto (fun u : ℝ => ∫ x : ℝ, cexp (-I * ((u : ℂ) + v * I) * x) *
      ((φ x * Real.sin (u * x) : ℝ) : ℂ)) atTop
      (𝓝 ((-I / 2) * ((∫ x, Real.exp (v * x) * φ x : ℝ) : ℂ))) := by
  set g : ℝ → ℝ := fun x => Real.exp (v * x) * φ x
  have hosc := (tendsto_integral_cexp_neg_mul_I fun x => (g x : ℂ)).comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have h := (hosc.const_mul (I / 2)).const_add ((-I / 2) * ((∫ x, g x : ℝ) : ℂ))
  rw [mul_zero, add_zero] at h
  refine h.congr fun u => ?_
  simp only [Function.comp_apply, id]
  have h1 : Integrable (fun x : ℝ => (-I / 2) * ((g x : ℝ) : ℂ)) :=
    (hφ.ofReal (𝕜 := ℂ)).const_mul _
  have h2 : Integrable (fun x : ℝ => (I / 2) *
      (cexp (-(((2 * u : ℝ) : ℂ) * (x : ℂ) * I)) * ((g x : ℝ) : ℂ))) :=
    (integrable_cexp_mul_ofReal hφ _).const_mul _
  have hpt : ∀ x : ℝ, cexp (-I * ((u : ℂ) + v * I) * x) * ((φ x * Real.sin (u * x) : ℝ) : ℂ) =
      (-I / 2) * ((g x : ℝ) : ℂ) +
        (I / 2) * (cexp (-(((2 * u : ℝ) : ℂ) * (x : ℂ) * I)) * ((g x : ℝ) : ℂ)) := by
    intro x
    have hs := cexp_mul_I_sub_cexp_neg_mul_I (u * x)
    have h2 : cexp (-(((2 * u : ℝ) : ℂ) * x * I)) = cexp (-(((u * x : ℝ) : ℂ) * I)) ^ 2 := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have h1 : cexp (-(((u * x : ℝ) : ℂ) * I)) * cexp (((u * x : ℝ) : ℂ) * I) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [cexp_packet, h2]
    simp only [g]
    push_cast at hs h1 ⊢
    linear_combination (I / 2 * cexp (-((u : ℂ) * x * I)) *
      (cexp ((v : ℂ) * x) * (φ x : ℂ))) * hs +
        (-I / 2 * (cexp ((v : ℂ) * x) * (φ x : ℂ))) * h1 +
        (cexp (-((u : ℂ) * x * I)) * cexp ((v : ℂ) * x) * (φ x : ℂ) * Complex.sin ((u : ℂ) * x)) *
          Complex.I_sq
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add h1 h2, integral_const_mul,
    integral_const_mul, integral_complex_ofReal]

/-! ## Real solution of one complex equation in two real unknowns -/

/-- `α a + β b = w` with `α = -Im(b̄w)/Im(āb)`, `β = Im(āw)/Im(āb)`. -/
theorem real_combination_eq {a b w : ℂ} (h : (conj a * b).im ≠ 0) :
    ((-(conj b * w).im / (conj a * b).im : ℝ) : ℂ) * a +
      (((conj a * w).im / (conj a * b).im : ℝ) : ℂ) * b = w := by
  have key : (((conj a * b).im : ℝ) : ℂ) * w =
      -(((conj b * w).im : ℝ) : ℂ) * a + (((conj a * w).im : ℝ) : ℂ) * b := by
    apply Complex.ext <;> simp <;> ring
  have hD : (((conj a * b).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
  apply mul_left_cancel₀ hD
  rw [key]
  push_cast
  field_simp

/-- Uniform real solvability near a nondegenerate limit pair. -/
theorem exists_real_solve_bound {a b : ℝ → ℂ} {A B : ℂ} (ha : Tendsto a atTop (𝓝 A))
    (hb : Tendsto b atTop (𝓝 B)) (hAB : (conj A * B).im ≠ 0) :
    ∃ K U : ℝ, 0 ≤ K ∧ ∀ u, U ≤ u → (conj (a u) * b u).im ≠ 0 ∧ ∀ w : ℂ,
      |(conj (b u) * w).im / (conj (a u) * b u).im| +
        |(conj (a u) * w).im / (conj (a u) * b u).im| ≤ K * ‖w‖ := by
  set D := |(conj A * B).im|
  have hD : 0 < D := abs_pos.mpr hAB
  have hdet : Tendsto (fun u => (conj (a u) * b u).im) atTop (𝓝 (conj A * B).im) :=
    (Complex.continuous_im.tendsto _).comp
      (((Complex.continuous_conj.tendsto _).comp ha).mul hb)
  have e1 := hdet.eventually (Metric.ball_mem_nhds _ (half_pos hD))
  have e2 := ha.norm.eventually (gt_mem_nhds (lt_add_one ‖A‖))
  have e3 := hb.norm.eventually (gt_mem_nhds (lt_add_one ‖B‖))
  obtain ⟨U, hU⟩ := eventually_atTop.mp (e1.and (e2.and e3))
  refine ⟨2 * (‖A‖ + 1 + (‖B‖ + 1)) / D, U, by positivity, fun u hu => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hU u hu
  rw [Real.dist_eq] at h1
  have hDu : D / 2 ≤ |(conj (a u) * b u).im| := by
    have := abs_sub_abs_le_abs_sub (conj A * B).im (conj (a u) * b u).im
    rw [abs_sub_comm] at this
    linarith
  have hDu0 : 0 < |(conj (a u) * b u).im| := lt_of_lt_of_le (half_pos hD) hDu
  refine ⟨abs_pos.mp hDu0, fun w => ?_⟩
  have hbw : |(conj (b u) * w).im| ≤ ‖b u‖ * ‖w‖ := by
    refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_mul, Complex.norm_conj]
  have haw : |(conj (a u) * w).im| ≤ ‖a u‖ * ‖w‖ := by
    refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_mul, Complex.norm_conj]
  rw [abs_div, abs_div, ← add_div, div_le_iff₀ hDu0]
  calc |(conj (b u) * w).im| + |(conj (a u) * w).im| ≤ (‖A‖ + 1 + (‖B‖ + 1)) * ‖w‖ := by
        nlinarith [norm_nonneg w]
    _ = 2 * (‖A‖ + 1 + (‖B‖ + 1)) / D * ‖w‖ * (D / 2) := by field_simp
    _ ≤ 2 * (‖A‖ + 1 + (‖B‖ + 1)) / D * ‖w‖ * |(conj (a u) * b u).im| :=
        mul_le_mul_of_nonneg_left hDu (by positivity)

/-! ## Derivatives of oscillatory packets -/

theorem iteratedDeriv_cos_mul_add (u c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Real.cos (u * x + c)) =
      fun x => u ^ n * Real.cos (u * x + c + n * (Real.pi / 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h' : HasDerivAt (fun x : ℝ => u ^ n * Real.cos (u * x + c + n * (Real.pi / 2)))
        (u ^ n * (-Real.sin (u * x + c + n * (Real.pi / 2)) * u)) x := by
      have := ((((hasDerivAt_id x).const_mul u).add_const c).add_const
        ((n : ℝ) * (Real.pi / 2))).cos.const_mul (u ^ n)
      simpa using this
    rw [h'.deriv]
    have hc : Real.cos (u * x + c + ((n + 1 : ℕ) : ℝ) * (Real.pi / 2)) =
        -Real.sin (u * x + c + n * (Real.pi / 2)) := by
      push_cast
      rw [show u * x + c + ((n : ℝ) + 1) * (Real.pi / 2) =
        u * x + c + n * (Real.pi / 2) + Real.pi / 2 by ring, Real.cos_add_pi_div_two]
    rw [hc, pow_succ]; ring

theorem abs_iteratedDeriv_cos_mul_add_le (u c : ℝ) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun x : ℝ => Real.cos (u * x + c)) x| ≤ |u| ^ n := by
  rw [iteratedDeriv_cos_mul_add, abs_mul, abs_pow]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- **Packet derivative bound.** If `|φ^{(j)}| ≤ M` for `j ≤ n`, then
`|(φ(x) cos(ux + c))^{(n)}| ≤ M (1 + |u|)^n`. -/
theorem abs_iteratedDeriv_mul_cos_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {n : ℕ} {M : ℝ}
    (hM : ∀ j ≤ n, ∀ x, |iteratedDeriv j φ x| ≤ M) (u c x : ℝ) :
    |iteratedDeriv n (fun x => φ x * Real.cos (u * x + c)) x| ≤ M * (1 + |u|) ^ n := by
  have hcos : ContDiff ℝ ∞ fun x : ℝ => Real.cos (u * x + c) := by fun_prop
  rw [show (fun x => φ x * Real.cos (u * x + c)) = φ * fun x => Real.cos (u * x + c) from rfl,
    iteratedDeriv_mul (hφ.contDiffAt.of_le (mod_cast le_top))
      (hcos.contDiffAt.of_le (mod_cast le_top))]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (Nat.zero_le _) x)
  calc |∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * iteratedDeriv i φ x *
        iteratedDeriv (n - i) (fun x => Real.cos (u * x + c)) x|
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M * |u| ^ (n - i) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        rw [abs_mul, abs_mul, Nat.abs_cast]
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hM i hi' x) (by positivity))
          (abs_iteratedDeriv_cos_mul_add_le u c _ x) (abs_nonneg _) (by positivity)
    _ = M * (1 + |u|) ^ n := by
        rw [add_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

end

end GaloisForLFunctions.HTGeometry
