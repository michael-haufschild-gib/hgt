import GaloisForLFunctions.RHTower.DeBruijnShiftContraction
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus

/-!
# The heat flow contracts the zero strip of a Fourier transform

For a kernel `g : ℝ → ℝ` that is continuous, even, nonnegative, positive at `0`, and decays like
`A·exp(−B e^{b|x|} + c x²)`, put

`T g (z) = ∫ g(x) e^{izx} dx`.

`T g` is entire, even, real on the real axis and of order at most one. If every zero of `T g`
satisfies `|Im w| ≤ Δ`, then for every `t > 0` every zero of `T (g·e^{t x²})` satisfies
`(Im w)² ≤ max(Δ² − 2t, 0)` (`cosTransform_heat_zeros_im_sq_le`). In particular the heat-deformed
transform has only real zeros once `2t ≥ Δ²`.

Mechanism (de Bruijn). Multiplying the kernel by `cosh(λx)` replaces `T g(z)` by
`(T g(z+iλ) + T g(z−iλ))/2`, which shrinks the zero strip from `Δ` to `√(Δ² − λ²)`
(`DeBruijn.add_shift_ne_zero`). With `λ² = 2t/n`, `n` steps shrink it to `√(Δ² − 2t)`; the kernels
`g·cosh(λx)^n` increase to `g·e^{t x²}` (`(1 + tx²/n)^n ≤ cosh(λx)^n ≤ e^{t x²}`), the transforms
converge locally uniformly, and the Hurwitz closed-locus transfer passes the strip to the limit.
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-! ## Kernels and their transforms -/

/-- A continuous even nonnegative kernel, positive at `0`, with super-exponential decay
`g(x) ≤ A exp(−B e^{b|x|} + c x²)`. -/
structure SuperExpKernel (g : ℝ → ℝ) : Prop where
  continuous : Continuous g
  even : ∀ x, g (-x) = g x
  nonneg : ∀ x, 0 ≤ g x
  pos_zero : 0 < g 0
  decay : ∃ A B b c : ℝ, 0 ≤ A ∧ 0 < B ∧ 0 < b ∧ 0 ≤ c ∧
    ∀ x, g x ≤ A * Real.exp (-(B * Real.exp (b * |x|)) + c * x ^ 2)

/-- The transform `T g (z) = ∫ g(x) e^{izx} dx`. -/
def cosTransform (g : ℝ → ℝ) (z : ℂ) : ℂ := ∫ x : ℝ, (g x : ℂ) * Complex.exp (I * z * x)

/-! ## Elementary majorants -/

theorem one_add_sq_div_two_le_cosh (u : ℝ) : 1 + u ^ 2 / 2 ≤ Real.cosh u := by
  have h := Real.hasSum_cosh u
  have hle := sum_le_hasSum (Finset.range 2)
    (fun n _ => div_nonneg ((even_two_mul n).pow_nonneg u) (by positivity)) h
  simpa [Finset.sum_range_succ] using hle

/-- `a v − e^v ≤ a log(1+a)` for `a ≥ 0`. -/
theorem mul_sub_exp_le {a v : ℝ} (ha : 0 ≤ a) : a * v - Real.exp v ≤ a * Real.log (1 + a) := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0; simp; exact (Real.exp_pos v).le
  have h1a : 0 < 1 + a := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < Real.exp v / (1 + a) by positivity)
  rw [Real.log_div (Real.exp_pos v).ne' h1a.ne', Real.log_exp] at hlog
  have hfrac : a * (Real.exp v / (1 + a)) ≤ Real.exp v := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ h1a]
    nlinarith [Real.exp_pos v]
  nlinarith [mul_le_mul_of_nonneg_left hlog ha]

/-- The quadratic term is absorbed by a quarter of the double exponential. -/
theorem exists_sq_le_exp {B b c : ℝ} (hB : 0 < B) (hb : 0 < b) (hc : 0 ≤ c) :
    ∃ K : ℝ, ∀ u : ℝ, 0 ≤ u → c * u ^ 2 ≤ B / 4 * Real.exp (b * u) + K := by
  set u₀ := 24 * c / (B * b ^ 3) with hu₀
  refine ⟨c * u₀ ^ 2, fun u hu => ?_⟩
  rcases le_or_gt u u₀ with h | h
  · have : c * u ^ 2 ≤ c * u₀ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact pow_le_pow_left₀ hu h 2
    have := Real.exp_pos (b * u)
    nlinarith
  · have hcube := Real.pow_div_factorial_le_exp (b * u) (by positivity) 3
    norm_num [Nat.factorial] at hcube
    have hu0 : 0 < u := lt_of_le_of_lt (by positivity) h
    -- `c u² ≤ (B b³/24) u³ ≤ (B/4) e^{bu}`
    have h1 : c * u ^ 2 ≤ B * b ^ 3 / 24 * u ^ 3 := by
      have : c ≤ B * b ^ 3 / 24 * u := by
        rw [hu₀, div_lt_iff₀ (by positivity)] at h
        nlinarith
      nlinarith [sq_nonneg u]
    have h2 : B * b ^ 3 / 24 * u ^ 3 ≤ B / 4 * Real.exp (b * u) := by
      have : (b * u) ^ 3 / 6 ≤ Real.exp (b * u) := hcube
      nlinarith
    nlinarith [sq_nonneg u₀]

/-- The pointwise majorant of `|g(x) e^{izx}|`. -/
theorem exponent_le {B b c K y x : ℝ} (hB : 0 < B) (hb : 0 < b) (hy : 0 ≤ y)
    (hK : ∀ u : ℝ, 0 ≤ u → c * u ^ 2 ≤ B / 4 * Real.exp (b * u) + K) :
    -(B * Real.exp (b * |x|)) + c * x ^ 2 + y * |x| ≤
      K + y / b * Real.log (1 + 4 * y / (B * b)) - B / 2 * Real.exp (b * |x|) := by
  have h1 := hK |x| (abs_nonneg x)
  rw [sq_abs] at h1
  have ha : 0 ≤ 4 * y / (B * b) := by positivity
  have h2 := mul_sub_exp_le (v := b * |x|) ha
  have h3 : y * |x| - B / 4 * Real.exp (b * |x|) =
      B / 4 * (4 * y / (B * b) * (b * |x|) - Real.exp (b * |x|)) := by
    field_simp
  have h4 : B / 4 * (4 * y / (B * b) * Real.log (1 + 4 * y / (B * b))) =
      y / b * Real.log (1 + 4 * y / (B * b)) := by
    field_simp
  have h5 : y * |x| - B / 4 * Real.exp (b * |x|) ≤ y / b * Real.log (1 + 4 * y / (B * b)) := by
    rw [h3, ← h4]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-- The Gaussian floor of the double exponential. -/
theorem exp_neg_half_doubleExp_le {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (x : ℝ) :
    Real.exp (-(B / 2 * Real.exp (b * |x|))) ≤ Real.exp (-(B * b ^ 2 / 4) * x ^ 2) := by
  apply Real.exp_le_exp.mpr
  have h := Real.pow_div_factorial_le_exp (b * |x|) (by positivity) 2
  norm_num [Nat.factorial] at h
  have : b ^ 2 * x ^ 2 / 2 ≤ Real.exp (b * |x|) := by
    have hx : (b * |x|) ^ 2 = b ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
    rw [← hx]; linarith
  nlinarith

/-- **Integrable majorant.** For `y ≥ 0` the kernel bound times `e^{y|x|}` is dominated by a
Gaussian with an explicit constant. -/
theorem kernel_mul_exp_le {A B b c K y : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (hb : 0 < b) (hy : 0 ≤ y)
    (hK : ∀ u : ℝ, 0 ≤ u → c * u ^ 2 ≤ B / 4 * Real.exp (b * u) + K) (x : ℝ) :
    A * Real.exp (-(B * Real.exp (b * |x|)) + c * x ^ 2) * Real.exp (y * |x|) ≤
      A * Real.exp K * Real.exp (y / b * Real.log (1 + 4 * y / (B * b))) *
        Real.exp (-(B * b ^ 2 / 4) * x ^ 2) := by
  rw [mul_assoc, ← Real.exp_add]
  have h1 := exponent_le (x := x) hB hb hy hK
  have h2 := exp_neg_half_doubleExp_le hB hb x
  calc A * Real.exp (-(B * Real.exp (b * |x|)) + c * x ^ 2 + y * |x|)
      ≤ A * Real.exp (K + y / b * Real.log (1 + 4 * y / (B * b)) -
          B / 2 * Real.exp (b * |x|)) := by
        gcongr
    _ = A * Real.exp K * Real.exp (y / b * Real.log (1 + 4 * y / (B * b))) *
          Real.exp (-(B / 2 * Real.exp (b * |x|))) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ _ := by gcongr

/-! ## Integrability and the order-one envelope -/

theorem norm_integrand (g : ℝ → ℝ) (z : ℂ) (x : ℝ) :
    ‖(g x : ℂ) * Complex.exp (I * z * x)‖ = |g x| * Real.exp (-(z.im * x)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem norm_integrand_le (g : ℝ → ℝ) (z : ℂ) (x : ℝ) :
    ‖(g x : ℂ) * Complex.exp (I * z * x)‖ ≤ |g x| * Real.exp (|z.im| * |x|) := by
  rw [norm_integrand]
  gcongr
  rw [← abs_mul]
  exact neg_le_abs _

theorem SuperExpKernel.integrable_mul_exp {g : ℝ → ℝ} (hg : SuperExpKernel g) (y : ℝ) :
    Integrable (fun x : ℝ => g x * Real.exp (y * |x|)) := by
  obtain ⟨A, B, b, c, hA, hB, hb, hc, hdec⟩ := hg.decay
  obtain ⟨K, hK⟩ := exists_sq_le_exp hB hb hc
  set y' := max y 0
  have hmaj : Integrable (fun x : ℝ => A * Real.exp K *
      Real.exp (y' / b * Real.log (1 + 4 * y' / (B * b))) *
        Real.exp (-(B * b ^ 2 / 4) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine hmaj.mono' ((hg.continuous.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg.nonneg x) (Real.exp_pos _).le)]
  calc g x * Real.exp (y * |x|) ≤ A * Real.exp (-(B * Real.exp (b * |x|)) + c * x ^ 2) *
        Real.exp (y' * |x|) := by
        gcongr
        · exact hdec x
        · exact le_max_left _ _
    _ ≤ _ := kernel_mul_exp_le hA hB hb (le_max_right _ _) hK x

theorem SuperExpKernel.integrable {g : ℝ → ℝ} (hg : SuperExpKernel g) (z : ℂ) :
    Integrable (fun x : ℝ => (g x : ℂ) * Complex.exp (I * z * x)) := by
  refine (hg.integrable_mul_exp |z.im|).mono'
    (((Complex.continuous_ofReal.comp hg.continuous).mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have h := norm_integrand_le g z x
  rwa [abs_of_nonneg (hg.nonneg x)] at h

/-- The logarithmic factor grows at most like `log(2+y)`. -/
theorem log_one_add_le {B b y : ℝ} (hB : 0 < B) (hb : 0 < b) (hy : 0 ≤ y) :
    Real.log (1 + 4 * y / (B * b)) ≤ Real.log (max 1 (4 / (B * b))) + Real.log (2 + y) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  have hM1 : 1 ≤ max 1 (4 / (B * b)) := le_max_left _ _
  have hM2 : 4 / (B * b) ≤ max 1 (4 / (B * b)) := le_max_right _ _
  have : 4 * y / (B * b) = 4 / (B * b) * y := by ring
  rw [this]
  nlinarith

/-- **Order-one envelope** of the transform of a super-exponential kernel. -/
theorem SuperExpKernel.exists_envelope {g : ℝ → ℝ} (hg : SuperExpKernel g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖cosTransform g z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  obtain ⟨A, B, b, c, hA, hB, hb, hc, hdec⟩ := hg.decay
  obtain ⟨K, hK⟩ := exists_sq_le_exp hB hb hc
  set M := max 1 (4 / (B * b)) with hM
  set I₀ := A * Real.exp K * Real.sqrt (Real.pi / (B * b ^ 2 / 4)) with hI₀
  have hI₀0 : 0 ≤ I₀ := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM1 : 1 ≤ M := le_max_left _ _
  set C := 1 / b * (1 + Real.log M / Real.log 2) + |Real.log (I₀ + 1)| / Real.log 2 with hC
  have hC0 : 0 ≤ C := by
    have := Real.log_nonneg hM1
    positivity
  refine ⟨C, hC0, fun z => ?_⟩
  set y := |z.im|
  have hy : 0 ≤ y := abs_nonneg _
  have hyz : y ≤ ‖z‖ := Complex.abs_im_le_norm z
  -- the integral bound
  have hbound : ‖cosTransform g z‖ ≤ I₀ * Real.exp (y / b * Real.log (1 + 4 * y / (B * b))) := by
    unfold cosTransform
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmaj : ∀ x : ℝ, ‖(g x : ℂ) * Complex.exp (I * z * x)‖ ≤
        A * Real.exp K * Real.exp (y / b * Real.log (1 + 4 * y / (B * b))) *
          Real.exp (-(B * b ^ 2 / 4) * x ^ 2) := by
      intro x
      refine (norm_integrand_le g z x).trans ?_
      rw [abs_of_nonneg (hg.nonneg x)]
      calc g x * Real.exp (y * |x|) ≤ A * Real.exp (-(B * Real.exp (b * |x|)) + c * x ^ 2) *
            Real.exp (y * |x|) := by gcongr; exact hdec x
        _ ≤ _ := kernel_mul_exp_le hA hB hb hy hK x
    refine (integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
      ((integrable_exp_neg_mul_sq (by positivity)).const_mul _)
      (Eventually.of_forall hmaj)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_gaussian, hI₀]
    ring
  refine hbound.trans ?_
  -- compare exponents
  have hlog2y : Real.log 2 ≤ Real.log (2 + ‖z‖) := Real.log_le_log (by norm_num) (by linarith)
  have hL : 0 ≤ Real.log (2 + ‖z‖) := le_trans hl2.le hlog2y
  have hI₀le : I₀ ≤ Real.exp (|Real.log (I₀ + 1)|) := by
    calc I₀ ≤ I₀ + 1 := by linarith
      _ = Real.exp (Real.log (I₀ + 1)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (le_abs_self _)
  rw [← Real.exp_log (show 0 < Real.exp (|Real.log (I₀ + 1)|) by positivity)] at hI₀le
  calc I₀ * Real.exp (y / b * Real.log (1 + 4 * y / (B * b)))
      ≤ Real.exp (|Real.log (I₀ + 1)|) * Real.exp (y / b * Real.log (1 + 4 * y / (B * b))) := by
        rw [Real.log_exp] at hI₀le
        gcongr
    _ = Real.exp (|Real.log (I₀ + 1)| + y / b * Real.log (1 + 4 * y / (B * b))) := by
        rw [Real.exp_add]
    _ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
        apply Real.exp_le_exp.mpr
        have h1 : Real.log (1 + 4 * y / (B * b)) ≤ Real.log M + Real.log (2 + y) :=
          log_one_add_le hB hb hy
        have hlogy : Real.log (2 + y) ≤ Real.log (2 + ‖z‖) := Real.log_le_log (by linarith)
          (by linarith)
        have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
        have hq : 1 ≤ Real.log (2 + ‖z‖) / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
        have hz1 : 1 + ‖z‖ ≤ (1 + ‖z‖) * (Real.log (2 + ‖z‖) / Real.log 2) :=
          le_mul_of_one_le_right (by positivity) hq
        have hp : 1 ≤ (1 + ‖z‖) * (Real.log (2 + ‖z‖) / Real.log 2) := by
          have := norm_nonneg z; linarith
        have hyb : y / b * Real.log (1 + 4 * y / (B * b)) ≤
            (1 / b) * ‖z‖ * (Real.log M + Real.log (2 + ‖z‖)) := by
          have hlog_nonneg : 0 ≤ Real.log (1 + 4 * y / (B * b)) :=
            Real.log_nonneg (by have : 0 ≤ 4 * y / (B * b) := by positivity
                                linarith)
          calc y / b * Real.log (1 + 4 * y / (B * b)) ≤ ‖z‖ / b * Real.log (1 + 4 * y / (B * b)) := by
                gcongr
            _ ≤ ‖z‖ / b * (Real.log M + Real.log (2 + ‖z‖)) := by
                gcongr
                exact h1.trans (by linarith)
            _ = _ := by ring
        -- assemble with `C`
        have hzL : ‖z‖ * Real.log M ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) * (Real.log M / Real.log 2) := by
          have : ‖z‖ ≤ (1 + ‖z‖) * (Real.log (2 + ‖z‖) / Real.log 2) := by linarith
          calc ‖z‖ * Real.log M ≤ (1 + ‖z‖) * (Real.log (2 + ‖z‖) / Real.log 2) * Real.log M :=
                mul_le_mul_of_nonneg_right this hlogM
            _ = _ := by ring
        have hzL2 : ‖z‖ * Real.log (2 + ‖z‖) ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := by nlinarith
        have habs : |Real.log (I₀ + 1)| ≤
            |Real.log (I₀ + 1)| / Real.log 2 * ((1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
          have h := mul_le_mul_of_nonneg_left hp (abs_nonneg (Real.log (I₀ + 1)))
          calc |Real.log (I₀ + 1)| = |Real.log (I₀ + 1)| * 1 := by ring
            _ ≤ _ := h
            _ = _ := by ring
        rw [hC]
        have hb1 : 0 ≤ 1 / b := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hzL hb1, mul_le_mul_of_nonneg_left hzL2 hb1]

/-! ## Analytic structure of the transform -/

theorem SuperExpKernel.differentiable {g : ℝ → ℝ} (hg : SuperExpKernel g) :
    Differentiable ℂ (cosTransform g) := by
  intro z₀
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun x : ℝ => (g x : ℂ) * Complex.exp (I * z * x))
      volume := fun z =>
    ((Complex.continuous_ofReal.comp hg.continuous).mul (by fun_prop)).aestronglyMeasurable
  refine GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated
    (bound := fun x => g x * Real.exp ((|z₀.im| + 1) * |x|)) one_pos (fun z _ => hmeas z)
    (fun x => ?_) (fun x z hz => ?_) (hg.integrable_mul_exp _)
  · exact (Differentiable.differentiableOn (by fun_prop))
  · refine (norm_integrand_le g z x).trans ?_
    rw [abs_of_nonneg (hg.nonneg x)]
    gcongr
    · exact hg.nonneg x
    · have h1 : ‖z - z₀‖ < 1 := by rwa [mem_ball, dist_eq_norm] at hz
      have h2 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        have := Complex.abs_im_le_norm (z - z₀); simpa using this
      have h3 := abs_sub_abs_le_abs_sub z.im z₀.im
      linarith

theorem SuperExpKernel.cosTransform_neg {g : ℝ → ℝ} (hg : SuperExpKernel g) (z : ℂ) :
    cosTransform g (-z) = cosTransform g z := by
  unfold cosTransform
  rw [← integral_neg_eq_self (fun x : ℝ => (g x : ℂ) * Complex.exp (I * z * x)) volume]
  congr 1
  funext x
  rw [hg.even]
  push_cast
  ring_nf

theorem SuperExpKernel.cosTransform_conj {g : ℝ → ℝ} (hg : SuperExpKernel g) (z : ℂ) :
    cosTransform g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (cosTransform g z) := by
  have h : (starRingEnd ℂ) (cosTransform g z) = cosTransform g (-(starRingEnd ℂ) z) := by
    unfold cosTransform
    rw [← integral_conj]
    congr 1
    funext x
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [h, hg.cosTransform_neg]

theorem SuperExpKernel.integral_pos {g : ℝ → ℝ} (hg : SuperExpKernel g) : 0 < ∫ x, g x := by
  have hint : Integrable g := by
    simpa using hg.integrable_mul_exp 0
  rw [integral_pos_iff_support_of_nonneg (fun x => hg.nonneg x) hint]
  have hopen : IsOpen {x : ℝ | 0 < g x} := isOpen_lt continuous_const hg.continuous
  have hpos : 0 < volume {x : ℝ | 0 < g x} := hopen.measure_pos volume ⟨0, hg.pos_zero⟩
  refine lt_of_lt_of_le hpos (measure_mono fun x hx => ?_)
  exact Function.mem_support.mpr (ne_of_gt hx)

theorem SuperExpKernel.cosTransform_zero_ne {g : ℝ → ℝ} (hg : SuperExpKernel g) :
    cosTransform g 0 ≠ 0 := by
  unfold cosTransform
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal]
  exact_mod_cast hg.integral_pos.ne'

/-- **The shift identity**: `T g(z+iλ) + T g(z−iλ) = 2 T(g·cosh(λ·))(z)`. -/
theorem SuperExpKernel.cosTransform_add_shift {g : ℝ → ℝ} (hg : SuperExpKernel g) (lam : ℝ)
    (z : ℂ) :
    cosTransform g (z + lam * I) + cosTransform g (z - lam * I) =
      2 * cosTransform (fun x => g x * Real.cosh (lam * x)) z := by
  unfold cosTransform
  rw [← integral_add (hg.integrable _) (hg.integrable _), ← integral_const_mul]
  congr 1
  funext x
  push_cast
  have e1 : I * ((z + lam * I) * x) = I * z * x + -(lam * x) := by
    ring_nf; rw [Complex.I_sq]; ring
  have e2 : I * ((z - lam * I) * x) = I * z * x + lam * x := by
    ring_nf; rw [Complex.I_sq]; ring
  have hc : Complex.cosh (lam * x) * 2 = Complex.exp (lam * x) + Complex.exp (-(lam * x)) := by
    rw [mul_comm, Complex.two_cosh]
  simp only [mul_assoc] at e1 e2 ⊢
  rw [e1, e2, Complex.exp_add, Complex.exp_add]
  linear_combination (-((g x : ℂ) * Complex.exp (I * (z * x)))) * hc

/-! ## Closure of the kernel class -/

theorem SuperExpKernel.mul_cosh_pow {g : ℝ → ℝ} (hg : SuperExpKernel g) (lam : ℝ) (j : ℕ) :
    SuperExpKernel (fun x => g x * Real.cosh (lam * x) ^ j) where
  continuous := hg.continuous.mul (by fun_prop)
  even x := by simp only [mul_neg, Real.cosh_neg, hg.even]
  nonneg x := mul_nonneg (hg.nonneg x) (pow_nonneg (Real.cosh_pos _).le _)
  pos_zero := by simpa using hg.pos_zero
  decay := by
    obtain ⟨A, B, b, c, hA, hB, hb, hc, hdec⟩ := hg.decay
    refine ⟨A, B, b, c + j * lam ^ 2 / 2, hA, hB, hb, by positivity, fun x => ?_⟩
    have hcosh : Real.cosh (lam * x) ^ j ≤ Real.exp (j * lam ^ 2 / 2 * x ^ 2) := by
      calc Real.cosh (lam * x) ^ j ≤ Real.exp ((lam * x) ^ 2 / 2) ^ j :=
            pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) j
        _ = Real.exp (j * lam ^ 2 / 2 * x ^ 2) := by
            rw [← Real.exp_nat_mul]; ring_nf
    calc g x * Real.cosh (lam * x) ^ j ≤ A * Real.exp (-(B * Real.exp (b * |x|)) + c * x ^ 2) *
          Real.exp (j * lam ^ 2 / 2 * x ^ 2) :=
          mul_le_mul (hdec x) hcosh (pow_nonneg (Real.cosh_pos _).le _)
            (mul_nonneg hA (Real.exp_pos _).le)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

theorem SuperExpKernel.mul_exp_sq {g : ℝ → ℝ} (hg : SuperExpKernel g) {t : ℝ} (ht : 0 ≤ t) :
    SuperExpKernel (fun x => g x * Real.exp (t * x ^ 2)) where
  continuous := hg.continuous.mul (by fun_prop)
  even x := by simp only [even_two.neg_pow, hg.even]
  nonneg x := mul_nonneg (hg.nonneg x) (Real.exp_pos _).le
  pos_zero := by simpa using hg.pos_zero
  decay := by
    obtain ⟨A, B, b, c, hA, hB, hb, hc, hdec⟩ := hg.decay
    refine ⟨A, B, b, c + t, hA, hB, hb, by positivity, fun x => ?_⟩
    calc g x * Real.exp (t * x ^ 2) ≤ A * Real.exp (-(B * Real.exp (b * |x|)) + c * x ^ 2) *
          Real.exp (t * x ^ 2) :=
          mul_le_mul_of_nonneg_right (hdec x) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-! ## One contraction step and its iteration -/

/-- **One step.** If every zero of `T g` has `(Im w)² ≤ D`, every zero of `T(g·cosh(λ·))` has
`(Im w)² ≤ max(D − λ², 0)`. -/
theorem SuperExpKernel.zeros_mul_cosh {g : ℝ → ℝ} (hg : SuperExpKernel g) {D : ℝ} (hD : 0 ≤ D)
    (hzeros : ∀ w, cosTransform g w = 0 → w.im ^ 2 ≤ D) {lam : ℝ} (hlam : 0 < lam) :
    ∀ w, cosTransform (fun x => g x * Real.cosh (lam * x)) w = 0 →
      w.im ^ 2 ≤ max (D - lam ^ 2) 0 := by
  intro w hw
  obtain ⟨C, hC0, hC⟩ := hg.exists_envelope
  have han : AnalyticOnNhd ℂ (cosTransform g) univ :=
    hg.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hΔ : ∀ v, cosTransform g v = 0 → |v.im| ≤ Real.sqrt D :=
    fun v hv => Real.abs_le_sqrt (hzeros v hv)
  have hsum : cosTransform g (w + lam * I) + cosTransform g (w - lam * I) = 0 := by
    rw [hg.cosTransform_add_shift, hw, mul_zero]
  by_contra hcon
  push Not at hcon
  have hne : w.im ≠ 0 := by
    intro h0
    rw [h0] at hcon
    have : (0 : ℝ) ^ 2 ≤ max (D - lam ^ 2) 0 := by simp
    linarith
  have hlt : Real.sqrt D ^ 2 < w.im ^ 2 + lam ^ 2 := by
    rw [Real.sq_sqrt hD]
    have := le_max_left (D - lam ^ 2) 0
    linarith
  exact DeBruijn.add_shift_ne_zero hC0 han hg.cosTransform_zero_ne hg.cosTransform_neg
    hg.cosTransform_conj hC hΔ hlam hne hlt hsum

/-- **Iteration.** `j` steps with shift `λ` give `(Im w)² ≤ max(D − jλ², 0)`. -/
theorem SuperExpKernel.zeros_mul_cosh_pow {g : ℝ → ℝ} (hg : SuperExpKernel g) {D : ℝ}
    (hzeros : ∀ w, cosTransform g w = 0 → w.im ^ 2 ≤ D) {lam : ℝ} (hlam : 0 < lam) :
    ∀ j : ℕ, ∀ w, cosTransform (fun x => g x * Real.cosh (lam * x) ^ j) w = 0 →
      w.im ^ 2 ≤ max (D - j * lam ^ 2) 0 := by
  intro j
  induction j with
  | zero =>
    intro w hw
    have : (fun x => g x * Real.cosh (lam * x) ^ (0 : ℕ)) = g := by funext x; simp
    rw [this] at hw
    have := hzeros w hw
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    exact le_max_of_le_left this
  | succ j ih =>
    intro w hw
    have hk := hg.mul_cosh_pow lam j
    have hDj : 0 ≤ max (D - j * lam ^ 2) 0 := le_max_right _ _
    have hfun : (fun x => g x * Real.cosh (lam * x) ^ (j + 1)) =
        fun x => (g x * Real.cosh (lam * x) ^ j) * Real.cosh (lam * x) := by
      funext x; ring
    rw [hfun] at hw
    have h := hk.zeros_mul_cosh hDj ih hlam w hw
    refine h.trans ?_
    push_cast
    rcases le_total (D - j * lam ^ 2) 0 with h0 | h0
    · rw [max_eq_right h0, zero_sub]
      exact max_le (by nlinarith [sq_nonneg lam]) le_rfl |>.trans (le_max_right _ _)
    · rw [max_eq_left h0]
      exact max_le_max (by ring_nf; linarith) le_rfl

/-! ## Passage to the heat kernel -/

/-- `(1 + t x²/n)^n ≤ cosh(√(2t/n) x)^n ≤ e^{t x²}`, whence convergence. -/
theorem tendsto_cosh_pow_heat {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    Tendsto (fun n : ℕ => Real.cosh (Real.sqrt (2 * t / (n + 1)) * x) ^ (n + 1)) atTop
      (𝓝 (Real.exp (t * x ^ 2))) := by
  have hsq : ∀ n : ℕ, (Real.sqrt (2 * t / (n + 1)) * x) ^ 2 = 2 * t / (n + 1) * x ^ 2 := by
    intro n
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hlow : ∀ n : ℕ, (1 + t * x ^ 2 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
      Real.cosh (Real.sqrt (2 * t / (n + 1)) * x) ^ (n + 1) := by
    intro n
    apply pow_le_pow_left₀ (by positivity)
    have := one_add_sq_div_two_le_cosh (Real.sqrt (2 * t / (n + 1)) * x)
    rw [hsq] at this
    push_cast
    calc 1 + t * x ^ 2 / ((n : ℝ) + 1) = 1 + 2 * t / (n + 1) * x ^ 2 / 2 := by
          field_simp
      _ ≤ _ := this
  have hup : ∀ n : ℕ, Real.cosh (Real.sqrt (2 * t / (n + 1)) * x) ^ (n + 1) ≤
      Real.exp (t * x ^ 2) := by
    intro n
    calc Real.cosh (Real.sqrt (2 * t / (n + 1)) * x) ^ (n + 1)
        ≤ Real.exp ((Real.sqrt (2 * t / (n + 1)) * x) ^ 2 / 2) ^ (n + 1) :=
          pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) _
      _ = Real.exp (t * x ^ 2) := by
          rw [← Real.exp_nat_mul, hsq]
          congr 1
          push_cast
          field_simp
  have hlim : Tendsto (fun n : ℕ => (1 + t * x ^ 2 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) atTop
      (𝓝 (Real.exp (t * x ^ 2))) :=
    (Real.tendsto_one_add_div_pow_exp (t * x ^ 2)).comp (tendsto_add_atTop_nat 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hup

/-- The cosh-iterated transforms converge to the heat transform locally uniformly. -/
theorem SuperExpKernel.tendstoLocallyUniformly_heat {g : ℝ → ℝ} (hg : SuperExpKernel g) {t : ℝ}
    (ht : 0 ≤ t) :
    TendstoLocallyUniformly
      (fun n : ℕ => cosTransform (fun x => g x * Real.cosh (Real.sqrt (2 * t / (n + 1)) * x) ^ (n + 1)))
      (cosTransform (fun x => g x * Real.exp (t * x ^ 2))) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set R' := max R 0
  have hh := hg.mul_exp_sq ht
  set gn : ℕ → ℝ → ℝ := fun n x => g x * Real.cosh (Real.sqrt (2 * t / (n + 1)) * x) ^ (n + 1)
  set h : ℝ → ℝ := fun x => g x * Real.exp (t * x ^ 2)
  have hgn_le : ∀ n x, 0 ≤ gn n x ∧ gn n x ≤ h x := by
    intro n x
    refine ⟨mul_nonneg (hg.nonneg x) (pow_nonneg (Real.cosh_pos _).le _), ?_⟩
    refine mul_le_mul_of_nonneg_left ?_ (hg.nonneg x)
    calc Real.cosh (Real.sqrt (2 * t / (n + 1)) * x) ^ (n + 1)
        ≤ Real.exp ((Real.sqrt (2 * t / (n + 1)) * x) ^ 2 / 2) ^ (n + 1) :=
          pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) _
      _ = Real.exp (t * x ^ 2) := by
          rw [← Real.exp_nat_mul, mul_pow, Real.sq_sqrt (by positivity)]
          congr 1
          push_cast
          field_simp
  -- the scalar error
  set ε : ℕ → ℝ := fun n => ∫ x, (h x - gn n x) * Real.exp (R' * |x|)
  have hε : Tendsto ε atTop (𝓝 0) := by
    have hbound := hh.integrable_mul_exp R'
    have hmeas : ∀ n : ℕ, AEStronglyMeasurable
        (fun x => (h x - gn n x) * Real.exp (R' * |x|)) volume := fun n =>
      ((hh.continuous.sub (hg.mul_cosh_pow (Real.sqrt (2 * t / (n + 1))) (n + 1)).continuous).mul
        (by fun_prop)).aestronglyMeasurable
    have hle : ∀ n : ℕ, ∀ᵐ x ∂volume, ‖(h x - gn n x) * Real.exp (R' * |x|)‖ ≤
        h x * Real.exp (R' * |x|) := fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (hgn_le n x).2)
        (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_right (by linarith [(hgn_le n x).1]) (Real.exp_pos _).le
    have hlim : ∀ᵐ x ∂volume, Tendsto (fun n : ℕ => (h x - gn n x) * Real.exp (R' * |x|)) atTop
        (𝓝 0) := Eventually.of_forall fun x => by
      have hc := (tendsto_cosh_pow_heat ht x).const_mul (g x)
      have hd := (tendsto_const_nhds (x := h x)).sub hc
      have hz : h x - g x * Real.exp (t * x ^ 2) = 0 := sub_self _
      rw [hz] at hd
      simpa using hd.mul_const (Real.exp (R' * |x|))
    have := tendsto_integral_of_dominated_convergence
      (F := fun n x => (h x - gn n x) * Real.exp (R' * |x|)) (f := fun _ => (0 : ℝ))
      (fun x => h x * Real.exp (R' * |x|)) hmeas hbound hle hlim
    simpa using this
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [hε.eventually (gt_mem_nhds hδ)] with n hn z hz
  have hzR : |z.im| ≤ R' := (Complex.abs_im_le_norm z).trans ((hR z hz).trans (le_max_left _ _))
  have hk := hg.mul_cosh_pow (Real.sqrt (2 * t / (n + 1))) (n + 1)
  rw [dist_eq_norm]
  unfold cosTransform
  rw [← integral_sub (hh.integrable z) (hk.integrable z)]
  refine lt_of_le_of_lt ((norm_integral_le_integral_norm _).trans ?_) hn
  have hint : Integrable (fun x => (h x - gn n x) * Real.exp (R' * |x|)) :=
    ((hh.integrable_mul_exp R').sub (hk.integrable_mul_exp R')).congr
      (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hint ?_
  · refine Eventually.of_forall fun x => ?_
    beta_reduce
    rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp]
    rw [abs_of_nonneg (sub_nonneg.mpr (hgn_le n x).2)]
    refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr (hgn_le n x).2)
    apply Real.exp_le_exp.mpr
    have : (I * z * x).re = -(z.im * x) := by simp [Complex.mul_re]
    rw [this]
    calc -(z.im * x) ≤ |z.im| * |x| := by rw [← abs_mul]; exact neg_le_abs _
      _ ≤ R' * |x| := mul_le_mul_of_nonneg_right hzR (abs_nonneg x)

/-- **Heat contraction of the zero strip.** If every zero of `T g` has `(Im w)² ≤ D`, then for
every `t > 0` every zero of `T(g·e^{t x²})` has `(Im w)² ≤ max(D − 2t, 0)`. -/
theorem cosTransform_heat_zeros_im_sq_le {g : ℝ → ℝ} (hg : SuperExpKernel g) {D : ℝ}
    (hzeros : ∀ w, cosTransform g w = 0 → w.im ^ 2 ≤ D) {t : ℝ} (ht : 0 < t) :
    ∀ w, cosTransform (fun x => g x * Real.exp (t * x ^ 2)) w = 0 →
      w.im ^ 2 ≤ max (D - 2 * t) 0 := by
  intro w hw
  have hh := hg.mul_exp_sq ht.le
  have hS : IsClosed {v : ℂ | v.im ^ 2 ≤ max (D - 2 * t) 0} :=
    isClosed_le (by fun_prop) continuous_const
  have hconv := hg.tendstoLocallyUniformly_heat ht.le
  have hF : AnalyticOnNhd ℂ (cosTransform (fun x => g x * Real.exp (t * x ^ 2))) univ :=
    hh.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hFn : ∀ n : ℕ, Differentiable ℂ
      (cosTransform (fun x => g x * Real.cosh (Real.sqrt (2 * t / (n + 1)) * x) ^ (n + 1))) :=
    fun n => (hg.mul_cosh_pow _ _).differentiable
  have hzeroS : ∀ n : ℕ, ∀ v,
      cosTransform (fun x => g x * Real.cosh (Real.sqrt (2 * t / (n + 1)) * x) ^ (n + 1)) v = 0 →
        v ∈ {v : ℂ | v.im ^ 2 ≤ max (D - 2 * t) 0} := by
    intro n v hv
    have hlam : 0 < Real.sqrt (2 * t / (n + 1)) := Real.sqrt_pos.mpr (by positivity)
    have h := hg.zeros_mul_cosh_pow hzeros hlam (n + 1) v hv
    have heq : ((n + 1 : ℕ) : ℝ) * Real.sqrt (2 * t / (n + 1)) ^ 2 = 2 * t := by
      rw [Real.sq_sqrt (by positivity)]
      push_cast
      field_simp
    rw [heq] at h
    exact h
  exact GaloisForLFunctions.HTGeometry.zero_mem_closed_of_tendstoLocallyUniformly hconv hF
    (Eventually.of_forall hFn) hS (Eventually.of_forall hzeroS) hh.cosTransform_zero_ne hw

/-- Once `2t ≥ D` the heat transform has only real zeros. -/
theorem cosTransform_heat_zeros_real {g : ℝ → ℝ} (hg : SuperExpKernel g) {D : ℝ}
    (hzeros : ∀ w, cosTransform g w = 0 → w.im ^ 2 ≤ D) {t : ℝ} (ht : D ≤ 2 * t)
    (ht0 : 0 < t) :
    ∀ w, cosTransform (fun x => g x * Real.exp (t * x ^ 2)) w = 0 → w.im = 0 := by
  intro w hw
  have h := cosTransform_heat_zeros_im_sq_le hg hzeros ht0 w hw
  rw [max_eq_right (by linarith)] at h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h (sq_nonneg _))

end

end RHTower.DeBruijn
