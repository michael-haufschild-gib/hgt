import GaloisForLFunctions.RHTower.WeilDeletionTestKit

/-!
# The two-bump test and its autocorrelation

For a bump `φ` supported in `[−s, s]` and a separation `u₀ > 2s`, the real test
`f(y) = φ(y − u₀/2) − φ(y + u₀/2)` has autocorrelation `k = f ⋆ f̃` (`f̃(x) = f(−x)`), a `C²`
compactly supported function with

* `k̂(z) = f̂(z)·f̂(−z)` and `f̂(z) = φ̂(z)·(e^{izu₀/2} − e^{−izu₀/2})`,
* `‖f̂(z)‖ ≤ 2·cosh(u₀·Im z/2)·‖φ̂(z)‖`,
* `k(u₀) = k(−u₀) = −∫ φ²` (the two translates never overlap).

These are the ingredients of the single-prime deletion argument: the prime `p₀ = e^{u₀}` enters
the explicit formula through `k(±u₀)`, which is negative and of size `‖φ‖²`, while the zero side is
controlled by the Fourier decay of `φ`.
-/

open MeasureTheory Complex Set
open scoped Convolution

namespace RHTower.WeilDeletion

noncomputable section

/-- The two-bump test `f(y) = φ(y − u₀/2) − φ(y + u₀/2)`. -/
def twoBump (φ : ℝ → ℝ) (u₀ : ℝ) (y : ℝ) : ℝ := φ (y - u₀ / 2) - φ (y + u₀ / 2)

/-- The reflection `f̃(x) = f(−x)`. -/
def reflectFn (f : ℝ → ℝ) (x : ℝ) : ℝ := f (-x)

/-- The autocorrelation `k = f ⋆ f̃`. -/
def autocorr (f : ℝ → ℝ) : ℝ → ℝ := f ⋆ reflectFn f

/-! ## Regularity and support -/

theorem reflectFn_contDiff {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (reflectFn f) :=
  hf.comp contDiff_neg

theorem reflectFn_integrable {f : ℝ → ℝ} (hf : Integrable f) : Integrable (reflectFn f) := by
  unfold reflectFn
  exact hf.comp_neg

theorem support_reflectFn_subset {f : ℝ → ℝ} {a b : ℝ} (h : Function.support f ⊆ Icc a b) :
    Function.support (reflectFn f) ⊆ Icc (-b) (-a) := by
  intro x hx
  have hx' : -x ∈ Function.support f := hx
  have := h hx'
  exact ⟨by linarith [this.2], by linarith [this.1]⟩

theorem reflectFn_hasCompactSupport {f : ℝ → ℝ} {a b : ℝ} (h : Function.support f ⊆ Icc a b) :
    HasCompactSupport (reflectFn f) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_reflectFn_subset h)

theorem twoBump_contDiff {φ : ℝ → ℝ} {n : ℕ} (hφ : ContDiff ℝ n φ) (u₀ : ℝ) :
    ContDiff ℝ n (twoBump φ u₀) := by
  unfold twoBump
  exact (hφ.comp (contDiff_id.sub contDiff_const)).sub (hφ.comp (contDiff_id.add contDiff_const))

theorem support_twoBump_subset {φ : ℝ → ℝ} {s : ℝ} (hsupp : Function.support φ ⊆ Icc (-s) s)
    {u₀ : ℝ} (hu : 0 ≤ u₀) : Function.support (twoBump φ u₀) ⊆ Icc (-(u₀ / 2 + s)) (u₀ / 2 + s) := by
  intro y hy
  rw [Function.mem_support] at hy
  unfold twoBump at hy
  by_cases h1 : φ (y - u₀ / 2) = 0
  · have h2 : φ (y + u₀ / 2) ≠ 0 := by
      intro h2; apply hy; rw [h1, h2, sub_zero]
    have := hsupp (Function.mem_support.mpr h2)
    rw [Set.mem_Icc] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · have := hsupp (Function.mem_support.mpr h1)
    rw [Set.mem_Icc] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

theorem twoBump_hasCompactSupport {φ : ℝ → ℝ} {s : ℝ} (hsupp : Function.support φ ⊆ Icc (-s) s)
    {u₀ : ℝ} (hu : 0 ≤ u₀) : HasCompactSupport (twoBump φ u₀) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_twoBump_subset hsupp hu)

theorem twoBump_integrable {φ : ℝ → ℝ} {s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 0 ≤ u₀) :
    Integrable (twoBump φ u₀) :=
  (twoBump_contDiff hφ u₀).continuous.integrable_of_hasCompactSupport
    (twoBump_hasCompactSupport hsupp hu)

theorem autocorr_contDiff {φ : ℝ → ℝ} {s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 0 ≤ u₀) :
    ContDiff ℝ 2 (autocorr (twoBump φ u₀)) :=
  HasCompactSupport.contDiff_convolution_left _ (twoBump_hasCompactSupport hsupp hu)
    (twoBump_contDiff hφ u₀)
    (reflectFn_integrable (twoBump_integrable hφ hsupp hu)).locallyIntegrable

theorem autocorr_hasCompactSupport {φ : ℝ → ℝ} {s : ℝ}
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 0 ≤ u₀) :
    HasCompactSupport (autocorr (twoBump φ u₀)) :=
  (twoBump_hasCompactSupport hsupp hu).convolution _
    (reflectFn_hasCompactSupport (support_twoBump_subset hsupp hu))

/-! ## Fourier transforms -/

theorem paperFT_reflectFn (f : ℝ → ℝ) (z : ℂ) :
    Zeta23.paperFT (fun x => (reflectFn f x : ℂ)) z = Zeta23.paperFT (fun x => (f x : ℂ)) (-z) := by
  unfold Zeta23.paperFT reflectFn
  have h : (fun x : ℝ => (f (-x) : ℂ) * Complex.exp (I * z * x)) =
      fun x : ℝ => (fun y : ℝ => (f y : ℂ) * Complex.exp (I * (-z) * y)) (-x) := by
    funext x
    simp only []
    congr 1
    congr 1
    push_cast
    ring
  rw [h, integral_neg_eq_self (fun y : ℝ => (f y : ℂ) * Complex.exp (I * (-z) * y))]

theorem paperFT_autocorr {f : ℝ → ℝ} {a b : ℝ} (hf : Integrable f)
    (hsupp : Function.support f ⊆ Icc a b) (z : ℂ) :
    Zeta23.paperFT (fun x => (autocorr f x : ℂ)) z =
      Zeta23.paperFT (fun x => (f x : ℂ)) z * Zeta23.paperFT (fun x => (f x : ℂ)) (-z) := by
  unfold autocorr
  rw [paperFT_conv hf (reflectFn_integrable hf)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp)
    (reflectFn_hasCompactSupport hsupp), paperFT_reflectFn]

theorem support_translate_subset {φ : ℝ → ℝ} {s : ℝ} (hsupp : Function.support φ ⊆ Icc (-s) s)
    (c : ℝ) : Function.support (fun y => φ (y - c)) ⊆ Icc (-s + c) (s + c) := by
  intro y hy
  have := hsupp hy
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The Fourier transform of a translate. -/
theorem paperFT_translate (φ : ℝ → ℝ) (c : ℝ) (z : ℂ) :
    Zeta23.paperFT (fun y => (φ (y - c) : ℂ)) z =
      Complex.exp (I * z * c) * Zeta23.paperFT (fun x => (φ x : ℂ)) z := by
  unfold Zeta23.paperFT
  have h : (fun y : ℝ => (φ (y - c) : ℂ) * Complex.exp (I * z * y)) =
      fun y : ℝ => (fun t : ℝ => Complex.exp (I * z * c) * ((φ t : ℂ) * Complex.exp (I * z * t)))
        (y - c) := by
    funext y
    have e : Complex.exp (I * z * y) =
        Complex.exp (I * z * c) * Complex.exp (I * z * ((y - c : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    show (φ (y - c) : ℂ) * Complex.exp (I * z * y) =
      Complex.exp (I * z * c) * ((φ (y - c) : ℂ) * Complex.exp (I * z * ((y - c : ℝ) : ℂ)))
    rw [e]
    ring
  rw [h, integral_sub_right_eq_self (fun t : ℝ =>
    Complex.exp (I * z * c) * ((φ t : ℂ) * Complex.exp (I * z * t))) c, integral_const_mul]

theorem paperFT_twoBump {φ : ℝ → ℝ} {s : ℝ} (hφ : Integrable φ)
    (hsupp : Function.support φ ⊆ Icc (-s) s) (u₀ : ℝ) (z : ℂ) :
    Zeta23.paperFT (fun x => (twoBump φ u₀ x : ℂ)) z =
      Zeta23.paperFT (fun x => (φ x : ℂ)) z *
        (Complex.exp (I * z * (u₀ / 2)) - Complex.exp (-(I * z * (u₀ / 2)))) := by
  have h1 : Zeta23.paperFT (fun y => (φ (y - u₀ / 2) : ℂ)) z =
      Complex.exp (I * z * (u₀ / 2)) * Zeta23.paperFT (fun x => (φ x : ℂ)) z := by
    have := paperFT_translate φ (u₀ / 2) z
    push_cast at this
    exact this
  have h2 : Zeta23.paperFT (fun y => (φ (y + u₀ / 2) : ℂ)) z =
      Complex.exp (-(I * z * (u₀ / 2))) * Zeta23.paperFT (fun x => (φ x : ℂ)) z := by
    have := paperFT_translate φ (-(u₀ / 2)) z
    simp only [sub_neg_eq_add] at this
    rw [this]
    congr 2
    push_cast
    ring
  have hsub : Zeta23.paperFT (fun x => (twoBump φ u₀ x : ℂ)) z =
      Zeta23.paperFT (fun y => (φ (y - u₀ / 2) : ℂ)) z -
        Zeta23.paperFT (fun y => (φ (y + u₀ / 2) : ℂ)) z := by
    unfold Zeta23.paperFT twoBump
    rw [← integral_sub]
    · congr 1
      funext x
      push_cast
      ring
    · exact integrable_ofReal_mul_exp (hφ.comp_sub_right (u₀ / 2))
        (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
          (support_translate_subset hsupp (u₀ / 2))) z
    · have hsupp' : Function.support (fun y => φ (y + u₀ / 2)) ⊆
          Icc (-s + -(u₀ / 2)) (s + -(u₀ / 2)) := by
        have := support_translate_subset hsupp (-(u₀ / 2))
        simpa [sub_neg_eq_add] using this
      exact integrable_ofReal_mul_exp (hφ.comp_add_right (u₀ / 2))
        (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp') z
  rw [hsub, h1, h2]
  ring

theorem norm_paperFT_twoBump_le {φ : ℝ → ℝ} {s : ℝ} (hφ : Integrable φ)
    (hsupp : Function.support φ ⊆ Icc (-s) s) (u₀ : ℝ) (z : ℂ) :
    ‖Zeta23.paperFT (fun x => (twoBump φ u₀ x : ℂ)) z‖ ≤
      ‖Zeta23.paperFT (fun x => (φ x : ℂ)) z‖ * (2 * Real.cosh (u₀ / 2 * z.im)) := by
  rw [paperFT_twoBump hφ hsupp u₀ z, norm_mul]
  gcongr
  calc ‖Complex.exp (I * z * (u₀ / 2)) - Complex.exp (-(I * z * (u₀ / 2)))‖
      ≤ ‖Complex.exp (I * z * (u₀ / 2))‖ + ‖Complex.exp (-(I * z * (u₀ / 2)))‖ := norm_sub_le _ _
    _ = Real.exp (-(u₀ / 2 * z.im)) + Real.exp (u₀ / 2 * z.im) := by
        rw [Complex.norm_exp, Complex.norm_exp]
        congr 2
        · simp [Complex.mul_re, Complex.mul_im]; ring
        · simp [Complex.mul_re, Complex.mul_im]; ring
    _ = 2 * Real.cosh (u₀ / 2 * z.im) := by rw [Real.cosh_eq]; ring

/-! ## The autocorrelation at the separation -/

theorem mul_eq_zero_of_far {φ : ℝ → ℝ} {s : ℝ} (hsupp : Function.support φ ⊆ Icc (-s) s)
    {a b : ℝ} (hab : 2 * s < |a - b|) : φ a * φ b = 0 := by
  by_contra h
  have ha : φ a ≠ 0 := left_ne_zero_of_mul h
  have hb : φ b ≠ 0 := right_ne_zero_of_mul h
  have hA := hsupp (Function.mem_support.mpr ha)
  have hB := hsupp (Function.mem_support.mpr hb)
  have : |a - b| ≤ 2 * s := by
    rw [abs_le]; constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  linarith

theorem twoBump_mul_shift {φ : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 2 * s < u₀) (t : ℝ) :
    twoBump φ u₀ t * twoBump φ u₀ (t - u₀) = -(φ (t - u₀ / 2)) ^ 2 := by
  unfold twoBump
  have e1 : t - u₀ + u₀ / 2 = t - u₀ / 2 := by ring
  rw [e1]
  have h1 : φ (t - u₀ / 2) * φ (t - u₀ - u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t - u₀ / 2 - (t - u₀ - u₀ / 2) = u₀ by ring]; rw [abs_of_pos (by linarith)]; linarith)
  have h2 : φ (t + u₀ / 2) * φ (t - u₀ - u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t + u₀ / 2 - (t - u₀ - u₀ / 2) = 2 * u₀ by ring]; rw [abs_of_pos (by linarith)]; linarith)
  have h3 : φ (t + u₀ / 2) * φ (t - u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t + u₀ / 2 - (t - u₀ / 2) = u₀ by ring]; rw [abs_of_pos (by linarith)]; linarith)
  linear_combination h1 - h2 + h3

theorem twoBump_mul_shift' {φ : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 2 * s < u₀) (t : ℝ) :
    twoBump φ u₀ t * twoBump φ u₀ (t + u₀) = -(φ (t + u₀ / 2)) ^ 2 := by
  unfold twoBump
  have e1 : t + u₀ - u₀ / 2 = t + u₀ / 2 := by ring
  rw [e1]
  have h1 : φ (t - u₀ / 2) * φ (t + u₀ + u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t - u₀ / 2 - (t + u₀ + u₀ / 2) = -(2 * u₀) by ring]; rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have h2 : φ (t + u₀ / 2) * φ (t + u₀ + u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t + u₀ / 2 - (t + u₀ + u₀ / 2) = -u₀ by ring]; rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have h3 : φ (t - u₀ / 2) * φ (t + u₀ / 2) = 0 :=
    mul_eq_zero_of_far hsupp (by rw [show t - u₀ / 2 - (t + u₀ / 2) = -u₀ by ring]; rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  linear_combination h3 - h1 + h2

/-- `k(u₀) = −∫ φ²`. -/
theorem autocorr_twoBump_apply {φ : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 2 * s < u₀) :
    autocorr (twoBump φ u₀) u₀ = -∫ x, φ x ^ 2 := by
  unfold autocorr
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, reflectFn, neg_sub]
  have h : (fun t : ℝ => twoBump φ u₀ t * twoBump φ u₀ (t - u₀)) =
      fun t : ℝ => -((fun x : ℝ => φ x ^ 2) (t - u₀ / 2)) := by
    funext t
    exact twoBump_mul_shift hs hsupp hu t
  rw [h, integral_neg, integral_sub_right_eq_self (fun x : ℝ => φ x ^ 2) (u₀ / 2)]

/-- `k(−u₀) = −∫ φ²`. -/
theorem autocorr_twoBump_apply_neg {φ : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hsupp : Function.support φ ⊆ Icc (-s) s) {u₀ : ℝ} (hu : 2 * s < u₀) :
    autocorr (twoBump φ u₀) (-u₀) = -∫ x, φ x ^ 2 := by
  unfold autocorr
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, reflectFn, neg_sub]
  have h : (fun t : ℝ => twoBump φ u₀ t * twoBump φ u₀ (t - -u₀)) =
      fun t : ℝ => -((fun x : ℝ => φ x ^ 2) (t + u₀ / 2)) := by
    funext t
    rw [sub_neg_eq_add]
    exact twoBump_mul_shift' hs hsupp hu t
  rw [h, integral_neg, integral_add_right_eq_self (fun x : ℝ => φ x ^ 2) (u₀ / 2)]

end

end RHTower.WeilDeletion
