import GaloisForLFunctions.HTGeometry.LocalSamplingForCompactlySupportedSources
import GaloisForLFunctions.HTGeometry.LogarithmicDensitySamplingSums

/-!
# Plancherel–Pólya with a logarithmic weight

A transform of a source supported in `[−a, a]`, sampled on a point set whose count in the unit
window at height `n` is at most `A₀ log(|n|+3)`, obeys

`Σ_{x ∈ T} ‖Φ(x)‖² ≤ C(a) A₀ ∫ ‖Φ(y)‖² log(|y|+3) dy`.

So a logarithmic sampling density costs exactly the logarithmic weight on the right — the
weight that is the archimedean energy of the Weil form — and nothing more.  The proof composes
the localised sampling bound (reproducing kernel of quadratic decay) with the fact that a
quadratically decaying kernel reproduces a logarithmic density.
-/

open MeasureTheory Set Real Complex
open scoped FourierTransform

namespace GaloisForLFunctions.HTGeometry.LocalSampling

noncomputable section
set_option autoImplicit false

/-! ## The constant of the integer sum -/

/-- The constant in `Σ_{n ∈ ℤ} log(|n|+3)(1+(n−x)²)⁻¹ ≤ C log(|x|+3)`. -/
def logKernelConst : ℝ := LogDensity.exists_bound_tsum_log_kernel.choose

theorem logKernelConst_nonneg : 0 ≤ logKernelConst :=
  LogDensity.exists_bound_tsum_log_kernel.choose_spec.1

theorem tsum_log_kernel_le (x : ℝ) :
    ∑' n : ℤ, Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ ≤
      logKernelConst * Real.log (|x| + 3) :=
  LogDensity.exists_bound_tsum_log_kernel.choose_spec.2 x

/-! ## From a logarithmic density to the logarithmic weight -/

/-- Inside one unit window the kernel changes by at most a factor three. -/
theorem kernel_window_le {n : ℤ} {x y : ℝ} (hx : (n : ℝ) ≤ x) (hx' : x ≤ (n : ℝ) + 1) :
    (1 + (x - y) ^ 2)⁻¹ ≤ 3 * (1 + ((n : ℝ) - y) ^ 2)⁻¹ := by
  have hkey : 1 + ((n : ℝ) - y) ^ 2 ≤ 3 * (1 + (x - y) ^ 2) := by
    nlinarith [sq_nonneg ((x - y) - 1), sq_nonneg ((x - y) + 1), sq_nonneg (x - (n : ℝ))]
  have ha : (0:ℝ) < (1 + ((n : ℝ) - y) ^ 2) / 3 := by positivity
  calc (1 + (x - y) ^ 2)⁻¹ = 1 / (1 + (x - y) ^ 2) := (one_div _).symm
    _ ≤ 1 / ((1 + ((n : ℝ) - y) ^ 2) / 3) := one_div_le_one_div_of_le ha (by linarith)
    _ = 3 * (1 + ((n : ℝ) - y) ^ 2)⁻¹ := by field_simp

/-- **A logarithmic sampling density is reproduced by the kernel.**  The kernel summed over a
finite point set with at most `A₀ log(|n|+3)` points per unit window is `≲ A₀ log(|y|+3)`. -/
theorem sum_kernel_le {A₀ : ℝ} (hA₀ : 0 ≤ A₀) (T : Finset ℝ)
    (hcount : ∀ n : ℤ, ((T.filter fun x => (n : ℝ) ≤ x ∧ x ≤ (n : ℝ) + 1).card : ℝ) ≤
      A₀ * Real.log (|(n : ℝ)| + 3)) (y : ℝ) :
    ∑ x ∈ T, (1 + (x - y) ^ 2)⁻¹ ≤ 3 * A₀ * logKernelConst * Real.log (|y| + 3) := by
  classical
  have hmaps : ∀ x ∈ T, (⌊x⌋ : ℤ) ∈ T.image fun x => (⌊x⌋ : ℤ) := fun x hx =>
    Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hnonneg : ∀ n : ℤ, 0 ≤ Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - y) ^ 2)⁻¹ := by
    intro n
    exact mul_nonneg (Real.log_nonneg (by linarith [abs_nonneg ((n : ℝ))])) (by positivity)
  have hfib : ∀ n ∈ T.image fun x => (⌊x⌋ : ℤ),
      ∑ x ∈ T.filter fun x => (⌊x⌋ : ℤ) = n, (1 + (x - y) ^ 2)⁻¹ ≤
        3 * A₀ * (Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - y) ^ 2)⁻¹) := by
    intro n _
    have hsub : (T.filter fun x => (⌊x⌋ : ℤ) = n) ⊆
        T.filter fun x => (n : ℝ) ≤ x ∧ x ≤ (n : ℝ) + 1 := by
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      refine ⟨hx.1, ?_, ?_⟩
      · rw [← hx.2]; exact Int.floor_le x
      · rw [← hx.2]; linarith [Int.lt_floor_add_one x]
    have hcard : (((T.filter fun x => (⌊x⌋ : ℤ) = n).card : ℝ)) ≤
        A₀ * Real.log (|(n : ℝ)| + 3) :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) (hcount n)
    have hterm : ∀ x ∈ T.filter fun x => (⌊x⌋ : ℤ) = n,
        (1 + (x - y) ^ 2)⁻¹ ≤ 3 * (1 + ((n : ℝ) - y) ^ 2)⁻¹ := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      refine kernel_window_le ?_ ?_
      · rw [← hx.2]; exact Int.floor_le x
      · rw [← hx.2]; linarith [Int.lt_floor_add_one x]
    calc ∑ x ∈ T.filter fun x => (⌊x⌋ : ℤ) = n, (1 + (x - y) ^ 2)⁻¹
        ≤ ∑ _x ∈ T.filter fun x => (⌊x⌋ : ℤ) = n, 3 * (1 + ((n : ℝ) - y) ^ 2)⁻¹ :=
          Finset.sum_le_sum hterm
      _ = ((T.filter fun x => (⌊x⌋ : ℤ) = n).card : ℝ) * (3 * (1 + ((n : ℝ) - y) ^ 2)⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A₀ * Real.log (|(n : ℝ)| + 3)) * (3 * (1 + ((n : ℝ) - y) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 3 * A₀ * (Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - y) ^ 2)⁻¹) := by ring
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  have hfin : ∑ n ∈ T.image fun x => (⌊x⌋ : ℤ),
      Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - y) ^ 2)⁻¹ ≤
      ∑' n : ℤ, Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - y) ^ 2)⁻¹ :=
    Summable.sum_le_tsum _ (fun n _ => hnonneg n) (LogDensity.summable_log_kernel y)
  calc 3 * A₀ * ∑ n ∈ T.image fun x => (⌊x⌋ : ℤ),
        Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - y) ^ 2)⁻¹
      ≤ 3 * A₀ * ∑' n : ℤ, Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - y) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ ≤ 3 * A₀ * (logKernelConst * Real.log (|y| + 3)) :=
        mul_le_mul_of_nonneg_left (tsum_log_kernel_le y) (by positivity)
    _ = 3 * A₀ * logKernelConst * Real.log (|y| + 3) := by ring

/-! ## The weighted sampling inequality -/

/-- **Plancherel–Pólya with a logarithmic weight.**  For a source supported in `[−a, a]`, the
transform sampled on a point set of logarithmic density `A₀` is bounded by the logarithmically
weighted energy of the transform — the archimedean weight — with constant linear in `A₀`. -/
theorem sum_norm_sq_fourier_le {a A₀ : ℝ} (ha : 0 < a) (hA₀ : 0 ≤ A₀) {f : ℝ → ℂ}
    (hf : Integrable f) (hsupp : ∀ t : ℝ, a < |t| → f t = 0)
    (hint : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3))
    (T : Finset ℝ)
    (hcount : ∀ n : ℤ, ((T.filter fun x => (n : ℝ) ≤ x ∧ x ≤ (n : ℝ) + 1).card : ℝ) ≤
      A₀ * Real.log (|(n : ℝ)| + 3)) :
    ∑ x ∈ T, ‖𝓕 f x‖ ^ 2 ≤
      (((8 * a + a⁻¹) * π) * ((8 * a + a⁻¹) * (3 * A₀ * logKernelConst))) *
        ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3) := by
  classical
  have hM : (0:ℝ) ≤ (8 * a + a⁻¹) * π := by positivity
  have hK : (0:ℝ) ≤ 8 * a + a⁻¹ := by positivity
  have hΦc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hf
  have hlog1 : ∀ y : ℝ, (1:ℝ) ≤ Real.log (|y| + 3) := by
    intro y
    have hlog3 : (1:ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_three]
    refine hlog3.trans (Real.log_le_log (by norm_num) ?_)
    linarith [abs_nonneg y]
  -- the unweighted energy is integrable, the logarithm being at least one
  have hΦ2 : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2 := by
    refine Integrable.mono' hint (hΦc.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hlog1 y, sq_nonneg ‖𝓕 f y‖]
  -- the kernel-weighted energies, one per sample point
  have hker : ∀ x₀ : ℝ, Integrable fun y : ℝ => ‖sampKernel a (x₀ - y)‖ * ‖𝓕 f y‖ ^ 2 := by
    intro x₀
    have hGc : Continuous fun y : ℝ => sampKernel a (x₀ - y) :=
      (continuous_sampKernel ha).comp (continuous_const.sub continuous_id)
    refine Integrable.mono' (hΦ2.const_mul (8 * a + a⁻¹))
      (hGc.norm.mul (hΦc.norm.pow 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb : ‖sampKernel a (x₀ - y)‖ ≤ (8 * a + a⁻¹) / (1 + (x₀ - y) ^ 2) :=
      norm_sampKernel_le ha _
    have hb' : ‖sampKernel a (x₀ - y)‖ ≤ 8 * a + a⁻¹ := by
      refine hb.trans ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (x₀ - y)]
    exact mul_le_mul_of_nonneg_right hb' (by positivity)
  -- each sample point costs the kernel average, and the kernel decays quadratically
  have hpt : ∀ x₀ : ℝ, ‖𝓕 f x₀‖ ^ 2 ≤ ((8 * a + a⁻¹) * π) * ((8 * a + a⁻¹) *
      ∫ y : ℝ, (1 + (x₀ - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) := by
    intro x₀
    have h1 := norm_sq_fourier_le_integral ha hf hsupp x₀ (hker x₀)
    have hmono : (∫ y : ℝ, ‖sampKernel a (x₀ - y)‖ * ‖𝓕 f y‖ ^ 2) ≤
        (8 * a + a⁻¹) * ∫ y : ℝ, (1 + (x₀ - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2 := by
      have hmeas : Measurable fun y : ℝ => (1 + (x₀ - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2 :=
        ((measurable_const.add ((measurable_const.sub measurable_id).pow_const 2)).inv).mul
          ((hΦc.norm.pow 2).measurable)
      have hdom : Integrable fun y : ℝ => (1 + (x₀ - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2 := by
        refine Integrable.mono' hΦ2 hmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hk1 : (1 + (x₀ - y) ^ 2)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          right
          nlinarith [sq_nonneg (x₀ - y)]
        nlinarith [hk1, sq_nonneg ‖𝓕 f y‖]
      rw [← MeasureTheory.integral_const_mul]
      refine integral_mono (hker x₀) (hdom.const_mul _) fun y => ?_
      have hb : ‖sampKernel a (x₀ - y)‖ ≤ (8 * a + a⁻¹) / (1 + (x₀ - y) ^ 2) :=
        norm_sampKernel_le ha _
      have heq : (8 * a + a⁻¹) / (1 + (x₀ - y) ^ 2) =
          (8 * a + a⁻¹) * (1 + (x₀ - y) ^ 2)⁻¹ := by ring
      rw [heq] at hb
      calc ‖sampKernel a (x₀ - y)‖ * ‖𝓕 f y‖ ^ 2
          ≤ ((8 * a + a⁻¹) * (1 + (x₀ - y) ^ 2)⁻¹) * ‖𝓕 f y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = (8 * a + a⁻¹) * ((1 + (x₀ - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) := by ring
    exact h1.trans (mul_le_mul_of_nonneg_left hmono hM)
  -- sum over the sample points and exchange the finite sum with the integral
  have hsum : ∑ x ∈ T, ‖𝓕 f x‖ ^ 2 ≤ ((8 * a + a⁻¹) * π) * ((8 * a + a⁻¹) *
      ∑ x ∈ T, ∫ y : ℝ, (1 + (x - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) := by
    have := Finset.sum_le_sum fun x (_ : x ∈ T) => hpt x
    rw [← Finset.mul_sum, ← Finset.mul_sum] at this
    exact this
  have hdomall : ∀ x : ℝ, Integrable fun y : ℝ => (1 + (x - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2 := by
    intro x
    have hmeas : Measurable fun y : ℝ => (1 + (x - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2 :=
      ((measurable_const.add ((measurable_const.sub measurable_id).pow_const 2)).inv).mul
        ((hΦc.norm.pow 2).measurable)
    refine Integrable.mono' hΦ2 hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hk1 : (1 + (x - y) ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      nlinarith [sq_nonneg (x - y)]
    nlinarith [hk1, sq_nonneg ‖𝓕 f y‖]
  have hexch : ∑ x ∈ T, ∫ y : ℝ, (1 + (x - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2 =
      ∫ y : ℝ, ∑ x ∈ T, (1 + (x - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2 :=
    (MeasureTheory.integral_finsetSum T fun x _ => hdomall x).symm
  have hinner : (∫ y : ℝ, ∑ x ∈ T, (1 + (x - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) ≤
      (3 * A₀ * logKernelConst) * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3) := by
    have hL : Integrable fun y : ℝ => ∑ x ∈ T, (1 + (x - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2 :=
      integrable_finsetSum T fun x _ => hdomall x
    rw [← MeasureTheory.integral_const_mul]
    refine integral_mono hL (hint.const_mul _) fun y => ?_
    have hker := sum_kernel_le hA₀ T hcount y
    have hfactor : ∑ x ∈ T, (1 + (x - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2 =
        (∑ x ∈ T, (1 + (x - y) ^ 2)⁻¹) * ‖𝓕 f y‖ ^ 2 := by
      rw [Finset.sum_mul]
    rw [hfactor]
    calc (∑ x ∈ T, (1 + (x - y) ^ 2)⁻¹) * ‖𝓕 f y‖ ^ 2
        ≤ (3 * A₀ * logKernelConst * Real.log (|y| + 3)) * ‖𝓕 f y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hker (by positivity)
      _ = 3 * A₀ * logKernelConst * (‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) := by ring
  calc ∑ x ∈ T, ‖𝓕 f x‖ ^ 2
      ≤ ((8 * a + a⁻¹) * π) * ((8 * a + a⁻¹) *
          ∑ x ∈ T, ∫ y : ℝ, (1 + (x - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) := hsum
    _ = ((8 * a + a⁻¹) * π) * ((8 * a + a⁻¹) *
          ∫ y : ℝ, ∑ x ∈ T, (1 + (x - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) := by rw [hexch]
    _ ≤ ((8 * a + a⁻¹) * π) * ((8 * a + a⁻¹) *
          ((3 * A₀ * logKernelConst) * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hK) hM
    _ = (((8 * a + a⁻¹) * π) * ((8 * a + a⁻¹) * (3 * A₀ * logKernelConst))) *
          ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3) := by ring

end

end GaloisForLFunctions.HTGeometry.LocalSampling
