import GaloisForLFunctions.HTGeometry.UnitIntervalFourierProjection

/-!
# The truncated-convolution form is continuous for the `L²` norm

On the unit interval the `L¹` norm is dominated by the `L²` norm, and the truncated convolution is
bounded by the supremum of its kernel times the `L¹` norms.  Together these make the quadratic form
`f ↦ ⟨f, A f⟩` Lipschitz on `L²` balls, which is what transports an `L²`-approximation of a ground
state into an approximation of its Rayleigh quotient.
-/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The `L¹` norm on the unit interval. -/
def l1Norm (f : ℝ → ℂ) : ℝ := ∫ x in (0 : ℝ)..1, ‖f x‖

theorem l1Norm_nonneg (f : ℝ → ℂ) : 0 ≤ l1Norm f := by
  rw [l1Norm]
  exact intervalIntegral.integral_nonneg (by norm_num) fun x _ => norm_nonneg _

/-- **Cauchy--Schwarz against the constant one.** -/
theorem l1Norm_sq_le_l2NormSq {f : ℝ → ℂ} (hf : Continuous f) :
    l1Norm f ^ 2 ≤ l2NormSq f := by
  set c : ℝ := l1Norm f with hc
  have hint : IntervalIntegrable (fun x : ℝ => (‖f x‖ - c) ^ 2) volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..1, (‖f x‖ - c) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => by positivity
  have hexp : (∫ x in (0 : ℝ)..1, (‖f x‖ - c) ^ 2)
      = l2NormSq f - 2 * c * l1Norm f + c ^ 2 := by
    have hsplit : ∀ x : ℝ, (‖f x‖ - c) ^ 2 = ‖f x‖ ^ 2 - 2 * c * ‖f x‖ + c ^ 2 := by
      intro x
      ring
    rw [intervalIntegral.integral_congr (fun x _ => hsplit x)]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub]
    · rw [l2NormSq, l1Norm, intervalIntegral.integral_const_mul]
      simp
    · exact (continuous_norm.comp hf).pow 2 |>.intervalIntegrable _ _
    · exact ((continuous_const.mul (continuous_norm.comp hf))).intervalIntegrable _ _
    · refine IntervalIntegrable.sub ?_ ?_
      · exact ((continuous_norm.comp hf).pow 2).intervalIntegrable _ _
      · exact ((continuous_const.mul (continuous_norm.comp hf))).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  rw [hexp, ← hc] at hnn
  nlinarith [hnn]

theorem l1Norm_le_sqrt_l2NormSq {f : ℝ → ℂ} (hf : Continuous f) :
    l1Norm f ≤ Real.sqrt (l2NormSq f) := by
  have h := l1Norm_sq_le_l2NormSq hf
  have hle : Real.sqrt (l1Norm f ^ 2) ≤ Real.sqrt (l2NormSq f) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (l1Norm_nonneg f)] at hle

/-- **The truncated-convolution pairing is bounded by the kernel bound times the `L¹` norms.** -/
theorem norm_l2Pair_truncConv_le {k : ℝ → ℝ} (hkc : Continuous k) {M : ℝ}
    (hM : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖k u‖ ≤ M) {f g : ℝ → ℂ} (hf : Continuous f)
    (hg : Continuous g) :
    ‖l2Pair f (truncConv k g)‖ ≤ M * (l1Norm f * l1Norm g) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hinner : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖truncConv k g x‖ ≤ M * l1Norm g := by
    intro x hx
    have hstep : ‖truncConv k g x‖ ≤ ∫ y in (0 : ℝ)..1, ‖((k (x - y) : ℝ) : ℂ) * g y‖ := by
      rw [truncConv]
      exact intervalIntegral.norm_integral_le_integral_norm h01
    refine hstep.trans ?_
    have hbound : ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖((k (x - y) : ℝ) : ℂ) * g y‖ ≤ M * ‖g y‖ := by
      intro y hy
      have hxy : x - y ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor <;> [linarith [hx.1, hy.2]; linarith [hx.2, hy.1]]
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (hM _ hxy) (norm_nonneg _)
    have hmono := intervalIntegral.integral_mono_on (μ := volume) h01
      (((Complex.continuous_ofReal.comp (hkc.comp (continuous_const.sub continuous_id))).mul
        hg).norm.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_norm.comp hg)).intervalIntegrable _ _) hbound
    refine hmono.trans ?_
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [intervalIntegral.integral_const_mul, l1Norm]
  have houter : ‖l2Pair f (truncConv k g)‖
      ≤ ∫ x in (0 : ℝ)..1, ‖(starRingEnd ℂ) (f x) * truncConv k g x‖ := by
    rw [l2Pair]
    exact intervalIntegral.norm_integral_le_integral_norm h01
  refine houter.trans ?_
  have hbound2 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖(starRingEnd ℂ) (f x) * truncConv k g x‖ ≤ (M * l1Norm g) * ‖f x‖ := by
    intro x hx
    rw [norm_mul, RCLike.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (hinner x hx) (norm_nonneg _)
  have hmono2 := intervalIntegral.integral_mono_on (μ := volume) h01
    ((hf.star.mul (continuous_truncConv hkc hg)).norm.intervalIntegrable _ _)
    ((continuous_const.mul (continuous_norm.comp hf)).intervalIntegrable _ _) hbound2
  refine hmono2.trans ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [intervalIntegral.integral_const_mul]
  simp only [l1Norm]
  exact le_of_eq (by ring)

theorem truncConv_sub {k : ℝ → ℝ} (hkc : Continuous k) {f g : ℝ → ℂ} (hf : Continuous f)
    (hg : Continuous g) (x : ℝ) :
    truncConv k (fun y => f y - g y) x = truncConv k f x - truncConv k g x := by
  rw [truncConv, truncConv, truncConv, ← intervalIntegral.integral_sub]
  · refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  · refine Continuous.intervalIntegrable ?_ _ _
    exact (Complex.continuous_ofReal.comp (hkc.comp (continuous_const.sub continuous_id))).mul hf
  · refine Continuous.intervalIntegrable ?_ _ _
    exact (Complex.continuous_ofReal.comp (hkc.comp (continuous_const.sub continuous_id))).mul hg

/-- **The truncated-convolution form is Lipschitz on `L²` balls.** -/
theorem norm_form_sub_le {k : ℝ → ℝ} (hkc : Continuous k) {M : ℝ}
    (hM : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖k u‖ ≤ M) {f g : ℝ → ℂ} (hf : Continuous f)
    (hg : Continuous g) :
    ‖l2Pair g (truncConv k g) - l2Pair f (truncConv k f)‖
      ≤ M * (Real.sqrt (l2NormSq fun x => g x - f x)) * Real.sqrt (l2NormSq g)
        + M * Real.sqrt (l2NormSq f) * (Real.sqrt (l2NormSq fun x => g x - f x)) := by
  have hd : Continuous fun x => g x - f x := hg.sub hf
  have hsplit : l2Pair g (truncConv k g) - l2Pair f (truncConv k f)
      = l2Pair (fun x => g x - f x) (truncConv k g)
        + l2Pair f (truncConv k fun x => g x - f x) := by
    have h1 : l2Pair (fun x => g x - f x) (truncConv k g)
        = l2Pair g (truncConv k g) - l2Pair f (truncConv k g) :=
      l2Pair_sub_left hg hf (continuous_truncConv hkc hg)
    have h2 : l2Pair f (truncConv k fun x => g x - f x)
        = l2Pair f (truncConv k g) - l2Pair f (truncConv k f) := by
      rw [← l2Pair_sub_right hf (continuous_truncConv hkc hg) (continuous_truncConv hkc hf)]
      refine congrArg (l2Pair f) ?_
      funext x
      exact truncConv_sub hkc hg hf x
    rw [h1, h2]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hb1 := norm_l2Pair_truncConv_le hkc hM hd hg
  have hb2 := norm_l2Pair_truncConv_le hkc hM hf hd
  have hMnn : 0 ≤ M := by
    have h0 : ‖k 0‖ ≤ M := hM 0 ⟨by norm_num, by norm_num⟩
    exact le_trans (norm_nonneg _) h0
  have hc1 : M * (l1Norm (fun x => g x - f x) * l1Norm g)
      ≤ M * Real.sqrt (l2NormSq fun x => g x - f x) * Real.sqrt (l2NormSq g) := by
    have h1 := l1Norm_le_sqrt_l2NormSq hd
    have h2 := l1Norm_le_sqrt_l2NormSq hg
    have := mul_le_mul h1 h2 (l1Norm_nonneg g) (Real.sqrt_nonneg _)
    nlinarith [l1Norm_nonneg (fun x => g x - f x), l1Norm_nonneg g, Real.sqrt_nonneg
      (l2NormSq fun x => g x - f x), Real.sqrt_nonneg (l2NormSq g)]
  have hc2 : M * (l1Norm f * l1Norm (fun x => g x - f x))
      ≤ M * Real.sqrt (l2NormSq f) * Real.sqrt (l2NormSq fun x => g x - f x) := by
    have h1 := l1Norm_le_sqrt_l2NormSq hf
    have h2 := l1Norm_le_sqrt_l2NormSq hd
    have := mul_le_mul h1 h2 (l1Norm_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [l1Norm_nonneg f, l1Norm_nonneg (fun x => g x - f x), Real.sqrt_nonneg (l2NormSq f),
      Real.sqrt_nonneg (l2NormSq fun x => g x - f x)]
  linarith [hb1.trans hc1, hb2.trans hc2]

end

end GaloisForLFunctions.HTGeometry
