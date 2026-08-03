import GaloisForLFunctions.HTGeometry.ClockNullFoliationRiccati

/-!
# The Volterra operator of a clock kernel

The characteristic form of the two-dimensional clock equation is `∂ξ∂η u = K u`. Integrating once
in `η` turns it into an ordinary differential equation in `ξ` whose values are functions of `η`:

`∂ξ U(ξ) = A(ξ) U(ξ)`,  `(A(ξ) v)(η) = ∫_b^η K(ξ,t) v(t) dt`.

This file builds the operator `A(ξ)` on the Banach space of bounded continuous functions, with the
interval of integration clamped to a fixed compact range so that the operator is bounded. The two
estimates proved here — the norm bound and the Lipschitz estimate — are exactly the hypotheses
that the Picard–Lindelöf structure of mathlib requires of a vector field.
-/

namespace GaloisForLFunctions.HTGeometry

open Set intervalIntegral MeasureTheory

/-! ## Clamping to a compact interval -/

/-- Clamp a real to a compact interval. -/
noncomputable def clampTo (b b' η : ℝ) : ℝ := min (max η b) b'

theorem continuous_clampTo (b b' : ℝ) : Continuous (clampTo b b') := by
  unfold clampTo
  fun_prop

theorem clampTo_mem {b b' : ℝ} (h : b ≤ b') (η : ℝ) : clampTo b b' η ∈ Icc b b' := by
  constructor
  · exact le_min (le_max_right _ _) h
  · exact min_le_right _ _

theorem clampTo_of_mem {b b' η : ℝ} (h : η ∈ Icc b b') : clampTo b b' η = η := by
  obtain ⟨h1, h2⟩ := h
  rw [clampTo, max_eq_left h1, min_eq_left h2]

/-! ## The integral operator -/

/-- The Volterra integral operator of a kernel, clamped to `[b, b']`. -/
noncomputable def volterraFun (K : ℝ → ℝ) (b b' : ℝ) (U : ℝ → ℝ) : ℝ → ℝ :=
  fun η => ∫ t in b..clampTo b b' η, K t * U t

theorem continuous_primitive_of_continuous {a : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous fun u : ℝ => ∫ t in a..u, g t :=
  Differentiable.continuous fun x =>
    (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable a x)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt).differentiableAt

theorem continuous_volterraFun {K U : ℝ → ℝ} (hK : Continuous K) (hU : Continuous U)
    (b b' : ℝ) : Continuous (volterraFun K b b' U) :=
  (continuous_primitive_of_continuous (hK.mul hU)).comp (continuous_clampTo b b')

/-- **The operator is bounded by the kernel bound times the length of the interval.** -/
theorem abs_volterraFun_le {b b' : ℝ} (hbb : b ≤ b') {K U : ℝ → ℝ} {M C : ℝ}
    (hM : ∀ t ∈ Icc b b', |K t| ≤ M) (hC : ∀ t, |U t| ≤ C) (hM0 : 0 ≤ M) (hC0 : 0 ≤ C)
    (η : ℝ) : |volterraFun K b b' U η| ≤ M * C * (b' - b) := by
  have hmem := clampTo_mem hbb η
  have hle : b ≤ clampTo b b' η := hmem.1
  have hbound : ∀ t ∈ uIoc b (clampTo b b' η), ‖K t * U t‖ ≤ M * C := by
    intro t ht
    rw [uIoc_of_le hle] at ht
    have htmem : t ∈ Icc b b' := ⟨le_of_lt ht.1, le_trans ht.2 hmem.2⟩
    have h1 : |K t| ≤ M := hM t htmem
    have h2 : |U t| ≤ C := hC t
    calc ‖K t * U t‖ = |K t| * |U t| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ M * C := by
          refine mul_le_mul h1 h2 (abs_nonneg _) hM0
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hlen : |clampTo b b' η - b| ≤ b' - b := by
    rw [abs_of_nonneg (by linarith [hmem.1])]
    linarith [hmem.2]
  calc |volterraFun K b b' U η| = ‖∫ t in b..clampTo b b' η, K t * U t‖ := by
        rw [volterraFun, Real.norm_eq_abs]
    _ ≤ M * C * |clampTo b b' η - b| := hint
    _ ≤ M * C * (b' - b) := by
        refine mul_le_mul_of_nonneg_left hlen (mul_nonneg hM0 hC0)

/-- **The Lipschitz estimate.** -/
theorem abs_volterraFun_sub_le {b b' : ℝ} (hbb : b ≤ b') {K U V : ℝ → ℝ} {M C : ℝ}
    (hK : Continuous K) (hU : Continuous U) (hV : Continuous V)
    (hM : ∀ t ∈ Icc b b', |K t| ≤ M) (hC : ∀ t, |U t - V t| ≤ C) (hM0 : 0 ≤ M)
    (hC0 : 0 ≤ C) (η : ℝ) :
    |volterraFun K b b' U η - volterraFun K b b' V η| ≤ M * C * (b' - b) := by
  have hiU : IntervalIntegrable (fun t => K t * U t) volume b (clampTo b b' η) :=
    (hK.mul hU).intervalIntegrable _ _
  have hiV : IntervalIntegrable (fun t => K t * V t) volume b (clampTo b b' η) :=
    (hK.mul hV).intervalIntegrable _ _
  have hsub : volterraFun K b b' U η - volterraFun K b b' V η
      = ∫ t in b..clampTo b b' η, K t * (U t - V t) := by
    rw [volterraFun, volterraFun, ← intervalIntegral.integral_sub hiU hiV]
    refine intervalIntegral.integral_congr ?_
    intro t _
    ring
  rw [hsub]
  have h := abs_volterraFun_le (b := b) (b' := b') hbb (K := K) (U := fun t => U t - V t)
    hM hC hM0 hC0 η
  rw [volterraFun] at h
  exact h

/-! ## The operator on bounded continuous functions -/

/-- The Volterra operator as a bounded continuous function. -/
noncomputable def volterraBCF {b b' : ℝ} (hbb : b ≤ b') {K : ℝ → ℝ} (hK : Continuous K)
    {M : ℝ} (hM : ∀ t ∈ Icc b b', |K t| ≤ M) (hM0 : 0 ≤ M)
    (U : BoundedContinuousFunction ℝ ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (volterraFun K b b' U)
    (continuous_volterraFun hK U.continuous b b') (M * ‖U‖ * (b' - b))
    (fun η => by
      rw [Real.norm_eq_abs]
      exact abs_volterraFun_le hbb hM
        (fun t => by
          rw [← Real.norm_eq_abs]
          exact U.norm_coe_le_norm t)
        hM0 (norm_nonneg U) η)

theorem volterraBCF_apply {b b' : ℝ} (hbb : b ≤ b') {K : ℝ → ℝ} (hK : Continuous K)
    {M : ℝ} (hM : ∀ t ∈ Icc b b', |K t| ≤ M) (hM0 : 0 ≤ M)
    (U : BoundedContinuousFunction ℝ ℝ) (η : ℝ) :
    volterraBCF hbb hK hM hM0 U η = volterraFun K b b' U η := rfl

/-- **The operator norm bound**, in the form the Picard–Lindelöf structure asks for. -/
theorem norm_volterraBCF_le {b b' : ℝ} (hbb : b ≤ b') {K : ℝ → ℝ} (hK : Continuous K)
    {M : ℝ} (hM : ∀ t ∈ Icc b b', |K t| ≤ M) (hM0 : 0 ≤ M)
    (U : BoundedContinuousFunction ℝ ℝ) :
    ‖volterraBCF hbb hK hM hM0 U‖ ≤ M * (b' - b) * ‖U‖ := by
  have hnn : (0 : ℝ) ≤ M * (b' - b) * ‖U‖ :=
    mul_nonneg (mul_nonneg hM0 (by linarith)) (norm_nonneg U)
  refine (BoundedContinuousFunction.norm_le hnn).2 fun η => ?_
  rw [Real.norm_eq_abs, volterraBCF_apply]
  have h := abs_volterraFun_le hbb hM
    (fun t => by
      rw [← Real.norm_eq_abs]
      exact U.norm_coe_le_norm t)
    hM0 (norm_nonneg U) η
  calc |volterraFun K b b' U η| ≤ M * ‖U‖ * (b' - b) := h
    _ = M * (b' - b) * ‖U‖ := by ring

/-- **The Lipschitz bound**, in the form the Picard–Lindelöf structure asks for. -/
theorem dist_volterraBCF_le {b b' : ℝ} (hbb : b ≤ b') {K : ℝ → ℝ} (hK : Continuous K)
    {M : ℝ} (hM : ∀ t ∈ Icc b b', |K t| ≤ M) (hM0 : 0 ≤ M)
    (U V : BoundedContinuousFunction ℝ ℝ) :
    ‖volterraBCF hbb hK hM hM0 U - volterraBCF hbb hK hM hM0 V‖ ≤ M * (b' - b) * ‖U - V‖ := by
  have hnn : (0 : ℝ) ≤ M * (b' - b) * ‖U - V‖ :=
    mul_nonneg (mul_nonneg hM0 (by linarith)) (norm_nonneg (U - V))
  refine (BoundedContinuousFunction.norm_le hnn).2 fun η => ?_
  have hdiff :
      (volterraBCF hbb hK hM hM0 U - volterraBCF hbb hK hM hM0 V) η
        = volterraFun K b b' U η - volterraFun K b b' V η := rfl
  rw [hdiff, Real.norm_eq_abs]
  have hCsub : ∀ t : ℝ, |U t - V t| ≤ ‖U - V‖ := by
    intro t
    rw [← Real.norm_eq_abs]
    have : (U - V) t = U t - V t := rfl
    rw [← this]
    exact (U - V).norm_coe_le_norm t
  have h := abs_volterraFun_sub_le hbb hK U.continuous V.continuous hM hCsub hM0
    (norm_nonneg (U - V)) η
  calc |volterraFun K b b' U η - volterraFun K b b' V η| ≤ M * ‖U - V‖ * (b' - b) := h
    _ = M * (b' - b) * ‖U - V‖ := by ring

end GaloisForLFunctions.HTGeometry
