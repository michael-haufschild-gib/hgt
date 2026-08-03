import GaloisForLFunctions.HTGeometry.ClockVolterraParameter

/-!
# The characteristic ODE has a local solution

The three estimates of the previous files are exactly the hypotheses that mathlib's Picard–Lindelöf
structure asks of a vector field. Assembling them — the only remaining condition being that the
interval of the characteristic parameter be short enough — gives a local solution of

`∂ξ U(ξ) = A(ξ) U(ξ)`,  `U(ξ₀) = 1`,

with values in the Banach space of bounded continuous functions of the second null coordinate. This
is the analytic content of Riemann's method for the Goursat problem.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Metric MeasureTheory

/-! ## Bounds for the vector field -/

theorem norm_goursatBCF_le (K : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hbb : b ≤ b') (hcc : c ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M) (ξ : ℝ)
    (U : BoundedContinuousFunction ℝ ℝ) :
    ‖goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ U‖ ≤ M * (b' - b) * ‖U‖ := by
  have hnn : (0 : ℝ) ≤ M * (b' - b) * ‖U‖ :=
    mul_nonneg (mul_nonneg hM0 (by linarith)) (norm_nonneg U)
  refine (BoundedContinuousFunction.norm_le hnn).2 fun η => ?_
  rw [Real.norm_eq_abs, goursatBCF_apply]
  have h := abs_volterraFun_le hbb (fun t ht => hM _ (clampTo_mem hcc ξ) t ht)
    (fun t => by
      rw [← Real.norm_eq_abs]
      exact U.norm_coe_le_norm t)
    hM0 (norm_nonneg U) η
  calc |volterraFun (K (clampTo c c' ξ)) b b' U η| ≤ M * ‖U‖ * (b' - b) := h
    _ = M * (b' - b) * ‖U‖ := by ring

theorem dist_goursatBCF_le (K : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hbb : b ≤ b') (hcc : c ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M) (ξ : ℝ)
    (U V : BoundedContinuousFunction ℝ ℝ) :
    dist (goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ U)
        (goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ V)
      ≤ M * (b' - b) * dist U V := by
  have hnn : (0 : ℝ) ≤ M * (b' - b) * ‖U - V‖ :=
    mul_nonneg (mul_nonneg hM0 (by linarith)) (norm_nonneg _)
  simp only [dist_eq_norm]
  refine (BoundedContinuousFunction.norm_le hnn).2 fun η => ?_
  have hval : (goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ U
      - goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ V) η
      = volterraFun (K (clampTo c c' ξ)) b b' U η
        - volterraFun (K (clampTo c c' ξ)) b b' V η := rfl
  rw [hval, Real.norm_eq_abs]
  have hCsub : ∀ t : ℝ, |U t - V t| ≤ ‖U - V‖ := by
    intro t
    have hUV : (U - V) t = U t - V t := rfl
    rw [← Real.norm_eq_abs, ← hUV]
    exact (U - V).norm_coe_le_norm t
  have h := abs_volterraFun_sub_le hbb (continuous_kernel_slice hK _) U.continuous V.continuous
    (fun t ht => hM _ (clampTo_mem hcc ξ) t ht) hCsub hM0 (norm_nonneg (U - V)) η
  calc |volterraFun (K (clampTo c c' ξ)) b b' U η
        - volterraFun (K (clampTo c c' ξ)) b b' V η| ≤ M * ‖U - V‖ * (b' - b) := h
    _ = M * (b' - b) * ‖U - V‖ := by ring

/-! ## The Picard–Lindelöf hypotheses -/

/-- **Local solvability of the characteristic ODE.** -/
theorem exists_goursat_solution (K : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hbb : b ≤ b') (hcc : c ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M) (ξ₀ : ℝ) :
    ∃ h : ℝ, 0 < h ∧ ∃ α : ℝ → BoundedContinuousFunction ℝ ℝ,
      α ξ₀ = BoundedContinuousFunction.const ℝ (1 : ℝ) ∧
        ∀ ξ ∈ Icc (ξ₀ - h) (ξ₀ + h),
          HasDerivWithinAt α (goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ (α ξ))
            (Icc (ξ₀ - h) (ξ₀ + h)) ξ := by
  classical
  set x₀ : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.const ℝ (1 : ℝ) with hx₀
  set Mb : ℝ := M * (b' - b) with hMb
  have hMb0 : 0 ≤ Mb := mul_nonneg hM0 (by linarith)
  set Lr : ℝ := Mb * (‖x₀‖ + 1) with hLr
  have hLr0 : 0 ≤ Lr := mul_nonneg hMb0 (by positivity)
  set h : ℝ := 1 / (Lr + 1) with hhdef
  have hh : 0 < h := by
    rw [hhdef]
    positivity
  refine ⟨h, hh, ?_⟩
  have hmem : ξ₀ ∈ Icc (ξ₀ - h) (ξ₀ + h) := ⟨by linarith, by linarith⟩
  set t₀ : Icc (ξ₀ - h) (ξ₀ + h) := ⟨ξ₀, hmem⟩ with ht₀
  have hPL : IsPicardLindelof
      (fun ξ U => goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ U) t₀ x₀ 1 0
      (Real.toNNReal Lr) (Real.toNNReal Mb) := by
    constructor
    · intro ξ _
      refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun U V => ?_)
      rw [Real.coe_toNNReal Mb hMb0]
      exact dist_goursatBCF_le K b b' c c' M hK hbb hcc hM0 hM ξ U V
    · intro U _
      exact (continuous_goursatBCF K b b' c c' M hK hbb hcc hM0 hM U).continuousOn
    · intro ξ _ U hU
      have hd : dist U x₀ ≤ 1 := by
        have := hU
        rw [mem_closedBall] at this
        simpa using this
      have hUn : ‖U‖ ≤ ‖x₀‖ + 1 := by
        have hsub := norm_sub_norm_le U x₀
        rw [← dist_eq_norm] at hsub
        linarith
      rw [Real.coe_toNNReal Lr hLr0]
      calc ‖goursatBCF K b b' c c' M hK hbb hcc hM0 hM ξ U‖ ≤ Mb * ‖U‖ :=
            norm_goursatBCF_le K b b' c c' M hK hbb hcc hM0 hM ξ U
        _ ≤ Mb * (‖x₀‖ + 1) := mul_le_mul_of_nonneg_left hUn hMb0
        _ = Lr := by rw [hLr]
    · have hmax : max ((ξ₀ + h) - (t₀ : ℝ)) ((t₀ : ℝ) - (ξ₀ - h)) = h := by
        rw [ht₀]
        simp only []
        rw [show ξ₀ + h - ξ₀ = h by ring, show ξ₀ - (ξ₀ - h) = h by ring, max_self]
      rw [hmax, Real.coe_toNNReal Lr hLr0]
      have hle : Lr * h ≤ 1 := by
        rw [hhdef, mul_one_div, div_le_one (by linarith)]
        linarith
      calc Lr * h ≤ 1 := hle
        _ = ((1 : NNReal) : ℝ) - ((0 : NNReal) : ℝ) := by norm_num
  obtain ⟨α, hα0, hαd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, hαd⟩

end GaloisForLFunctions.HTGeometry
