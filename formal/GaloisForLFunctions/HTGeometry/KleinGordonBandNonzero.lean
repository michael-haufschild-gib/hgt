import GaloisForLFunctions.HTGeometry.KleinGordonCircleMultiplier

/-!
# The band carries a nonzero state

The low-pass symbol is the indicator of a closed ball, which is compact and of positive measure, so it
is itself a nonzero element of `L²` fixed by multiplication by itself. Transporting it back through
the Fourier transform gives a nonzero element of `L²` fixed by the low-pass projection.

The eigenvectors exhibited for the Floquet theory are therefore nonzero, which is what the statements
requiring a nonvanishing datum — the unit-modulus law, the exact conservation, the flat envelope —
need in order to apply.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section BandNonzero

set_option maxHeartbeats 1000000 in
/-- **The band carries a nonzero state.** -/
theorem exists_ne_zero_kgLowPassOp_fixed [Nontrivial E] {R : ℝ} (hR : 0 < R) :
    ∃ z : Lp ℂ 2 (volume : Measure E), z ≠ 0 ∧ kgLowPassOp R z = z := by
  have hmeas : MeasurableSet (Metric.closedBall (0 : E) R) := measurableSet_closedBall
  have hfin : (volume : Measure E) (Metric.closedBall (0 : E) R) ≠ ⊤ :=
    ne_of_lt (IsCompact.measure_lt_top (isCompact_closedBall 0 R))
  have hpos : 0 < (volume : Measure E) (Metric.closedBall (0 : E) R) :=
    Metric.measure_closedBall_pos volume 0 hR
  have hmem : MemLp ((Metric.closedBall (0 : E) R).indicator fun _ => (1 : ℂ)) 2 volume :=
    memLp_indicator_const 2 hmeas 1 (Or.inr hfin)
  set f := hmem.toLp _ with hfdef
  -- the indicator is the low-pass symbol
  have hsym : ∀ ξ : E, (Metric.closedBall (0 : E) R).indicator (fun _ => (1 : ℂ)) ξ
      = kgLowPass R ξ := by
    classical
    intro ξ
    simp [Set.indicator_apply, Metric.mem_closedBall, dist_zero_right, kgLowPass]
  -- `f` is fixed by multiplication by the symbol
  have hMf : lpBoundedMulCLM (p := 2) (μ := (volume : Measure E))
      (measurable_kgLowPass (E := E) R) zero_le_one (norm_kgLowPass_le R) f = f := by
    refine Lp.ext ?_
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure E))
      (measurable_kgLowPass (E := E) R) zero_le_one (norm_kgLowPass_le R) f,
      hmem.coeFn_toLp] with ξ h1 h2
    rw [h1, h2, hsym, kgLowPass]
    split <;> simp
  -- `f` is nonzero
  have hfne : f ≠ 0 := by
    classical
    intro hzero
    have hae : (Metric.closedBall (0 : E) R).indicator (fun _ => (1 : ℂ)) =ᵐ[volume] 0 := by
      have h1 := hmem.coeFn_toLp
      rw [← hfdef, hzero] at h1
      exact h1.symm.trans (Lp.coeFn_zero ℂ 2 (volume : Measure E))
    have hsub : {ξ : E | ¬ ((Metric.closedBall (0 : E) R).indicator (fun _ => (1 : ℂ)) ξ
        = (0 : E → ℂ) ξ)} = Metric.closedBall (0 : E) R := by
      ext ξ
      simp [Set.indicator_apply]
    rw [Filter.EventuallyEq, ae_iff, hsub] at hae
    exact absurd hae (ne_of_gt hpos)
  refine ⟨fourierL2inv E f, ?_, ?_⟩
  · intro hzero
    apply hfne
    have hnorm : ‖fourierL2inv E f‖ = ‖f‖ := norm_fourierL2inv_apply f
    rw [hzero, norm_zero] at hnorm
    exact norm_eq_zero.mp hnorm.symm
  · rw [kgLowPassOp_eq, fourierMulCLM_apply]
    have hround : fourierL2 E (fourierL2inv E f) = f :=
      (Lp.fourierTransformₗᵢ E ℂ).apply_symm_apply f
    rw [hround, hMf]

end BandNonzero

end GaloisForLFunctions.HTGeometry
