import GaloisForLFunctions.RHTower.XiRealDivisorSampling
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity

/-!
# The real Xi divisor has a superlinear counting function

**Theorem** (`superlinearSamples_xiRealDivisor`).  The real zeros of `ΞC(z) = ξ(½ + iz)` satisfy
`SuperlinearSamples`: for every `c` there is `T ≥ 1` with `c T < #(Z ∩ [−T, T])`.

Every positive simple critical ordinate `t` is a real zero of `ΞC`, and the Zeta23 simple-critical
density gives at least `T log T/(72π)` of them in `(0, T]`
(`eventually_superlinear_xiSimpleCriticalZeroCount`).

This is equation `(22)` of the sampling-idealizer card, the input of
`SuperlinearSamplingAperiodicity` for the real Xi divisor.  The collapse `(23)` is already
unconditional by progression-freeness (`xiSamplingIdealizer_collapse_unconditional`); this module
supplies the superlinear route.
-/

noncomputable section

open Filter Set

namespace RHTower

/-- **The real Xi divisor has a superlinear counting function, unconditionally.**  Every positive
simple critical ordinate `t` is a real zero of `ΞC`, and Zeta23 gives at least `T log T/(72π)` of
them in `(0, T]`. -/
theorem superlinearSamples_xiRealDivisor : SuperlinearSamples xiRealDivisor := by
  classical
  intro c
  have hlog : ∀ᶠ T : ℝ in atTop, 72 * Real.pi * (|c| + 1) < Real.log T :=
    Real.tendsto_log_atTop.eventually_gt_atTop _
  obtain ⟨T, hsuper, hlogT, hT1⟩ :=
    (eventually_superlinear_xiSimpleCriticalZeroCount.and (hlog.and
      (eventually_ge_atTop (1 : ℝ)))).exists
  refine ⟨T, hT1, ?_⟩
  set O := xiSimpleCriticalOrdinateFinset T with hO
  have hsub : (O : Set ℝ) ⊆ xiRealDivisor ∩ Icc (-T) T := by
    intro t ht
    obtain ⟨ht0, htT, hxi, -⟩ := mem_xiSimpleCriticalOrdinateFinset.mp ht
    refine ⟨?_, ⟨by linarith, htT⟩⟩
    show XiC (t : ℂ) = 0
    unfold XiC
    simpa [linePt] using hxi
  have hcard : (O.card : ℝ) ≤ samplingCount xiRealDivisor T := by
    have h := Set.ncard_le_ncard hsub (locallyFiniteSamples_xiRealDivisor T)
    rw [Set.ncard_coe_finset] at h
    exact_mod_cast h
  rw [hO, card_xiSimpleCriticalOrdinateFinset] at hcard
  have hpi : 0 < Real.pi := Real.pi_pos
  have hT0 : 0 < T := by linarith
  have hstep : c * T < 1 / (72 * Real.pi) * T * Real.log T := by
    have h1 : c * T ≤ |c| * T := mul_le_mul_of_nonneg_right (le_abs_self c) hT0.le
    have h2 : |c| * T < 1 / (72 * Real.pi) * T * Real.log T := by
      rw [show 1 / (72 * Real.pi) * T * Real.log T = T * (Real.log T / (72 * Real.pi)) by ring]
      rw [mul_comm |c| T]
      refine mul_lt_mul_of_pos_left ?_ hT0
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]
    linarith
  linarith

end RHTower
