import GaloisForLFunctions.HTGeometry.SegmentParameterHolomorphy
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The parameter fundamental theorem for the half-power segment integral

For `G` holomorphic on an open set star-shaped about the origin, the weighted segment integrals

`Φ(z) = ∫₀¹ s^{1/2} G(zs) ds`

satisfy the exact relation

`(3/2)Φ(z) + z Φ'(z) = G(z)`,

because the integrand of the left side is `d/ds [s^{3/2}G(zs)]` and the boundary values are `G(z)`
and `0`.  This is what makes `z^{3/2}Φ(z)`, the contour integral of `z^{1/2}G(z)` along the segment
from the origin, a primitive of that integrand.

The half-power weight is exactly the one produced by the Gamma propagator inverse, so the identity
is what links the segment representation of the forced particular solution with the
variation-of-constants representation along a horizontal line.
-/

open MeasureTheory Set Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- On the nonnegative reals the complex half powers are real powers. -/
theorem cpow_ofReal_nonneg {c s : ℝ} (hs : 0 ≤ s) :
    ((s : ℂ) ^ ((c : ℝ) : ℂ)) = ((s ^ c : ℝ) : ℂ) := (Complex.ofReal_cpow hs c).symm

theorem continuousOn_cpow_ofReal {c : ℝ} (hc : 0 ≤ c) :
    ContinuousOn (fun s : ℝ => (s : ℂ) ^ ((c : ℝ) : ℂ)) (Icc (0 : ℝ) 1) := by
  refine ContinuousOn.congr (f := fun s : ℝ => ((s ^ c : ℝ) : ℂ)) ?_ ?_
  · exact Complex.continuous_ofReal.comp_continuousOn (Real.continuous_rpow_const hc).continuousOn
  · intro s hs
    exact cpow_ofReal_nonneg hs.1

theorem hasDerivAt_cpow_ofReal {c s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ ((c : ℝ) : ℂ))
      (((c : ℝ) : ℂ) * (s : ℂ) ^ (((c - 1 : ℝ)) : ℂ)) s := by
  have hreal : HasDerivAt (fun t : ℝ => t ^ c) (c * s ^ (c - 1)) s :=
    Real.hasDerivAt_rpow_const (Or.inl hs.ne')
  have hC := hreal.ofReal_comp
  have heq : (fun t : ℝ => (t : ℂ) ^ ((c : ℝ) : ℂ)) =ᶠ[nhds s]
      (fun t : ℝ => ((t ^ c : ℝ) : ℂ)) := by
    filter_upwards [eventually_gt_nhds hs] with t ht
    exact cpow_ofReal_nonneg ht.le
  refine (hC.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [cpow_ofReal_nonneg hs.le]
  push_cast
  ring

/-- **The parameter fundamental theorem.**  The half-power segment integral and its parameter
derivative combine to the value of the integrand at the endpoint. -/
theorem segment_ftc_half {U : Set ℂ} (hU : IsOpen U)
    (hstar : ∀ z ∈ U, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → z * (s : ℂ) ∈ U)
    {G : ℂ → X} (hG : DifferentiableOn ℂ G U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ((3 : ℂ) / 2) • (∫ s in (0 : ℝ)..1, ((s : ℂ) ^ ((1 : ℂ) / 2)) • G (z₀ * (s : ℂ)))
        + z₀ • (∫ s in (0 : ℝ)..1, ((s : ℂ) ^ ((3 : ℂ) / 2)) • deriv G (z₀ * (s : ℂ)))
      = G z₀ := by
  have hcast1 : ((1 : ℂ) / 2) = (((1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
  have hcast3 : ((3 : ℂ) / 2) = (((3 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
  -- the swept points stay in `U`
  have hmemU : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → z₀ * (s : ℂ) ∈ U := fun s hs => hstar z₀ hz₀ s hs
  have hGa : AnalyticOnNhd ℂ G U := hG.analyticOnNhd hU
  have hdercont : ContinuousOn (deriv G) U := hGa.deriv.continuousOn
  have hline : ContinuousOn (fun s : ℝ => z₀ * (s : ℂ)) (Icc (0 : ℝ) 1) := by fun_prop
  have hGcont : ContinuousOn (fun s : ℝ => G (z₀ * (s : ℂ))) (Icc (0 : ℝ) 1) :=
    ContinuousOn.comp hG.continuousOn hline hmemU
  have hdGcont : ContinuousOn (fun s : ℝ => deriv G (z₀ * (s : ℂ))) (Icc (0 : ℝ) 1) :=
    ContinuousOn.comp hdercont hline hmemU
  set f : ℝ → X := fun s => ((s : ℂ) ^ ((3 : ℂ) / 2)) • G (z₀ * (s : ℂ)) with hfdef
  set f' : ℝ → X := fun s => ((3 : ℂ) / 2) • (((s : ℂ) ^ ((1 : ℂ) / 2)) • G (z₀ * (s : ℂ)))
    + z₀ • (((s : ℂ) ^ ((3 : ℂ) / 2)) • deriv G (z₀ * (s : ℂ))) with hf'def
  have hpow1 : ContinuousOn (fun s : ℝ => (s : ℂ) ^ ((1 : ℂ) / 2)) (Icc (0 : ℝ) 1) := by
    rw [hcast1]
    exact continuousOn_cpow_ofReal (by norm_num)
  have hpow3 : ContinuousOn (fun s : ℝ => (s : ℂ) ^ ((3 : ℂ) / 2)) (Icc (0 : ℝ) 1) := by
    rw [hcast3]
    exact continuousOn_cpow_ofReal (by norm_num)
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 1) := hpow3.smul hGcont
  have hf'cont : ContinuousOn f' (Icc (0 : ℝ) 1) :=
    ((hpow1.smul hGcont).const_smul _).add ((hpow3.smul hdGcont).const_smul _)
  have hf'int : IntervalIntegrable f' volume 0 1 := by
    refine (hf'cont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt f (f' s) (Ioi s) s := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hsIcc : s ∈ Icc (0 : ℝ) 1 := ⟨hs0.le, hs.2.le⟩
    have hpow : HasDerivAt (fun t : ℝ => (t : ℂ) ^ ((3 : ℂ) / 2))
        (((3 : ℂ) / 2) * (s : ℂ) ^ ((1 : ℂ) / 2)) s := by
      have h := hasDerivAt_cpow_ofReal (c := (3 / 2 : ℝ)) hs0
      rw [← hcast3] at h
      refine h.congr_deriv ?_
      norm_num
    have hlin : HasDerivAt (fun t : ℝ => z₀ * (t : ℂ)) z₀ s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul z₀
    have hGd : HasDerivAt G (deriv G (z₀ * (s : ℂ))) (z₀ * (s : ℂ)) :=
      (hG.differentiableAt (hU.mem_nhds (hmemU s hsIcc))).hasDerivAt
    have hGs : HasDerivAt (fun t : ℝ => G (z₀ * (t : ℂ))) (z₀ • deriv G (z₀ * (s : ℂ))) s :=
      HasDerivAt.scomp s hGd hlin
    have hprod := hpow.smul hGs
    refine (hprod.congr_deriv ?_).hasDerivWithinAt
    rw [hf'def]
    simp only
    rw [smul_smul, smul_smul]
    ring_nf
    module
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hfcont hderiv hf'int
  have hf1 : f 1 = G z₀ := by
    rw [hfdef]
    simp
  have hf0 : f 0 = 0 := by
    rw [hfdef]
    simp only
    rw [Complex.ofReal_zero, Complex.zero_cpow (by norm_num), zero_smul]
  rw [hf1, hf0, sub_zero] at hFTC
  have hint1 : IntervalIntegrable
      (fun s : ℝ => ((3 : ℂ) / 2) • (((s : ℂ) ^ ((1 : ℂ) / 2)) • G (z₀ * (s : ℂ))))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hpow1.smul hGcont).const_smul _
  have hint2 : IntervalIntegrable
      (fun s : ℝ => z₀ • (((s : ℂ) ^ ((3 : ℂ) / 2)) • deriv G (z₀ * (s : ℂ))))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hpow3.smul hdGcont).const_smul _
  have hsplit : (∫ y in (0 : ℝ)..1, f' y)
      = ((3 : ℂ) / 2) • (∫ s in (0 : ℝ)..1, ((s : ℂ) ^ ((1 : ℂ) / 2)) • G (z₀ * (s : ℂ)))
        + z₀ • (∫ s in (0 : ℝ)..1, ((s : ℂ) ^ ((3 : ℂ) / 2)) • deriv G (z₀ * (s : ℂ))) := by
    show (∫ y in (0 : ℝ)..1,
        (((3 : ℂ) / 2) • (((y : ℂ) ^ ((1 : ℂ) / 2)) • G (z₀ * (y : ℂ)))
          + z₀ • (((y : ℂ) ^ ((3 : ℂ) / 2)) • deriv G (z₀ * (y : ℂ))))) = _
    rw [intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_smul,
      intervalIntegral.integral_smul]
  rw [← hFTC]
  exact hsplit.symm

end GaloisForLFunctions.HTGeometry
