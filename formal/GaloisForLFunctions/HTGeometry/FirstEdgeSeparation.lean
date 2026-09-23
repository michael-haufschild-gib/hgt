import GaloisForLFunctions.HTGeometry.OneVariableMvPolynomial
import GaloisForLFunctions.HTGeometry.SeparationImpliesTranscendence

/-!
# The growth separation at the first edge

At the first edge of a cascade the only earlier state is the coordinate, so the coefficient of a
relation is a univariate polynomial.  Such a polynomial has an explicit floor beyond an explicit
radius, and a transcendental entire function exceeds every polynomial bound — necessarily outside any
fixed disc, since it is bounded on compacts.

The separation at the first edge is therefore a theorem, not a hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- `log⁺` is dominated by the logarithm of the shifted argument. -/
theorem posLog_le_log_one_add_firstEdgeSeparation {t : ℝ} (ht : 0 ≤ t) : Real.posLog t ≤ Real.log (1 + t) := by
  rw [Real.posLog_apply]
  refine max_le (Real.log_nonneg (by linarith)) ?_
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, Real.log_zero]
    exact Real.log_nonneg (by linarith)
  · exact Real.log_le_log h (by linarith)

/-- **The separation at the first edge.**  For a transcendental entire `f`, the coordinate is
separated from `f` at every level. -/
theorem stepSeparation_first_edge {Y : ℕ → ℂ → ℂ} (hY0 : ∀ z : ℂ, Y 0 z = z)
    (hf : TranscendentalEntire (Y 1)) :
    StepSeparation (prefixFamily Y 1) (Y 1) := by
  intro A hA c hc
  -- the coefficient is a univariate polynomial
  set q : Polynomial ℂ := toPoly A with hq
  have hq0 : q ≠ 0 := toPoly_ne_zero hA
  have hlc : 0 < ‖q.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hq0)
  set ε : ℝ := ‖q.leadingCoeff‖ / 2 with hε
  have hε0 : 0 < ε := by
    rw [hε]
    linarith
  set R : ℝ := growthRadius q with hR
  have hR1 : (1 : ℝ) ≤ R := one_le_growthRadius q
  -- `Y 1` is bounded on the disc of radius `R`
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hf.1.continuous.continuousOn
  set L : ℝ := Real.posLog ε⁻¹ with hL
  have hL0 : 0 ≤ L := Real.posLog_nonneg
  set d : ℕ := ⌈c⌉₊ + 1 with hd
  have hcd : c ≤ (d : ℝ) := by
    rw [hd]
    push_cast
    linarith [Nat.le_ceil c]
  set K : ℝ := Real.exp (c + c * L + 1) with hK
  have hK0 : 0 < K := Real.exp_pos _
  set Mbig : ℝ := max K M₀ with hM
  have hMbig : 0 < Mbig := lt_of_lt_of_le hK0 (le_max_left _ _)
  obtain ⟨z, hz⟩ := exists_norm_gt_of_not_polynomial hf.1 hf.2 Mbig d
  -- the point is outside the disc
  have hzR : R < ‖z‖ := by
    by_contra hcon
    have hmem : z ∈ Metric.closedBall (0 : ℂ) R := by
      simpa using not_lt.mp hcon
    have hle : ‖Y 1 z‖ ≤ M₀ := hM₀ z hmem
    have hpow : (1 : ℝ) ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z])
    have hMle : Mbig ≤ Mbig * (1 + ‖z‖) ^ d := by
      nlinarith [hMbig, hpow]
    have hM0le : M₀ ≤ Mbig := le_max_right K M₀
    linarith [hz, hMle, hle, hM0le]
  have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by linarith) hzR.le
  -- the floor
  have hfloor : ε ≤ ‖q.eval z‖ := by
    obtain ⟨hz1, hz2⟩ := hyps_of_growthRadius_le hq0 (le_of_lt hzR)
    have hge := norm_eval_ge_of_large hq0 hz1 hz2
    have hpow : (1 : ℝ) ≤ ‖z‖ ^ q.natDegree := one_le_pow₀ hz1
    have hstep : ‖q.leadingCoeff‖ / 2 * 1 ≤ ‖q.leadingCoeff‖ / 2 * ‖z‖ ^ q.natDegree :=
      mul_le_mul_of_nonneg_left hpow (by linarith)
    rw [hε]
    linarith [hge, hstep]
  refine ⟨z, ε, hε0, ?_, ?_⟩
  · have hxfun : (fun j : Fin 1 => prefixFamily Y 1 j z) = fun _ : Fin 1 => z := by
      funext j
      refine Fin.cases ?_ (fun i => i.elim0) j
      exact hY0 z
    rw [hxfun, ← eval_toPoly, ← hq]
    exact hfloor
  · -- the growth comparison
    have hsum : (∑ j : Fin 1, Real.posLog ‖prefixFamily Y 1 j z‖) = Real.posLog ‖z‖ := by
      rw [Fin.sum_univ_one]
      have hz0 : prefixFamily Y 1 0 z = z := hY0 z
      rw [hz0]
    rw [hsum]
    have hP0 : (0 : ℝ) ≤ Real.posLog ‖z‖ := Real.posLog_nonneg
    have hbig : Mbig * (1 + ‖z‖) ^ d < ‖Y 1 z‖ := hz
    have hpos : (0 : ℝ) < Mbig * (1 + ‖z‖) ^ d := by positivity
    have hlog : Real.log (Mbig * (1 + ‖z‖) ^ d) < Real.log ‖Y 1 z‖ :=
      Real.log_lt_log hpos hbig
    have hexp : Real.log (Mbig * (1 + ‖z‖) ^ d)
        = Real.log Mbig + d * Real.log (1 + ‖z‖) := by
      rw [Real.log_mul (ne_of_gt hMbig) (by positivity), Real.log_pow]
    have hKle : c + c * L + 1 ≤ Real.log Mbig := by
      have h1 : Real.log K = c + c * L + 1 := by
        rw [hK, Real.log_exp]
      have h2 : K ≤ Mbig := le_max_left _ _
      have := Real.log_le_log hK0 h2
      linarith [h1]
    have hPlog : Real.posLog ‖z‖ ≤ Real.log (1 + ‖z‖) :=
      posLog_le_log_one_add_firstEdgeSeparation (norm_nonneg z)
    have hfinal : Real.log ‖Y 1 z‖ ≤ Real.posLog ‖Y 1 z‖ := by
      rw [Real.posLog_apply]
      exact le_max_right _ _
    nlinarith [hlog, hexp, hKle, hPlog, hfinal, hP0, hcd, hL0, hc]

end GaloisForLFunctions.HTGeometry
