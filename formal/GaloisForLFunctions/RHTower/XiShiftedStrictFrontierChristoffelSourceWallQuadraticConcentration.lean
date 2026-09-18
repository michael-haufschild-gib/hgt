import GaloisForLFunctions.RHTower.XiShiftedArcsineVacuumRenormalizedSourceLaw

/-!
# Quadratic concentration at strict shifted-Xi source walls

The strict-frontier wall already dominates the reciprocal distance to its endogenous
newborn-admission zero.  Squaring this lower bound gives the Route-U quadratic shadow:
the exact source wall has infinite local `L²` energy at every occupied strict frontier.
This is independent of Padé contact order, so higher tangency cannot evade the common
U/Q concentration primitive by broadening the mass coordinate.

This result is only the lower shadow.  It does not assert the missing source-pure finite
quadratic ceiling required to exclude the cofinal wall phase.
-/

open Filter Matrix MeasureTheory Set Topology
open scoped Topology

namespace RHTower

noncomputable section

private theorem not_intervalIntegrable_sq_of_sub_inv_isBigO
    {y b : ℝ} {wall : ℝ → ℝ}
    (hbig : (fun v => (v - y)⁻¹) =O[𝓝[>] y] wall) (hb : y < b) :
    ¬IntervalIntegrable (fun v => wall v ^ 2) volume y b := by
  let kernel : ℝ → ℝ := fun v => (v - y)⁻¹
  have hbig' : kernel =O[𝓝[>] y] wall := by
    simpa only [kernel] using hbig
  have hderiv : ∀ᶠ v in 𝓝[>] y,
      HasDerivAt (-kernel) (kernel v ^ 2) v := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    change y < v at hv
    have hlinear : HasDerivAt (fun z : ℝ => z - y) 1 v := by
      simpa using (hasDerivAt_id v).sub_const y
    have hbase : HasDerivAt kernel (-(kernel v ^ 2)) v := by
      have hbase' := hlinear.inv (sub_ne_zero.mpr hv.ne')
      have hkernel : kernel = (fun z : ℝ => z - y)⁻¹ := by
        funext z
        rfl
      rw [← hkernel] at hbase'
      simpa only [kernel, one_div, inv_pow, neg_div] using hbase'
    simpa only [neg_neg] using hbase.neg
  have hsubN : Tendsto (fun v => v - y) (𝓝 y) (𝓝 0) := by
    have h : Tendsto (fun v => v - y) (𝓝 y) (𝓝 (y - y)) :=
      ((hasDerivAt_id y).sub_const y).continuousAt
    simpa using h
  have hsub : Tendsto (fun v => v - y) (𝓝[>] y) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hsubN.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    change y < v at hv
    exact sub_pos.mpr hv
  have hinv : Tendsto kernel (𝓝[>] y) atTop := by
    change Tendsto ((fun x : ℝ => x⁻¹) ∘ fun v => v - y) (𝓝[>] y) atTop
    exact tendsto_inv_nhdsGT_zero.comp hsub
  have hnorm : Tendsto (fun v => ‖-kernel v‖) (𝓝[>] y) atTop := by
    apply hinv.congr'
    filter_upwards [self_mem_nhdsWithin] with v hv
    change y < v at hv
    have hpos : 0 < kernel v := by
      dsimp only [kernel]
      exact inv_pos.mpr (sub_pos.mpr hv)
    rw [Real.norm_eq_abs, abs_of_neg (neg_lt_zero.mpr hpos)]
    ring
  have hderivBig : deriv (-kernel) =O[𝓝[>] y]
      (fun v => wall v ^ 2) :=
    (hbig'.pow 2).congr' (hderiv.mono fun v hv => hv.deriv.symm) EventuallyEq.rfl
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
    (𝓝[>] y) (Ioc_mem_nhdsGT hb)
      (hderiv.mono fun v hv => hv.differentiableAt) hnorm hderivBig

/-- **Route-U quadratic concentration.**  At every occupied strict shifted-Hankel frontier,
the square of the literal admission-completed arithmetic source wall is not locally integrable
on the positive mass side.  The proof retains the actual wall and needs no contact-order bound:
the established reciprocal-distance source lower bound is squared before applying the derivative
criterion. -/
theorem not_intervalIntegrable_sq_xiShiftedCanonicalAdmissionChristoffelSourceWall_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    {b : ℝ} (hb : xiShiftedHigherBlockTerminalFrontier (n + 1) < b) :
    ¬IntervalIntegrable
      (fun v => xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1) ^ 2)
      volume (xiShiftedHigherBlockTerminalFrontier (n + 1)) b := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let wall : ℝ → ℝ := fun v =>
    xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1)
  have hbig : (fun v => (v - y)⁻¹) =O[𝓝[>] y] wall := by
    simpa only [wall, y] using
      strictFrontier_sub_inv_isBigO_christoffelSourceWall hne hstrict
  exact not_intervalIntegrable_sq_of_sub_inv_isBigO hbig (by simpa only [y] using hb)

/-- Full arcsine-vacuum centering retains the reciprocal strict-frontier lower bound.  The
counterterm is degree-dependent but mass-regular; no contact residue or quadratic concentration
can be removed by this source-first subtraction. -/
theorem strictFrontier_sub_inv_isBigO_arcsineCenteredChristoffelSourceWall
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
    (fun v => (v - y)⁻¹) =O[𝓝[>] y]
      (fun v => xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall v (n + 1)) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let raw : ℝ → ℝ := fun v =>
    xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1)
  let centered : ℝ → ℝ := fun v =>
    xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall v (n + 1)
  let source0 := xiShiftedCanonicalAdmissionAdaptiveShear y (n + 1)
  let c := HTGeometry.monicMomentAdmissionVector
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)
  let K := source0 / (32 * (xiShiftedMomentHankelQuadraticLipschitzWeight c + 1))
  let C := XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm (n + 1)
  have hK : 0 < K := by
    dsimp only [K, source0, c]
    exact div_pos
      (xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier hne hstrict)
      (mul_pos (by norm_num)
        (by linarith [xiShiftedMomentHankelQuadraticLipschitzWeight_nonneg c]))
  have hC : 0 < C := by
    dsimp only [C, XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm]
    positivity
  have hraw : ∀ᶠ v in 𝓝[>] y, K * (v - y)⁻¹ ≤ raw v := by
    simpa only [K, source0, c, raw, y] using
      eventually_strictFrontier_reciprocal_le_christoffelSourceWall hne hstrict
  have hrawTop : Tendsto raw (𝓝[>] y) atTop := by
    simpa only [raw, y] using
      tendsto_xiShiftedCanonicalAdmissionChristoffelSourceWall_at_strict_frontier hne hstrict
  have hlarge : ∀ᶠ v in 𝓝[>] y, 2 * C ≤ raw v :=
    (tendsto_atTop.1 hrawTop) (2 * C)
  rw [Asymptotics.isBigO_iff'']
  refine ⟨K / 2, by positivity, ?_⟩
  filter_upwards [hraw, hlarge, self_mem_nhdsWithin] with v hvraw hvlarge hv
  change y < v at hv
  have hinv : 0 < (v - y)⁻¹ := inv_pos.mpr (sub_pos.mpr hv)
  have hcenter : 0 < raw v - C := by linarith
  have hbound : (K / 2) * (v - y)⁻¹ ≤ raw v - C := by
    nlinarith
  have hcentered : centered v = raw v - C := by
    dsimp only [centered, raw, C,
      xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall]
  change K / 2 * ‖(v - y)⁻¹‖ ≤ ‖centered v‖
  rw [hcentered]
  simpa only [Real.norm_eq_abs, abs_of_pos hinv, abs_of_pos hcenter] using hbound

/-- **Vacuum-free Route-U quadratic shadow.**  Full arcsine source centering removes the exact
far-right vacuum but leaves the strict-frontier local `L²` divergence intact.  Hence a common U/Q
energy must control genuine concentration, not merely a deterministic degree vacuum. -/
theorem not_intervalIntegrable_sq_xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    {b : ℝ} (hb : xiShiftedHigherBlockTerminalFrontier (n + 1) < b) :
    ¬IntervalIntegrable
      (fun v => xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall v (n + 1) ^ 2)
      volume (xiShiftedHigherBlockTerminalFrontier (n + 1)) b := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let wall : ℝ → ℝ := fun v =>
    xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall v (n + 1)
  have hbig : (fun v => (v - y)⁻¹) =O[𝓝[>] y] wall := by
    simpa only [wall, y] using
      strictFrontier_sub_inv_isBigO_arcsineCenteredChristoffelSourceWall hne hstrict
  exact not_intervalIntegrable_sq_of_sub_inv_isBigO hbig (by simpa only [y] using hb)

end

end RHTower
