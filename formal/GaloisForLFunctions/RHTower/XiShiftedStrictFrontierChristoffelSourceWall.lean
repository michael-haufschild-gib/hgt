import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionScaleCompletedArithmeticSource
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionDefectEnergy
import GaloisForLFunctions.RHTower.XiShiftedHankelStrictFrontierCurvatureRenewal

/-!
# Christoffel source walls at strict shifted-Xi frontiers

The adaptive arithmetic source is formed from current inverse-Hankel admission before reflection
aggregation.  This file identifies its exact behavior at an actual strict terminal frontier.

At such a frontier the newly admitted monic flag is the normalized null vector of the singular
positive-semidefinite extension, so its norm vanishes.  The preceding adaptive source does not
vanish: its Jacobi energy retains the previous positive Christoffel edge.  Consequently source
completed by the next admitted norm tends to `+∞` from the positive side of every strict frontier.

This is a source law, not an orientation map or a fixed linear reporter.  The pole belongs to the
endogenous admission scale; the literal arithmetic numerator remains finite and positive.
-/

open Filter Matrix Polynomial Set Topology

namespace RHTower

noncomputable section

/-- Actual source-first adaptive shear completed by the next current admitted norm. -/
def xiShiftedCanonicalAdmissionChristoffelSourceWall
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionAdaptiveShear y n /
    (16 * xiShiftedCanonicalAdmissionNorm y (n + 1))

/-- The completed-square Jacobi energy strictly dominates its current positive edge. -/
theorem adaptiveOrthoJacobiEnergy_gt_succ_mul_currentBeta
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s n <
      HTGeometry.adaptiveOrthoJacobiEnergy s n := by
  have hsquares :
      0 ≤ ∑ j ∈ Finset.range n,
        (HTGeometry.monicOrthoAlpha s j +
          HTGeometry.monicOrthoAlpha s n / 2) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiag :
      0 ≤ (3 * (n : ℝ) / 4 + 1) *
        HTGeometry.monicOrthoAlpha s n ^ 2 := by
    positivity
  have hinterior :
      0 ≤ 2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hboundary :
      (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s n <
        (n + 1 : ℝ) *
          (HTGeometry.monicOrthoBeta s n +
            HTGeometry.monicOrthoBeta s (n + 1)) := by
    have hnext := HTGeometry.monicOrthoBeta_pos_below
      (n := n + 1) h (by omega) (by omega)
    have hdegree : 0 < (n + 1 : ℝ) := by positivity
    nlinarith
  unfold HTGeometry.adaptiveOrthoJacobiEnergy
  linarith

/-- In a positive chamber, actual adaptive shear is current admitted norm times Jacobi energy. -/
theorem xiShiftedCanonicalAdmissionAdaptiveShear_eq_norm_mul_jacobiEnergy
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionAdaptiveShear y n =
      xiShiftedCanonicalAdmissionNorm y n *
        HTGeometry.adaptiveOrthoJacobiEnergy
          (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hP : HTGeometry.monicMomentAdmissionPolynomial s n =
      HTGeometry.monicOrtho s n :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedCanonicalAdmissionAdaptiveShear, HTGeometry.momentInner_def]
  dsimp only
  rw [hP]
  change HTGeometry.momentFunctional s
      (HTGeometry.adaptiveOrthoSourcePolynomial s n) = _
  rw [HTGeometry.momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy_below
    hbelow hn le_rfl]
  rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]

/-- The previous Christoffel edge gives a strict division-free lower bound for actual source. -/
theorem succ_mul_admissionNorm_mul_prevNormRatio_lt_adaptiveShear
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (n + 1 : ℝ) * xiShiftedCanonicalAdmissionNorm y n *
        (xiShiftedCanonicalAdmissionNorm y n /
          xiShiftedCanonicalAdmissionNorm y (n - 1)) <
      xiShiftedCanonicalAdmissionAdaptiveShear y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have henergy := adaptiveOrthoJacobiEnergy_gt_succ_mul_currentBeta hbelow hn le_rfl
  have hnorm : xiShiftedCanonicalAdmissionNorm y n =
      HTGeometry.monicOrthoNormSq s n := by
    simpa only [s] using xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH
  have hprevH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) ((n - 1) + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hprev : xiShiftedCanonicalAdmissionNorm y (n - 1) =
      HTGeometry.monicOrthoNormSq s (n - 1) := by
    simpa only [s] using xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hprevH
  have hbeta : HTGeometry.monicOrthoBeta s n =
      xiShiftedCanonicalAdmissionNorm y n /
        xiShiftedCanonicalAdmissionNorm y (n - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [HTGeometry.monicOrthoBeta, hnorm, hprev]
  have hnormPos : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    rw [hnorm]
    exact HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  rw [xiShiftedCanonicalAdmissionAdaptiveShear_eq_norm_mul_jacobiEnergy hn hH,
    ← hbeta]
  nlinarith

/-- Actual canonical admitted norm is continuous at every positive mass where its leading block
is nonsingular, including degree zero. -/
theorem continuousAt_xiShiftedCanonicalAdmissionNorm_of_det
    {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hdet : (xiShiftedMomentHankelMatrix y n).det ≠ 0) :
    ContinuousAt (fun v => xiShiftedCanonicalAdmissionNorm v n) y := by
  rcases n with _ | n
  · have hzero : (fun v => xiShiftedCanonicalAdmissionNorm v 0) =
        (fun v => (xiShiftedReciprocalMoment v 0).re) := by
      funext v
      simp [xiShiftedCanonicalAdmissionNorm,
        HTGeometry.monicMomentAdmissionPolynomial,
        HTGeometry.finiteHankelNullPolynomial,
        HTGeometry.monicMomentAdmissionVector,
        HTGeometry.monicMomentAdmissionCoefficients,
        HTGeometry.momentInner_def, HTGeometry.momentFunctional]
    rw [hzero]
    exact (hasDerivAt_re_xiShiftedReciprocalMoment hy 0).continuousAt
  · exact (hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det
      hy (Nat.succ_pos n) hdet).continuousAt

/-- A singular positive-semidefinite Hankel extension with positive head annihilates the canonical
terminal-normalized inverse-Hankel admission. -/
theorem xiShiftedCanonicalAdmissionVector_mem_ker_of_succ_posSemidef_not_posDef
    {y : ℝ} {n : ℕ}
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hpsd : (xiShiftedMomentHankelMatrix y (n + 1)).PosSemidef)
    (hnot : ¬(xiShiftedMomentHankelMatrix y (n + 1)).PosDef) :
    xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
        HTGeometry.monicMomentAdmissionVector
          (fun k => (xiShiftedReciprocalMoment y k).re) n = 0 := by
  have hdet : (xiShiftedMomentHankelMatrix y (n + 1)).det = 0 :=
    not_ne_iff.mp ((hpsd.posDef_iff_det_ne_zero).not.mp hnot)
  obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hlast : c (Fin.last n) ≠ 0 :=
    xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
      y n c hhead hcne hc
  let d : Fin (n + 1) → ℝ := (c (Fin.last n))⁻¹ • c
  have hd : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ d = 0 := by
    change xiShiftedMomentHankelMatrix y (n + 1) *ᵥ
      ((c (Fin.last n))⁻¹ • c) = 0
    rw [Matrix.mulVec_smul, hc, smul_zero]
  have hdlast : d (Fin.last n) = 1 := by
    simp [d, hlast]
  have heq : d = HTGeometry.monicMomentAdmissionVector
      (fun k => (xiShiftedReciprocalMoment y k).re) n := by
    have hhead' : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef := by
      simpa only [xiShiftedMomentHankelMatrix,
        GaloisForLFunctions.HTGeometry.finiteHankelMatrix,
        HTGeometry.momentHankelMatrix] using hhead
    apply HTGeometry.eq_monicMomentAdmissionVector_of_kernel_of_last_eq_one
      (ne_of_gt hhead'.det_pos)
    · simpa only [xiShiftedMomentHankelMatrix,
        GaloisForLFunctions.HTGeometry.finiteHankelMatrix,
        HTGeometry.momentHankelMatrix] using hd
    · exact hdlast
  rwa [← heq]

/-- At an occupied strict frontier, next canonical admitted norm is exactly zero. -/
theorem xiShiftedCanonicalAdmissionNorm_eq_zero_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    xiShiftedCanonicalAdmissionNorm
        (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 2) = 0 := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hflat :=
    xiShiftedCanonicalAdmissionVector_mem_ker_of_succ_posSemidef_not_posDef
      hface.1 hface.2.1 hface.2.2
  exact xiShiftedCanonicalAdmissionNorm_eq_zero_of_flatFace hflat

/-- Previous adaptive source remains strictly positive at an occupied strict frontier. -/
theorem xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    0 < xiShiftedCanonicalAdmissionAdaptiveShear
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let d := n + 1
  let source : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionAdaptiveShear v d
  let lower : ℝ → ℝ := fun v =>
    (d + 1 : ℝ) * xiShiftedCanonicalAdmissionNorm v d *
      (xiShiftedCanonicalAdmissionNorm v d /
        xiShiftedCanonicalAdmissionNorm v (d - 1))
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hdH : (xiShiftedMomentHankelMatrix y d).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hprevH : (xiShiftedMomentHankelMatrix y (d - 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hprevNormH : (xiShiftedMomentHankelMatrix y d).PosDef := hdH
  have hsourceCont : ContinuousAt source y := by
    have h := continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment
      hy d (ne_of_gt hdH.det_pos)
    simpa only [source, xiShiftedCanonicalAdmissionAdaptiveShear,
      HTGeometry.momentInner_def] using h
  have hnormCont : ContinuousAt
      (fun v => xiShiftedCanonicalAdmissionNorm v d) y :=
    continuousAt_xiShiftedCanonicalAdmissionNorm_of_det
      hy d (ne_of_gt hdH.det_pos)
  have hprevCont : ContinuousAt
      (fun v => xiShiftedCanonicalAdmissionNorm v (d - 1)) y :=
    continuousAt_xiShiftedCanonicalAdmissionNorm_of_det
      hy (d - 1) (ne_of_gt hprevH.det_pos)
  have hprevPos : 0 < xiShiftedCanonicalAdmissionNorm y (d - 1) := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_hankelQuadratic]
    exact hprevNormH.dotProduct_mulVec_pos (by
      intro hz
      have := congrFun hz (Fin.last (d - 1))
      simpa only [HTGeometry.monicMomentAdmissionVector_last, Pi.zero_apply] using this)
  have hnormPos : 0 < xiShiftedCanonicalAdmissionNorm y d := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_hankelQuadratic]
    exact hface.1.dotProduct_mulVec_pos (by
      intro hz
      have := congrFun hz (Fin.last d)
      simpa only [HTGeometry.monicMomentAdmissionVector_last, Pi.zero_apply] using this)
  have hlowerPos : 0 < lower y := by
    dsimp only [lower]
    exact mul_pos (mul_pos (by positivity) hnormPos)
      (div_pos hnormPos hprevPos)
  have hlowerCont : ContinuousAt lower y := by
    exact ((continuousAt_const.mul hnormCont).mul
      (hnormCont.div hprevCont (ne_of_gt hprevPos)))
  have hle : lower y ≤ source y := by
    have hsourceLim : Tendsto source (nhdsWithin y (Ioi y)) (nhds (source y)) :=
      hsourceCont.mono_left nhdsWithin_le_nhds
    have hlowerLim : Tendsto lower (nhdsWithin y (Ioi y)) (nhds (lower y)) :=
      hlowerCont.mono_left nhdsWithin_le_nhds
    have hdiff := hsourceLim.sub hlowerLim
    have hevent : ∀ᶠ v in nhdsWithin y (Ioi y), 0 ≤ source v - lower v := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      have hv0 : 0 ≤ v := (hy.trans hv).le
      have hH : (HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment v k).re) (d + 2)).PosDef := by
        simpa only [d, y] using
          (xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
            (n := n + 1) hv0 hv)
      have hbound :=
        succ_mul_admissionNorm_mul_prevNormRatio_lt_adaptiveShear
          (n := d) (by omega) hH
      dsimp only [source, lower]
      linarith
    have hzero : 0 ≤ source y - lower y := ge_of_tendsto hdiff hevent
    linarith
  dsimp only [source] at hle
  exact lt_of_lt_of_le hlowerPos hle

/-- **Strict-frontier Christoffel source wall.**  Approaching every occupied strict terminal
frontier from its positive chamber, preceding actual adaptive source divided by next admitted norm
tends to `+∞`. -/
theorem tendsto_xiShiftedCanonicalAdmissionChristoffelSourceWall_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    Tendsto
      (fun y => xiShiftedCanonicalAdmissionChristoffelSourceWall y (n + 1))
      (nhdsWithin (xiShiftedHigherBlockTerminalFrontier (n + 1))
        (Ioi (xiShiftedHigherBlockTerminalFrontier (n + 1)))) atTop := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let d := n + 1
  let source : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionAdaptiveShear v d
  let nextNorm : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v (d + 1)
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hsourcePos : 0 < source y := by
    simpa only [source, d, y] using
      xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier hne hstrict
  have hdH : (xiShiftedMomentHankelMatrix y d).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hsourceCont : ContinuousAt source y := by
    have h := continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment
      hy d (ne_of_gt hdH.det_pos)
    simpa only [source, xiShiftedCanonicalAdmissionAdaptiveShear,
      HTGeometry.momentInner_def] using h
  have hnextCont : ContinuousAt nextNorm y := by
    have hdet : (xiShiftedMomentHankelMatrix y (d + 1)).det ≠ 0 := by
      simpa only [d] using ne_of_gt hface.1.det_pos
    exact continuousAt_xiShiftedCanonicalAdmissionNorm_of_det hy (d + 1) hdet
  have hnextZero : nextNorm y = 0 := by
    simpa only [nextNorm, d, y, Nat.add_assoc] using
      xiShiftedCanonicalAdmissionNorm_eq_zero_at_strict_frontier hne hstrict
  have hnextTendsto : Tendsto nextNorm (nhdsWithin y (Ioi y)) (nhds 0) := by
    simpa only [hnextZero] using hnextCont.mono_left nhdsWithin_le_nhds
  have hnextPos : ∀ᶠ v in nhdsWithin y (Ioi y), nextNorm v ∈ Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv0 : 0 ≤ v := (hy.trans hv).le
    have hH : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (d + 2)).PosDef := by
      simpa only [d, y] using
        (xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
          (n := n + 1) hv0 hv)
    dsimp only [nextNorm]
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
  have hnextWithin : Tendsto nextNorm (nhdsWithin y (Ioi y))
      (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      nextNorm hnextTendsto hnextPos
  have hinv : Tendsto (fun v => (16 * nextNorm v)⁻¹)
      (nhdsWithin y (Ioi y)) atTop := by
    have hscaled : Tendsto (fun v => 16 * nextNorm v)
        (nhdsWithin y (Ioi y)) (nhdsWithin 0 (Ioi 0)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using (tendsto_const_nhds.mul hnextTendsto)
      · filter_upwards [hnextPos] with v hv
        change 0 < 16 * nextNorm v
        exact mul_pos (by norm_num) hv
    exact tendsto_inv_nhdsGT_zero.comp hscaled
  have hsourceTendsto : Tendsto source (nhdsWithin y (Ioi y)) (nhds (source y)) :=
    hsourceCont.mono_left nhdsWithin_le_nhds
  have hwall := Filter.Tendsto.pos_mul_atTop hsourcePos hsourceTendsto hinv
  simpa only [xiShiftedCanonicalAdmissionChristoffelSourceWall, source, nextNorm,
    d, y, div_eq_mul_inv] using hwall

/-- The wall numerator is exactly the literal rational--Gamma minus von Mangoldt adaptive
completed aggregate at square mass. -/
theorem two_mul_xiShiftedCanonicalAdmissionChristoffelSourceWall_eq_arithmeticSource_div_nextNorm
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    2 * xiShiftedCanonicalAdmissionChristoffelSourceWall (w ^ 2) n =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n) /
        (16 * xiShiftedCanonicalAdmissionNorm (w ^ 2) (n + 1)) := by
  have hsource := two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hw
    (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n)
  rw [xiShiftedCanonicalAdmissionChristoffelSourceWall]
  rw [← hsource]
  change 2 *
      (xiShiftedCanonicalAdmissionAdaptiveShear (w ^ 2) n /
        (16 * xiShiftedCanonicalAdmissionNorm (w ^ 2) (n + 1))) =
    (2 * xiShiftedCanonicalAdmissionAdaptiveShear (w ^ 2) n) /
      (16 * xiShiftedCanonicalAdmissionNorm (w ^ 2) (n + 1))
  ring

end

end RHTower
