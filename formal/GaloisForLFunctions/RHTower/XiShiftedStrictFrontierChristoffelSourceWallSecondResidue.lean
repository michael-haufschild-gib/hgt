import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierChristoffelSourceWallResidue
import Mathlib.Analysis.Calculus.LHopital

/-!
# Second contact of the strict-frontier arithmetic source wall

When the first omitted monic remainder vanishes, the newborn norm has zero first jet.  The next
jet is not missing: the division-free norm flux differentiates to the next adaptive completed
source.  L'Hopital then gives the exact quadratic coefficient and a second residue dichotomy.
-/

open Filter Matrix Polynomial Set Topology

namespace RHTower

/-- Next admitted adaptive source activated by tangential strict-frontier contact. -/
noncomputable def xiShiftedStrictFrontierTangentialSource (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionAdaptiveShear
    (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 2)

/-- Distance-squared rescaling of the preceding actual source wall. -/
noncomputable def xiShiftedStrictFrontierQuadraticallyScaledChristoffelSourceWall
    (n : ℕ) (v : ℝ) : ℝ :=
  (v - xiShiftedHigherBlockTerminalFrontier (n + 1)) ^ 2 *
    xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1)

/-- **Tangential source jet.**  If the first omitted remainder vanishes at an occupied strict
frontier, the newborn norm divided by squared distance tends to `(2m+1)` times the next adaptive
completed source, where `m=n+2`. -/
theorem tendsto_xiShiftedCanonicalAdmissionNorm_div_sq_at_strict_frontier_of_remainder_eq_zero
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hrem : xiShiftedStrictFrontierFirstOmittedRemainder n = 0) :
    Tendsto
      (fun v => xiShiftedCanonicalAdmissionNorm v (n + 2) /
        (v - xiShiftedHigherBlockTerminalFrontier (n + 1)) ^ 2)
      (𝓝[>] xiShiftedHigherBlockTerminalFrontier (n + 1))
      (𝓝 (((2 * (n + 2) + 1 : ℕ) : ℝ) *
        xiShiftedStrictFrontierTangentialSource n)) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let m := n + 2
  let N : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v m
  let F : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNormFlux v m
  let S : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionAdaptiveShear v m
  let K : ℝ := 2 * ((2 * m + 1 : ℕ) : ℝ) * S y
  have hy : 0 < y := by
    obtain ⟨u, hu⟩ := hne
    have hule := le_xiShiftedHigherBlockTerminalFrontier_of_mem hu
    exact lt_of_le_of_lt (hu.1.trans hule) hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hflat : xiShiftedMomentHankelMatrix y (m + 1) *ᵥ
      HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) m = 0 := by
    simpa only [m] using
      xiShiftedCanonicalAdmissionVector_mem_ker_of_succ_posSemidef_not_posDef
        hface.1 hface.2.1 hface.2.2
  have hNzero : N y = 0 := by
    simpa only [N, m, y] using
      xiShiftedCanonicalAdmissionNorm_eq_zero_at_strict_frontier hne hstrict
  have hrem' : xiShiftedHankelBoundaryMonicRemainder y
      (HTGeometry.monicMomentAdmissionVector
        (fun k => (xiShiftedReciprocalMoment y k).re) m) = 0 := by
    simpa only [xiShiftedStrictFrontierFirstOmittedRemainder, y, m] using hrem
  have hFzero : F y = 0 := by
    have hodd := xiShiftedCanonicalAdmissionOddCurrent_eq_monicRemainder_of_flatFace hflat
    have hNzero' : xiShiftedCanonicalAdmissionNorm y m = 0 := by
      simpa only [N] using hNzero
    dsimp only [F, xiShiftedCanonicalAdmissionNormFlux]
    rw [hNzero', hodd, hrem']
    ring
  have hFderiv : HasDerivAt F K y := by
    simpa only [F, K, S] using
      (hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_of_flatTangent
        hy (n := m) (by omega) hface.1 hflat hrem')
  have hFslope : Tendsto (fun v => (v - y)⁻¹ * F v)
      (𝓝[>] y) (𝓝 K) := by
    have h := hFderiv.tendsto_slope.mono_left inf_le_left
    simpa only [slope, hFzero, sub_zero, smul_eq_mul] using h
  have hff : ∀ᶠ v in 𝓝[>] y, HasDerivAt N (F v) v := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hH : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (n + 3)).PosDef := by
      simpa only [y] using
        (xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
          (n := n + 1) (le_of_lt (hy.trans hv)) hv)
    have hhead : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) m).PosDef := by
      simpa only [m] using
        (xiShiftedMomentHankel_posDef_of_le (by omega : n + 2 ≤ n + 3) hH)
    simpa only [N, F] using
      (hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det
        (hy.trans hv) (n := m) (by omega) (ne_of_gt hhead.det_pos))
  have hgg : ∀ᶠ v in 𝓝[>] y,
      HasDerivAt (fun u : ℝ => (u - y) ^ 2) (2 * (v - y)) v := by
    exact Eventually.of_forall fun v => by
      convert ((hasDerivAt_id v).sub_const y).pow 2 using 1 <;> ring
  have hg' : ∀ᶠ v in 𝓝[>] y, (2 * (v - y) : ℝ) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact ne_of_gt (mul_pos (by norm_num) (sub_pos.mpr hv))
  have hNderiv0 := hasDerivAt_xiShiftedCanonicalAdmissionNorm_of_flatFace
    hy (n := m) (by omega) hface.1 hflat
  have hfa : Tendsto N (𝓝[>] y) (𝓝 0) := by
    simpa only [hNzero] using hNderiv0.continuousAt.mono_left nhdsWithin_le_nhds
  have hga : Tendsto (fun v : ℝ => (v - y) ^ 2) (𝓝[>] y) (𝓝 0) := by
    have hcont : Tendsto (fun v : ℝ => (v - y) ^ 2) (𝓝 y) (𝓝 ((y - y) ^ 2)) :=
      ((continuousAt_id.sub continuousAt_const).pow 2)
    simpa using hcont.mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun v => F v / (2 * (v - y)))
      (𝓝[>] y) (𝓝 (K / 2)) := by
    have h := hFslope.div_const 2
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with v hv
    field_simp [sub_ne_zero.mpr hv.ne']
  have hquot := HasDerivAt.lhopital_zero_nhdsGT hff hgg hg' hfa hga hdiv
  have hK : K / 2 = ((2 * (n + 2) + 1 : ℕ) : ℝ) *
      xiShiftedStrictFrontierTangentialSource n := by
    dsimp only [K, S, xiShiftedStrictFrontierTangentialSource, m, y]
    ring
  rw [hK] at hquot
  simpa only [N, m, y] using hquot

/-- Right-chamber positivity forces the tangential successor source to be nonnegative. -/
theorem xiShiftedStrictFrontierTangentialSource_nonneg_of_remainder_eq_zero
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hrem : xiShiftedStrictFrontierFirstOmittedRemainder n = 0) :
    0 ≤ xiShiftedStrictFrontierTangentialSource n := by
  have hlim :=
    tendsto_xiShiftedCanonicalAdmissionNorm_div_sq_at_strict_frontier_of_remainder_eq_zero
      hne hstrict hrem
  have hnonneg : ∀ᶠ v in 𝓝[>] xiShiftedHigherBlockTerminalFrontier (n + 1),
      0 ≤ xiShiftedCanonicalAdmissionNorm v (n + 2) /
        (v - xiShiftedHigherBlockTerminalFrontier (n + 1)) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hy : 0 < xiShiftedHigherBlockTerminalFrontier (n + 1) := by
      obtain ⟨u, hu⟩ := hne
      have hule := le_xiShiftedHigherBlockTerminalFrontier_of_mem hu
      exact lt_of_le_of_lt (hu.1.trans hule) hstrict
    have hH : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (n + 3)).PosDef := by
      exact xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
        (n := n + 1) (le_of_lt (hy.trans hv)) hv
    have hhead : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (n + 2)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hH
    have hN : 0 < xiShiftedCanonicalAdmissionNorm v (n + 2) := by
      rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hhead]
      exact HTGeometry.monicOrthoNorm_pos_below
        (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
    exact div_nonneg hN.le (sq_nonneg _)
  have hcoef : 0 ≤ ((2 * (n + 2) + 1 : ℕ) : ℝ) *
      xiShiftedStrictFrontierTangentialSource n :=
    ge_of_tendsto hlim hnonneg
  have hfactor : 0 < ((2 * (n + 2) + 1 : ℕ) : ℝ) := by positivity
  nlinarith

end RHTower
