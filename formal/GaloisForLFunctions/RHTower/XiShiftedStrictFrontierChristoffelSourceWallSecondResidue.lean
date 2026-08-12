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

set_option maxHeartbeats 800000

/-- Next admitted adaptive source activated by tangential strict-frontier contact. -/
noncomputable def xiShiftedStrictFrontierTangentialSource (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionAdaptiveShear
    (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 2)

/-- Literal adaptive mixed completed arithmetic source attached to tangential successor admission. -/
noncomputable def xiShiftedStrictFrontierTangentialArithmeticSource (n : ℕ) : ℝ :=
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  xiShiftedAdaptiveMixedCompletedArithmeticSource (Real.sqrt y)
    (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 2))

/-- Exact finite residue when tangential contact has positive successor source. -/
noncomputable def xiShiftedStrictFrontierQuadraticResidue (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionAdaptiveShear
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) /
    (16 * (((2 * (n + 2) + 1 : ℕ) : ℝ) *
      xiShiftedStrictFrontierTangentialSource n))

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
  letI : NormedSpace ℝ ℝ := NormedAlgebra.toNormedSpace ℝ
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
    have h := hFderiv.tendsto_slope.mono_left (nhdsGT_le_nhdsNE y)
    apply h.congr'
    filter_upwards with v
    rw [slope, hFzero]
    change (v - y)⁻¹ * (F v - 0) = (v - y)⁻¹ * F v
    ring
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
      HasDerivAt ((fun x : ℝ => x - y) * (fun x : ℝ => x - y))
        (2 * (v - y)) v := by
    exact Eventually.of_forall fun v =>
      (((hasDerivAt_id' v).sub_const y).mul
        ((hasDerivAt_id' v).sub_const y)).congr_deriv (by ring)
  have hg' : ∀ᶠ v in 𝓝[>] y, (2 * (v - y) : ℝ) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact ne_of_gt (mul_pos (by norm_num) (sub_pos.mpr hv))
  have hNderiv0 := hasDerivAt_xiShiftedCanonicalAdmissionNorm_of_flatFace
    hy (n := m) (by omega) hface.1 hflat
  have hfa : Tendsto N (𝓝[>] y) (𝓝 0) := by
    have hc : Tendsto N (𝓝[>] y) (𝓝 (N y)) := by
      simpa only [N] using hNderiv0.continuousAt.mono_left nhdsWithin_le_nhds
    simpa only [hNzero] using hc
  have hga : Tendsto (fun v : ℝ => (v - y) ^ 2) (𝓝[>] y) (𝓝 0) := by
    have hcont : Tendsto (fun v : ℝ => (v - y) ^ 2) (𝓝 y) (𝓝 ((y - y) ^ 2)) :=
      ((continuousAt_id.sub continuousAt_const).pow 2)
    simpa using hcont.mono_left nhdsWithin_le_nhds
  have hga' : Tendsto ((fun x : ℝ => x - y) * (fun x : ℝ => x - y))
      (𝓝[>] y) (𝓝 0) := by
    apply hga.congr'
    filter_upwards with v
    simp only [Pi.mul_apply, pow_two]
  have hdiv : Tendsto (fun v => F v / (2 * (v - y)))
      (𝓝[>] y) (𝓝 (K / 2)) := by
    have h := hFslope.div_const 2
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with v hv
    change y < v at hv
    field_simp [sub_ne_zero.mpr hv.ne']
  have hquot := HasDerivAt.lhopital_zero_nhdsGT hff hgg hg' hfa hga' hdiv
  have hK : K / 2 = ((2 * (n + 2) + 1 : ℕ) : ℝ) *
      xiShiftedStrictFrontierTangentialSource n := by
    dsimp only [K, S, xiShiftedStrictFrontierTangentialSource, m, y]
    ring
  rw [hK] at hquot
  have hquot' : Tendsto (fun v => N v / (v - y) ^ 2) (𝓝[>] y)
      (𝓝 (((2 * (n + 2) + 1 : ℕ) : ℝ) *
        xiShiftedStrictFrontierTangentialSource n)) := by
    apply hquot.congr'
    filter_upwards with v
    simp only [Pi.mul_apply, pow_two]
  simpa only [N, m, y] using hquot'

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

/-- The tangential successor shear is itself exactly half the literal adaptive mixed completed
arithmetic source, with canonical admission performed at the frontier before packet formation. -/
theorem two_mul_xiShiftedStrictFrontierTangentialSource_eq_arithmeticSource
    {n : ℕ}
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    2 * xiShiftedStrictFrontierTangentialSource n =
      xiShiftedStrictFrontierTangentialArithmeticSource n := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hy0 : 0 ≤ y := by dsimp only [y]; linarith
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  have hsqrt0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hsqrt : 1 / 2 < Real.sqrt y := by
    nlinarith
  unfold xiShiftedStrictFrontierTangentialSource
  unfold xiShiftedStrictFrontierTangentialArithmeticSource
  change 2 * xiShiftedCanonicalAdmissionAdaptiveShear y (n + 2) = _
  rw [← hsq]
  exact two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hsqrt
    (HTGeometry.monicMomentAdmissionPolynomial
      (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 2))

/-- Positive side of the newborn norm at a strict frontier, in frontier rather than displacement
coordinates. -/
theorem eventually_pos_xiShiftedCanonicalAdmissionNorm_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    ∀ᶠ v in 𝓝[>] xiShiftedHigherBlockTerminalFrontier (n + 1),
      0 < xiShiftedCanonicalAdmissionNorm v (n + 2) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hy : 0 < y := by
    obtain ⟨u, hu⟩ := hne
    have hule := le_xiShiftedHigherBlockTerminalFrontier_of_mem hu
    exact lt_of_le_of_lt (hu.1.trans hule) hstrict
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment v k).re) (n + 3)).PosDef := by
    simpa only [y] using
      (xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
        (n := n + 1) (le_of_lt (hy.trans hv)) hv)
  have hhead : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment v k).re) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hhead]
  exact HTGeometry.monicOrthoNorm_pos_below
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)

/-- If the tangential successor source is positive, the preceding source wall has an exact finite
positive double-pole residue. -/
theorem tendsto_xiShiftedStrictFrontierQuadraticallyScaledChristoffelSourceWall_of_tangentialSource_pos
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hrem : xiShiftedStrictFrontierFirstOmittedRemainder n = 0)
    (hsourceNext : 0 < xiShiftedStrictFrontierTangentialSource n) :
    Tendsto (xiShiftedStrictFrontierQuadraticallyScaledChristoffelSourceWall n)
      (𝓝[>] xiShiftedHigherBlockTerminalFrontier (n + 1))
      (𝓝 (xiShiftedStrictFrontierQuadraticResidue n)) := by
  unfold xiShiftedStrictFrontierQuadraticResidue
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let source : ℝ → ℝ := fun v =>
    xiShiftedCanonicalAdmissionAdaptiveShear v (n + 1)
  let N : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v (n + 2)
  let b : ℝ := ((2 * (n + 2) + 1 : ℕ) : ℝ) *
    xiShiftedStrictFrontierTangentialSource n
  have hy : 0 < y := by
    obtain ⟨u, hu⟩ := hne
    have hule := le_xiShiftedHigherBlockTerminalFrontier_of_mem hu
    exact lt_of_le_of_lt (hu.1.trans hule) hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hhead : (xiShiftedMomentHankelMatrix y (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hsourceCont : ContinuousAt source y := by
    have h := continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment
      hy (n + 1) (ne_of_gt hhead.det_pos)
    simpa only [source, xiShiftedCanonicalAdmissionAdaptiveShear,
      HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial] using h
  have hsourceTendsto : Tendsto (fun v => source v / 16) (𝓝[>] y)
      (𝓝 (source y / 16)) :=
    (hsourceCont.div_const 16).mono_left nhdsWithin_le_nhds
  have hquad : Tendsto (fun v => N v / (v - y) ^ 2) (𝓝[>] y) (𝓝 b) := by
    simpa only [N, y, b] using
      tendsto_xiShiftedCanonicalAdmissionNorm_div_sq_at_strict_frontier_of_remainder_eq_zero
        hne hstrict hrem
  have hb : 0 < b := by dsimp only [b]; positivity
  have hinv : Tendsto (fun v => (N v / (v - y) ^ 2)⁻¹) (𝓝[>] y) (𝓝 b⁻¹) :=
    hquad.inv₀ (ne_of_gt hb)
  have hprod : Tendsto
      (fun v => source v / 16 * (N v / (v - y) ^ 2)⁻¹)
      (𝓝[>] y) (𝓝 (source y / (16 * b))) := by
    convert hsourceTendsto.mul hinv using 1
    field_simp [ne_of_gt hb]
  have hnorm :=
    eventually_pos_xiShiftedCanonicalAdmissionNorm_at_strict_frontier hne hstrict
  apply hprod.congr'
  filter_upwards [hnorm, self_mem_nhdsWithin] with v hNv hv
  have hN0 : N v ≠ 0 := by simpa only [N] using ne_of_gt hNv
  have hv0 : v - y ≠ 0 := sub_ne_zero.mpr hv.ne'
  dsimp only [xiShiftedStrictFrontierQuadraticallyScaledChristoffelSourceWall,
    xiShiftedCanonicalAdmissionChristoffelSourceWall, source, N, b, y]
  field_simp

/-- The exact double-pole residue is positive. -/
theorem xiShiftedStrictFrontier_quadraticResidue_pos_of_tangentialSource_pos
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hsourceNext : 0 < xiShiftedStrictFrontierTangentialSource n) :
    0 < xiShiftedStrictFrontierQuadraticResidue n := by
  have hsource :=
    xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier hne hstrict
  rw [xiShiftedStrictFrontierQuadraticResidue]
  exact div_pos hsource
    (mul_pos (by norm_num) (mul_pos (by positivity) hsourceNext))

/-- If both first remainder and successor source vanish, even squared-distance rescaling is
insufficient: the preceding source wall has infinite quadratic residue. -/
theorem tendsto_xiShiftedStrictFrontierQuadraticallyScaledChristoffelSourceWall_atTop_of_tangentialSource_eq_zero
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hrem : xiShiftedStrictFrontierFirstOmittedRemainder n = 0)
    (hsourceNext : xiShiftedStrictFrontierTangentialSource n = 0) :
    Tendsto (xiShiftedStrictFrontierQuadraticallyScaledChristoffelSourceWall n)
      (𝓝[>] xiShiftedHigherBlockTerminalFrontier (n + 1)) atTop := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let source : ℝ → ℝ := fun v =>
    xiShiftedCanonicalAdmissionAdaptiveShear v (n + 1)
  let N : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v (n + 2)
  have hy : 0 < y := by
    obtain ⟨u, hu⟩ := hne
    have hule := le_xiShiftedHigherBlockTerminalFrontier_of_mem hu
    exact lt_of_le_of_lt (hu.1.trans hule) hstrict
  have hsourcePos : 0 < source y := by
    simpa only [source, y] using
      xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier hne hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hhead : (xiShiftedMomentHankelMatrix y (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hsourceCont : ContinuousAt source y := by
    have h := continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment
      hy (n + 1) (ne_of_gt hhead.det_pos)
    simpa only [source, xiShiftedCanonicalAdmissionAdaptiveShear,
      HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial] using h
  have hsourceTendsto : Tendsto (fun v => source v / 16) (𝓝[>] y)
      (𝓝 (source y / 16)) :=
    (hsourceCont.div_const 16).mono_left nhdsWithin_le_nhds
  have hquad : Tendsto (fun v => N v / (v - y) ^ 2) (𝓝[>] y) (𝓝 0) := by
    have h :=
      tendsto_xiShiftedCanonicalAdmissionNorm_div_sq_at_strict_frontier_of_remainder_eq_zero
        hne hstrict hrem
    simpa only [N, y, hsourceNext, mul_zero] using h
  have hnorm :=
    eventually_pos_xiShiftedCanonicalAdmissionNorm_at_strict_frontier hne hstrict
  have hquadPos : ∀ᶠ v in 𝓝[>] y, 0 < N v / (v - y) ^ 2 := by
    filter_upwards [hnorm, self_mem_nhdsWithin] with v hNv hv
    exact div_pos (by simpa only [N] using hNv) (sq_pos_of_pos (sub_pos.mpr hv))
  have hquadWithin : Tendsto (fun v => N v / (v - y) ^ 2)
      (𝓝[>] y) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hquad hquadPos
  have hinv : Tendsto (fun v => (N v / (v - y) ^ 2)⁻¹)
      (𝓝[>] y) atTop := tendsto_inv_nhdsGT_zero.comp hquadWithin
  have hprod := Filter.Tendsto.pos_mul_atTop
    (div_pos hsourcePos (by norm_num)) hsourceTendsto hinv
  apply hprod.congr'
  filter_upwards [hnorm, self_mem_nhdsWithin] with v hNv hv
  have hN0 : N v ≠ 0 := by simpa only [N] using ne_of_gt hNv
  have hv0 : v - y ≠ 0 := sub_ne_zero.mpr hv.ne'
  dsimp only [xiShiftedStrictFrontierQuadraticallyScaledChristoffelSourceWall,
    xiShiftedCanonicalAdmissionChristoffelSourceWall, source, N, y]
  field_simp

/-- Exact contact-order-two law at one occupied strict frontier. -/
def XiShiftedStrictFrontierContactOrderTwoLaw (n : ℕ) : Prop :=
  let firstResidue := xiShiftedCanonicalAdmissionAdaptiveShear
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) /
    (16 * (-((2 * (n + 2) + 1 : ℕ) : ℝ) *
      xiShiftedStrictFrontierFirstOmittedRemainder n))
  let secondResidue := xiShiftedStrictFrontierQuadraticResidue n
  (xiShiftedStrictFrontierFirstOmittedRemainder n < 0 ∧
      Tendsto (xiShiftedStrictFrontierScaledChristoffelSourceWall n)
        (𝓝[>] (0 : ℝ)) (𝓝 firstResidue) ∧ 0 < firstResidue) ∨
  (xiShiftedStrictFrontierFirstOmittedRemainder n = 0 ∧
    ((0 < xiShiftedStrictFrontierTangentialSource n ∧
        Tendsto (xiShiftedStrictFrontierQuadraticallyScaledChristoffelSourceWall n)
          (𝓝[>] xiShiftedHigherBlockTerminalFrontier (n + 1))
          (𝓝 secondResidue) ∧ 0 < secondResidue) ∨
      (xiShiftedStrictFrontierTangentialSource n = 0 ∧
        Tendsto (xiShiftedStrictFrontierQuadraticallyScaledChristoffelSourceWall n)
          (𝓝[>] xiShiftedHigherBlockTerminalFrontier (n + 1)) atTop)))

/-- Every occupied strict frontier satisfies the exact simple/double/flatter contact trichotomy. -/
theorem xiShiftedStrictFrontier_contactOrderTwoLaw
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    XiShiftedStrictFrontierContactOrderTwoLaw n := by
  dsimp only [XiShiftedStrictFrontierContactOrderTwoLaw]
  have hremNonpos := xiShiftedStrictFrontierFirstOmittedRemainder_nonpos hne hstrict
  rcases hremNonpos.lt_or_eq with hrem | hrem
  · exact Or.inl ⟨hrem,
      tendsto_xiShiftedStrictFrontierScaledChristoffelSourceWall_of_remainder_neg
        hne hstrict hrem,
      xiShiftedStrictFrontier_residue_pos_of_remainder_neg hne hstrict hrem⟩
  · have hsourceNonneg :=
      xiShiftedStrictFrontierTangentialSource_nonneg_of_remainder_eq_zero
        hne hstrict hrem
    rcases hsourceNonneg.lt_or_eq with hsource | hsource
    · exact Or.inr ⟨hrem, Or.inl ⟨hsource,
        tendsto_xiShiftedStrictFrontierQuadraticallyScaledChristoffelSourceWall_of_tangentialSource_pos
          hne hstrict hrem hsource,
        xiShiftedStrictFrontier_quadraticResidue_pos_of_tangentialSource_pos
          hne hstrict hsource⟩⟩
    · exact Or.inr ⟨hrem, Or.inr ⟨hsource.symm,
        tendsto_xiShiftedStrictFrontierQuadraticallyScaledChristoffelSourceWall_atTop_of_tangentialSource_eq_zero
          hne hstrict hrem hsource.symm⟩⟩

/-- Cofinal source-first contact-order-two phase.  The exact identity in the middle conjunct makes
the successor coefficient a literal adaptive mixed completed arithmetic source, not a reporter. -/
def XiShiftedCofinalArithmeticSourceContactOrderTwoPhase : Prop :=
  ∀ A : ℝ, ∃ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      2 * xiShiftedStrictFrontierTangentialSource n =
        xiShiftedStrictFrontierTangentialArithmeticSource n ∧
      XiShiftedStrictFrontierContactOrderTwoLaw n

/-- False RH forces cofinally many literal arithmetic-source contact-order-two events. -/
theorem xiShiftedCofinalArithmeticSourceContactOrderTwoPhase_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) :
    XiShiftedCofinalArithmeticSourceContactOrderTwoPhase := by
  intro A
  obtain ⟨n, hne, hA, hstrict, _⟩ :=
    exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hnot
      (max A (1 / 4))
  have hA' : A < xiShiftedHigherBlockTerminalFrontier n :=
    lt_of_le_of_lt (le_max_left _ _) hA
  have hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) :=
    lt_trans (lt_of_le_of_lt (le_max_right _ _) hA) hstrict
  exact ⟨n, hne, hA', hstrict, hphysical,
    two_mul_xiShiftedStrictFrontierTangentialSource_eq_arithmeticSource hphysical,
    xiShiftedStrictFrontier_contactOrderTwoLaw hne hstrict⟩

/-- RH excludes the cofinal contact-order-two source phase. -/
theorem not_xiShiftedCofinalArithmeticSourceContactOrderTwoPhase_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ¬XiShiftedCofinalArithmeticSourceContactOrderTwoPhase := by
  intro hphase
  obtain ⟨n, hne, _⟩ := hphase 0
  rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
  exact Set.not_nonempty_empty hne

/-- **Closed second-contact arithmetic-source phase law.** -/
theorem riemannHypothesis_iff_not_xiShiftedCofinalArithmeticSourceContactOrderTwoPhase :
    RiemannHypothesis ↔ ¬XiShiftedCofinalArithmeticSourceContactOrderTwoPhase := by
  constructor
  · exact not_xiShiftedCofinalArithmeticSourceContactOrderTwoPhase_of_riemannHypothesis
  · intro hnotPhase
    by_contra hnotRH
    exact hnotPhase
      (xiShiftedCofinalArithmeticSourceContactOrderTwoPhase_of_not_riemannHypothesis hnotRH)

/-- Premise-free simple/double/flatter arithmetic-source contact dichotomy. -/
theorem riemannHypothesis_or_xiShiftedCofinalArithmeticSourceContactOrderTwoPhase :
    RiemannHypothesis ∨ XiShiftedCofinalArithmeticSourceContactOrderTwoPhase := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr
      (xiShiftedCofinalArithmeticSourceContactOrderTwoPhase_of_not_riemannHypothesis hRH)

end RHTower
