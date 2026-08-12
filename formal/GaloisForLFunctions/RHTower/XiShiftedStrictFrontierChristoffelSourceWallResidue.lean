import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierChristoffelSourceWall
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Strict-frontier Christoffel source-wall residue

At an occupied strict terminal frontier, the next canonical admission norm vanishes while the
preceding adaptive completed arithmetic source stays positive.  This file classifies the first
contact.  The first omitted monic remainder is forced to be nonpositive.  Negative remainder gives
an exact finite positive scaled residue; zero remainder gives infinite scaled residue.
-/

open Filter Matrix Polynomial Set Topology

namespace RHTower

/-- First omitted monic remainder at the strict frontier between levels `n` and `n + 1`. -/
noncomputable def xiShiftedStrictFrontierFirstOmittedRemainder (n : ℕ) : ℝ :=
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  xiShiftedHankelBoundaryMonicRemainder y
    (HTGeometry.monicMomentAdmissionVector
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2))

/-- Distance-rescaled actual adaptive source wall at the strict frontier. -/
noncomputable def xiShiftedStrictFrontierScaledChristoffelSourceWall
    (n : ℕ) (t : ℝ) : ℝ :=
  t * xiShiftedCanonicalAdmissionChristoffelSourceWall
    (xiShiftedHigherBlockTerminalFrontier (n + 1) + t) (n + 1)

/-- The next canonical admission norm is positive immediately to the right of every occupied
strict frontier. -/
theorem eventually_pos_xiShiftedCanonicalAdmissionNorm_add_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < xiShiftedCanonicalAdmissionNorm
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + t) (n + 2) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hy : 0 < y := by
    obtain ⟨u, hu⟩ := hne
    have hule := le_xiShiftedHigherBlockTerminalFrontier_of_mem hu
    exact lt_of_le_of_lt (hu.1.trans hule) hstrict
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hyt : y < y + t := lt_add_of_pos_right y ht
  have hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (y + t) k).re) (n + 3)).PosDef := by
    simpa only [y] using
      (xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
        (n := n + 1) (le_of_lt (hy.trans hyt)) hyt)
  have hhead : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (y + t) k).re) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm_of_head_posDef hhead]
  exact HTGeometry.monicOrthoNorm_pos_below
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)

/-- Exact right slope of the newborn admission norm at a strict frontier. -/
theorem tendsto_xiShiftedCanonicalAdmissionNorm_slope_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    Tendsto
      (fun t => t⁻¹ * xiShiftedCanonicalAdmissionNorm
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + t) (n + 2))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-((2 * (n + 2) + 1 : ℕ) : ℝ) *
        xiShiftedStrictFrontierFirstOmittedRemainder n)) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let c := HTGeometry.monicMomentAdmissionVector
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)
  have hy : 0 < y := by
    obtain ⟨u, hu⟩ := hne
    have hule := le_xiShiftedHigherBlockTerminalFrontier_of_mem hu
    exact lt_of_le_of_lt (hu.1.trans hule) hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hflat : xiShiftedMomentHankelMatrix y (n + 3) *ᵥ c = 0 := by
    simpa only [c] using
      xiShiftedCanonicalAdmissionVector_mem_ker_of_succ_posSemidef_not_posDef
        hface.1 hface.2.1 hface.2.2
  have hderiv := hasDerivAt_xiShiftedCanonicalAdmissionNorm_of_flatFace
    hy (n := n + 2) (by omega) hface.1 hflat
  have hzero : xiShiftedCanonicalAdmissionNorm y (n + 2) = 0 := by
    simpa only [y] using
      xiShiftedCanonicalAdmissionNorm_eq_zero_at_strict_frontier hne hstrict
  have hslope := hderiv.tendsto_slope_zero_right
  simpa only [hzero, sub_zero, smul_eq_mul, c, y,
    xiShiftedStrictFrontierFirstOmittedRemainder] using hslope

/-- Right-chamber positivity forces the first omitted monic remainder to be nonpositive. -/
theorem xiShiftedStrictFrontierFirstOmittedRemainder_nonpos
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    xiShiftedStrictFrontierFirstOmittedRemainder n ≤ 0 := by
  have hslope :=
    tendsto_xiShiftedCanonicalAdmissionNorm_slope_at_strict_frontier hne hstrict
  have hnorm :=
    eventually_pos_xiShiftedCanonicalAdmissionNorm_add_at_strict_frontier hne hstrict
  have hnonneg : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ t⁻¹ * xiShiftedCanonicalAdmissionNorm
        (xiShiftedHigherBlockTerminalFrontier (n + 1) + t) (n + 2) := by
    filter_upwards [hnorm, self_mem_nhdsWithin] with t hNt ht
    exact mul_nonneg (inv_nonneg.mpr ht.le) hNt.le
  have hderivNonneg : 0 ≤ -((2 * (n + 2) + 1 : ℕ) : ℝ) *
      xiShiftedStrictFrontierFirstOmittedRemainder n :=
    ge_of_tendsto hslope hnonneg
  have hfactor : 0 < ((2 * (n + 2) + 1 : ℕ) : ℝ) := by positivity
  nlinarith

/-- Negative first omitted remainder gives the exact finite positive residue of the actual
adaptive completed arithmetic source wall. -/
theorem tendsto_xiShiftedStrictFrontierScaledChristoffelSourceWall_of_remainder_neg
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hrem : xiShiftedStrictFrontierFirstOmittedRemainder n < 0) :
    Tendsto (xiShiftedStrictFrontierScaledChristoffelSourceWall n)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedCanonicalAdmissionAdaptiveShear
          (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) /
        (16 * (-((2 * (n + 2) + 1 : ℕ) : ℝ) *
          xiShiftedStrictFrontierFirstOmittedRemainder n)))) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let source : ℝ → ℝ := fun v =>
    xiShiftedCanonicalAdmissionAdaptiveShear v (n + 1)
  let N : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v (n + 2)
  let a : ℝ := -((2 * (n + 2) + 1 : ℕ) : ℝ) *
    xiShiftedStrictFrontierFirstOmittedRemainder n
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
  have hshift : Tendsto (fun t : ℝ => y + t) (𝓝 (0 : ℝ)) (𝓝 y) := by
    have hlim : Tendsto (fun t : ℝ => y + t) (𝓝 (0 : ℝ)) (𝓝 (y + 0)) :=
      tendsto_const_nhds.add tendsto_id
    simpa using hlim
  have hsource : Tendsto (fun t => source (y + t) / 16)
      (𝓝[>] (0 : ℝ)) (𝓝 (source y / 16)) := by
    exact ((hsourceCont.tendsto.comp hshift).div_const 16).mono_left nhdsWithin_le_nhds
  have hslope : Tendsto (fun t => t⁻¹ * N (y + t))
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    simpa only [N, y, a] using
      tendsto_xiShiftedCanonicalAdmissionNorm_slope_at_strict_frontier hne hstrict
  have ha : 0 < a := by
    dsimp only [a]
    have hfactor : 0 < ((2 * (n + 2) + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hinv : Tendsto (fun t => (t⁻¹ * N (y + t))⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 a⁻¹) := hslope.inv₀ (ne_of_gt ha)
  have hprod : Tendsto
      (fun t => source (y + t) / 16 * (t⁻¹ * N (y + t))⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (source y / (16 * a))) := by
    convert hsource.mul hinv using 1
    field_simp [ne_of_gt ha]
    <;> ring
  have hnorm :=
    eventually_pos_xiShiftedCanonicalAdmissionNorm_add_at_strict_frontier hne hstrict
  apply hprod.congr'
  filter_upwards [hnorm, self_mem_nhdsWithin] with t hNt ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hN0 : N (y + t) ≠ 0 := by simpa only [N, y] using ne_of_gt hNt
  dsimp only [xiShiftedStrictFrontierScaledChristoffelSourceWall,
    xiShiftedCanonicalAdmissionChristoffelSourceWall, source, N, y, a]
  field_simp
  <;> ring

/-- A transversal strict-frontier residue is strictly positive. -/
theorem xiShiftedStrictFrontier_residue_pos_of_remainder_neg
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hrem : xiShiftedStrictFrontierFirstOmittedRemainder n < 0) :
    0 < xiShiftedCanonicalAdmissionAdaptiveShear
          (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) /
        (16 * (-((2 * (n + 2) + 1 : ℕ) : ℝ) *
          xiShiftedStrictFrontierFirstOmittedRemainder n)) := by
  have hsource :=
    xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier hne hstrict
  have hfactor : 0 < ((2 * (n + 2) + 1 : ℕ) : ℝ) := by positivity
  have hden : 0 < -((2 * (n + 2) + 1 : ℕ) : ℝ) *
      xiShiftedStrictFrontierFirstOmittedRemainder n := by
    nlinarith
  exact div_pos hsource (mul_pos (by norm_num) hden)

/-- Tangential first contact has no finite scaled residue: the distance-rescaled source wall
itself tends to `+∞`. -/
theorem tendsto_xiShiftedStrictFrontierScaledChristoffelSourceWall_atTop_of_remainder_eq_zero
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hrem : xiShiftedStrictFrontierFirstOmittedRemainder n = 0) :
    Tendsto (xiShiftedStrictFrontierScaledChristoffelSourceWall n)
      (𝓝[>] (0 : ℝ)) atTop := by
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
  have hshift : Tendsto (fun t : ℝ => y + t) (𝓝 (0 : ℝ)) (𝓝 y) := by
    have hlim : Tendsto (fun t : ℝ => y + t) (𝓝 (0 : ℝ)) (𝓝 (y + 0)) :=
      tendsto_const_nhds.add tendsto_id
    simpa using hlim
  have hsource : Tendsto (fun t => source (y + t) / 16)
      (𝓝[>] (0 : ℝ)) (𝓝 (source y / 16)) := by
    exact ((hsourceCont.tendsto.comp hshift).div_const 16).mono_left nhdsWithin_le_nhds
  have hslope : Tendsto (fun t => t⁻¹ * N (y + t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h :=
      tendsto_xiShiftedCanonicalAdmissionNorm_slope_at_strict_frontier hne hstrict
    simpa only [N, y, hrem, mul_zero] using h
  have hnorm :=
    eventually_pos_xiShiftedCanonicalAdmissionNorm_add_at_strict_frontier hne hstrict
  have hslopePos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ * N (y + t) := by
    filter_upwards [hnorm, self_mem_nhdsWithin] with t hNt ht
    exact mul_pos (inv_pos.mpr ht) (by simpa only [N, y] using hNt)
  have hslopeWithin : Tendsto (fun t => t⁻¹ * N (y + t))
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hslope hslopePos
  have hinv : Tendsto (fun t => (t⁻¹ * N (y + t))⁻¹)
      (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero.comp hslopeWithin
  have hprod := Filter.Tendsto.pos_mul_atTop
    (div_pos hsourcePos (by norm_num)) hsource hinv
  apply hprod.congr'
  filter_upwards [hnorm, self_mem_nhdsWithin] with t hNt ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hN0 : N (y + t) ≠ 0 := by simpa only [N, y] using ne_of_gt hNt
  dsimp only [xiShiftedStrictFrontierScaledChristoffelSourceWall,
    xiShiftedCanonicalAdmissionChristoffelSourceWall, source, N, y]
  field_simp
  <;> ring

/-- **Exact strict-frontier contact-order law.**  Every occupied strict frontier has either a
finite positive transversal residue, explicitly determined by the negative first omitted monic
remainder, or infinite scaled residue at tangential contact. -/
theorem xiShiftedStrictFrontier_sourceWall_residue_dichotomy
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    let residue := xiShiftedCanonicalAdmissionAdaptiveShear
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) /
        (16 * (-((2 * (n + 2) + 1 : ℕ) : ℝ) *
          xiShiftedStrictFrontierFirstOmittedRemainder n))
    (xiShiftedStrictFrontierFirstOmittedRemainder n < 0 ∧
      Tendsto (xiShiftedStrictFrontierScaledChristoffelSourceWall n)
        (𝓝[>] (0 : ℝ)) (𝓝 residue) ∧
      0 < residue) ∨
    (xiShiftedStrictFrontierFirstOmittedRemainder n = 0 ∧
      Tendsto (xiShiftedStrictFrontierScaledChristoffelSourceWall n)
        (𝓝[>] (0 : ℝ)) atTop) := by
  dsimp only
  have hnonpos := xiShiftedStrictFrontierFirstOmittedRemainder_nonpos hne hstrict
  rcases hnonpos.lt_or_eq with hneg | hzero
  · exact Or.inl ⟨hneg,
      tendsto_xiShiftedStrictFrontierScaledChristoffelSourceWall_of_remainder_neg
        hne hstrict hneg,
      xiShiftedStrictFrontier_residue_pos_of_remainder_neg hne hstrict hneg⟩
  · exact Or.inr ⟨hzero,
      tendsto_xiShiftedStrictFrontierScaledChristoffelSourceWall_atTop_of_remainder_eq_zero
        hne hstrict hzero⟩

end RHTower
