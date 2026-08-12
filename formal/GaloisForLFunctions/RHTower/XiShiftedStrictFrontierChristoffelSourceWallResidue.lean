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

/-- Literal rational--Gamma minus von Mangoldt completed source divided by the newborn admission
norm, rescaled by distance from the strict frontier.  Its polynomial is the adaptive canonical
amplitude at the current square mass, so source formation precedes reflection aggregation. -/
noncomputable def xiShiftedStrictFrontierScaledArithmeticSourceWall
    (n : ℕ) (t : ℝ) : ℝ :=
  let v := xiShiftedHigherBlockTerminalFrontier (n + 1) + t
  t * (xiShiftedAdaptiveMixedCompletedArithmeticSource (Real.sqrt v)
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence (Real.sqrt v)) (n + 1)) /
    (32 * xiShiftedCanonicalAdmissionNorm v (n + 2)))

/-- In the physical square-mass chamber, the Christoffel source wall is exactly the literal
adaptive mixed completed arithmetic source over the next admission norm. -/
theorem xiShiftedCanonicalAdmissionChristoffelSourceWall_eq_arithmeticSource_div
    {v : ℝ} (hv : 1 / 4 < v) (n : ℕ) :
    xiShiftedCanonicalAdmissionChristoffelSourceWall v n =
      xiShiftedAdaptiveMixedCompletedArithmeticSource (Real.sqrt v)
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence (Real.sqrt v)) n) /
        (32 * xiShiftedCanonicalAdmissionNorm v (n + 1)) := by
  have hv0 : 0 ≤ v := by linarith
  have hsq : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv0
  have hsqrt0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  have hsqrt : 1 / 2 < Real.sqrt v := by nlinarith
  have hsource :=
    two_mul_xiShiftedCanonicalAdmissionChristoffelSourceWall_eq_arithmeticSource_div_nextNorm
      hsqrt n
  rw [hsq] at hsource
  calc
    xiShiftedCanonicalAdmissionChristoffelSourceWall v n =
        (2 * xiShiftedCanonicalAdmissionChristoffelSourceWall v n) / 2 := by ring
    _ = (xiShiftedAdaptiveMixedCompletedArithmeticSource (Real.sqrt v)
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence (Real.sqrt v)) n) /
        (16 * xiShiftedCanonicalAdmissionNorm v (n + 1))) / 2 := by rw [hsource]
    _ = xiShiftedAdaptiveMixedCompletedArithmeticSource (Real.sqrt v)
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence (Real.sqrt v)) n) /
        (32 * xiShiftedCanonicalAdmissionNorm v (n + 1)) := by ring

/-- Past the physical threshold, literal arithmetic-source and shear-coordinate scaled walls agree
on the entire positive germ of a strict frontier. -/
theorem eventuallyEq_xiShiftedStrictFrontierScaledArithmeticSourceWall
    {n : ℕ}
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    xiShiftedStrictFrontierScaledArithmeticSourceWall n =ᶠ[𝓝[>] (0 : ℝ)]
      xiShiftedStrictFrontierScaledChristoffelSourceWall n := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hv : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) + t := by linarith
  rw [xiShiftedStrictFrontierScaledArithmeticSourceWall,
    xiShiftedStrictFrontierScaledChristoffelSourceWall,
    xiShiftedCanonicalAdmissionChristoffelSourceWall_eq_arithmeticSource_div hv]

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
  have hnorm :=
    eventually_pos_xiShiftedCanonicalAdmissionNorm_add_at_strict_frontier hne hstrict
  apply hprod.congr'
  filter_upwards [hnorm, self_mem_nhdsWithin] with t hNt ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hN0 : N (y + t) ≠ 0 := by simpa only [N, y] using ne_of_gt hNt
  dsimp only [xiShiftedStrictFrontierScaledChristoffelSourceWall,
    xiShiftedCanonicalAdmissionChristoffelSourceWall, source, N, y, a]
  field_simp

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

/-- Literal arithmetic-source form of the exact strict-frontier contact-order law.  This is not an
orientation map or fixed linear reporter: the numerator is the adaptive mixed amplitude/completed
`P^sharp` aggregate formed at each current square mass. -/
theorem xiShiftedStrictFrontier_arithmeticSource_residue_dichotomy
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    let residue := xiShiftedCanonicalAdmissionAdaptiveShear
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) /
        (16 * (-((2 * (n + 2) + 1 : ℕ) : ℝ) *
          xiShiftedStrictFrontierFirstOmittedRemainder n))
    (xiShiftedStrictFrontierFirstOmittedRemainder n < 0 ∧
      Tendsto (xiShiftedStrictFrontierScaledArithmeticSourceWall n)
        (𝓝[>] (0 : ℝ)) (𝓝 residue) ∧
      0 < residue) ∨
    (xiShiftedStrictFrontierFirstOmittedRemainder n = 0 ∧
      Tendsto (xiShiftedStrictFrontierScaledArithmeticSourceWall n)
        (𝓝[>] (0 : ℝ)) atTop) := by
  dsimp only
  have heq :=
    eventuallyEq_xiShiftedStrictFrontierScaledArithmeticSourceWall (n := n) hphysical
  rcases xiShiftedStrictFrontier_sourceWall_residue_dichotomy hne hstrict with hfin | hinf
  · exact Or.inl ⟨hfin.1, hfin.2.1.congr' heq.symm, hfin.2.2⟩
  · exact Or.inr ⟨hinf.1, hinf.2.congr' heq.symm⟩

/-- False-RH phase in literal source-first coordinates: cofinally many physical strict frontiers
carry either their exact positive transversal residue or an infinite tangential scaled residue. -/
def XiShiftedCofinalArithmeticSourceResiduePhase : Prop :=
  ∀ A : ℝ, ∃ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      (let residue := xiShiftedCanonicalAdmissionAdaptiveShear
          (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) /
            (16 * (-((2 * (n + 2) + 1 : ℕ) : ℝ) *
              xiShiftedStrictFrontierFirstOmittedRemainder n))
       (xiShiftedStrictFrontierFirstOmittedRemainder n < 0 ∧
          Tendsto (xiShiftedStrictFrontierScaledArithmeticSourceWall n)
            (𝓝[>] (0 : ℝ)) (𝓝 residue) ∧ 0 < residue) ∨
       (xiShiftedStrictFrontierFirstOmittedRemainder n = 0 ∧
          Tendsto (xiShiftedStrictFrontierScaledArithmeticSourceWall n)
            (𝓝[>] (0 : ℝ)) atTop))

/-- False RH forces the cofinal literal arithmetic-source residue phase. -/
theorem xiShiftedCofinalArithmeticSourceResiduePhase_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) :
    XiShiftedCofinalArithmeticSourceResiduePhase := by
  intro A
  obtain ⟨n, hne, hA, hstrict, _⟩ :=
    exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hnot
      (max A (1 / 4))
  have hA' : A < xiShiftedHigherBlockTerminalFrontier n :=
    lt_of_le_of_lt (le_max_left _ _) hA
  have hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) :=
    lt_trans (lt_of_le_of_lt (le_max_right _ _) hA) hstrict
  exact ⟨n, hne, hA', hstrict,
    xiShiftedStrictFrontier_arithmeticSource_residue_dichotomy hne hstrict hphysical⟩

/-- RH excludes the cofinal arithmetic-source residue phase because every failure set is empty. -/
theorem not_xiShiftedCofinalArithmeticSourceResiduePhase_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ¬XiShiftedCofinalArithmeticSourceResiduePhase := by
  intro hphase
  obtain ⟨n, hne, _⟩ := hphase 0
  rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
  exact Set.not_nonempty_empty hne

/-- **Closed adaptive arithmetic-source phase law.**  RH is exactly absence of cofinally many
source-first strict-frontier contacts carrying either the explicit positive transversal residue or
an infinite tangential scaled residue.  No premises, schedules, orientations, or reporters remain. -/
theorem riemannHypothesis_iff_not_xiShiftedCofinalArithmeticSourceResiduePhase :
    RiemannHypothesis ↔ ¬XiShiftedCofinalArithmeticSourceResiduePhase := by
  constructor
  · exact not_xiShiftedCofinalArithmeticSourceResiduePhase_of_riemannHypothesis
  · intro hnotPhase
    by_contra hnotRH
    exact hnotPhase
      (xiShiftedCofinalArithmeticSourceResiduePhase_of_not_riemannHypothesis hnotRH)

/-- Premise-free arithmetic-source contact dichotomy. -/
theorem riemannHypothesis_or_xiShiftedCofinalArithmeticSourceResiduePhase :
    RiemannHypothesis ∨ XiShiftedCofinalArithmeticSourceResiduePhase := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · exact Or.inr
      (xiShiftedCofinalArithmeticSourceResiduePhase_of_not_riemannHypothesis hRH)

end RHTower
