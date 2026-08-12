import GaloisForLFunctions.RHTower.SoninCofinalReporterClockCommutatorSeam
import GaloisForLFunctions.RHTower.FisherDeconvolvedSameCarrierOrientationLaw
import GaloisForLFunctions.RHTower.SourceHorizontalAbelianClassLawApertureEvacuation
import GaloisForLFunctions.RHTower.SourceZeroHorizontalCarrier

/-!
# Signed complex-phase Sonin--Fisher splice

The real Fisher landing is positive and therefore erases reflection orientation.  This module
retains the unitary logarithmic phase before scalarization.  It first proves the complex critical
Euler limit along every fixed inward direction and then compares the reflection pair `+it`, `-it`
coordinate.  On the Xi strip that odd coordinate vanishes only at neutral horizontal grade.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- Complex critical ray with direction `1+u`. -/
def soninComplexCriticalPath (u : ℂ) (sigma : ℝ) : ℂ :=
  1 + (1 + u) * ((sigma - 1 : ℝ) : ℂ)

@[simp]
theorem soninComplexCriticalPath_zero (sigma : ℝ) :
    soninComplexCriticalPath 0 sigma = (sigma : ℂ) := by
  rw [soninComplexCriticalPath]
  push_cast
  ring

private theorem one_add_ne_zero_of_re_nonneg {u : ℂ} (hu : 0 ≤ u.re) :
    1 + u ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [add_re, one_re, zero_re] at hre
  linarith

theorem tendsto_soninComplexCriticalPath (u : ℂ) :
    Tendsto (soninComplexCriticalPath u)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hbase : Tendsto (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have hcont : Continuous (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ)) := by
      fun_prop
    simpa using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hone : Tendsto (fun _ : ℝ => (1 : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := tendsto_const_nhds
  have hc : Tendsto (fun _ : ℝ => (1 + u : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 + u)) := tendsto_const_nhds
  change Tendsto (fun sigma : ℝ =>
    1 + (1 + u) * ((sigma - 1 : ℝ) : ℂ))
    (nhdsWithin 1 (Set.Ioi 1)) (nhds 1)
  simpa only [add_zero, mul_zero] using hone.add (hc.mul hbase)

theorem tendsto_soninComplexCriticalPath_punctured
    {u : ℂ} (hu : 0 ≤ u.re) :
    Tendsto (soninComplexCriticalPath u)
      (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 1 ({1} : Set ℂ)ᶜ) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact tendsto_soninComplexCriticalPath u
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    have heps : ((sigma - 1 : ℝ) : ℂ) ≠ 0 := by
      exact ofReal_ne_zero.mpr (sub_ne_zero.mpr hsigma.ne')
    have hc : 1 + u ≠ 0 := one_add_ne_zero_of_re_nonneg hu
    change soninComplexCriticalPath u sigma ≠ 1
    rw [soninComplexCriticalPath, add_ne_left]
    exact mul_ne_zero hc heps

theorem tendsto_two_mul_soninComplexCriticalPath :
    Tendsto (fun sigma : ℝ => 2 * soninComplexCriticalPath u sigma)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (2 : ℂ)) := by
  have hpath := tendsto_soninComplexCriticalPath u
  simpa using (tendsto_const_nhds.mul hpath : Tendsto
    (fun sigma : ℝ => (2 : ℂ) * soninComplexCriticalPath u sigma)
    (nhdsWithin 1 (Set.Ioi 1)) (nhds ((2 : ℂ) * 1)))

/-- Pole-normalized squarefree partition on an arbitrary fixed inward complex ray. -/
theorem tendsto_sub_one_mul_squarefreePartition_complexPath
    {u : ℂ} (hu : 0 ≤ u.re) :
    Tendsto (fun sigma : ℝ =>
      ((sigma - 1 : ℝ) : ℂ) *
        GaloisForLFunctions.squarefreePartition
          (soninComplexCriticalPath u sigma))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((1 + u)⁻¹ / riemannZeta (2 : ℂ))) := by
  let l := nhdsWithin (1 : ℝ) (Set.Ioi 1)
  have hpath := tendsto_soninComplexCriticalPath_punctured hu
  have hres := riemannZeta_residue_one.comp hpath
  have hdenPath := tendsto_two_mul_soninComplexCriticalPath (u := u)
  have hden : Tendsto (fun sigma : ℝ =>
      riemannZeta (2 * soninComplexCriticalPath u sigma)) l
      (nhds (riemannZeta (2 : ℂ))) := by
    exact (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp
      hdenPath
  have hzetaTwo : riemannZeta (2 : ℂ) ≠ 0 := by
    rw [riemannZeta_two]
    exact div_ne_zero (pow_ne_zero 2 (ofReal_ne_zero.mpr Real.pi_ne_zero))
      (by norm_num)
  have hconst : Tendsto (fun _ : ℝ => (1 + u)⁻¹) l
      (nhds (1 + u)⁻¹) := tendsto_const_nhds
  have hnum := hconst.mul hres
  have hmain : Tendsto (fun sigma : ℝ =>
      ((1 + u)⁻¹ *
        ((soninComplexCriticalPath u sigma - 1) *
          riemannZeta (soninComplexCriticalPath u sigma))) /
        riemannZeta (2 * soninComplexCriticalPath u sigma)) l
      (nhds (((1 + u)⁻¹ * 1) / riemannZeta (2 : ℂ))) :=
    hnum.div hden hzetaTwo
  convert hmain using 1
  · funext sigma
    change ((sigma - 1 : ℝ) : ℂ) *
        (riemannZeta (soninComplexCriticalPath u sigma) /
          riemannZeta (2 * soninComplexCriticalPath u sigma)) =
      (1 + u)⁻¹ *
        ((soninComplexCriticalPath u sigma - 1) *
          riemannZeta (soninComplexCriticalPath u sigma)) /
        riemannZeta (2 * soninComplexCriticalPath u sigma)
    rw [soninComplexCriticalPath]
    by_cases hs : sigma = 1
    · subst sigma
      simp
    · have hc := one_add_ne_zero_of_re_nonneg hu
      have heps : ((sigma - 1 : ℝ) : ℂ) ≠ 0 := by
        exact ofReal_ne_zero.mpr (sub_ne_zero.mpr hs)
      field_simp [hc, heps]
      ring
  · simp

/-- Pole-normalized squarefree logarithmic current on a fixed inward complex ray. -/
theorem tendsto_sub_one_mul_squarefreeFixedCurrent_complexPath
    {u : ℂ} (hu : 0 ≤ u.re) :
    Tendsto (fun sigma : ℝ =>
      ((sigma - 1 : ℝ) : ℂ) *
        GaloisForLFunctions.squarefreeFixedCurrent
          (soninComplexCriticalPath u sigma))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 + u)⁻¹) := by
  let l := nhdsWithin (1 : ℝ) (Set.Ioi 1)
  have hpathPunctured := tendsto_soninComplexCriticalPath_punctured hu
  have hprincipal := neg_logDeriv_zeta_residue.comp hpathPunctured
  have hpath := tendsto_soninComplexCriticalPath u
  have hsub : Tendsto (fun sigma : ℝ =>
      soninComplexCriticalPath u sigma - 1) l (nhds 0) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℂ)) l (nhds 1) :=
      tendsto_const_nhds
    simpa using hpath.sub hone
  have htwoFlux : Tendsto
      ((fun z : ℂ => infinitePrimeFlux (2 * z)) ∘
        soninComplexCriticalPath u) l
      (nhds (infinitePrimeFlux (2 : ℂ))) := by
    have hcont := (GaloisForLFunctions.differentiableAt_infinitePrimeFlux_two_mul
      (s := (1 : ℂ)) (by norm_num)).continuousAt.tendsto
    simpa only [mul_one] using hcont.comp hpath
  have hcorrection : Tendsto (fun sigma : ℝ =>
      (soninComplexCriticalPath u sigma - 1) *
        (2 * infinitePrimeFlux
          (2 * soninComplexCriticalPath u sigma))) l (nhds 0) := by
    have htwoConst : Tendsto (fun _ : ℝ => (2 : ℂ)) l (nhds 2) :=
      tendsto_const_nhds
    have htwo : Tendsto (fun sigma : ℝ =>
        2 * infinitePrimeFlux (2 * soninComplexCriticalPath u sigma)) l
        (nhds (2 * infinitePrimeFlux (2 : ℂ))) := by
      simpa only [Function.comp_apply] using htwoConst.mul htwoFlux
    simpa using hsub.mul htwo
  have hnormalized : Tendsto (fun sigma : ℝ =>
      (soninComplexCriticalPath u sigma - 1) *
        GaloisForLFunctions.squarefreeFixedCurrent
          (soninComplexCriticalPath u sigma)) l (nhds 1) := by
    have hmain := hprincipal.sub hcorrection
    convert hmain using 1
    · funext sigma
      simp only [Function.comp_apply,
        GaloisForLFunctions.squarefreeFixedCurrent,
        infinitePrimeFlux, logDeriv_apply]
      ring
    · simp
  have hconst : Tendsto (fun _ : ℝ => (1 + u)⁻¹) l
      (nhds (1 + u)⁻¹) := tendsto_const_nhds
  have hscaled := hconst.mul hnormalized
  convert hscaled using 1
  · funext sigma
    rw [soninComplexCriticalPath]
    have hc := one_add_ne_zero_of_re_nonneg hu
    by_cases hs : sigma = 1
    · subst sigma
      simp
    · have heps : ((sigma - 1 : ℝ) : ℂ) ≠ 0 := by
        exact ofReal_ne_zero.mpr (sub_ne_zero.mpr hs)
      field_simp [hc, heps]
      ring
  · simp

/-- The squarefree source overlap has the full holomorphic critical profile `1/(1+u)`. -/
theorem tendsto_squarefreeBoundaryOverlap_complexCritical
    {u : ℂ} (hu : 0 ≤ u.re) :
    Tendsto (fun sigma : ℝ =>
      GaloisForLFunctions.squarefreeBoundaryOverlap
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) u)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 + u)⁻¹) := by
  let l := nhdsWithin (1 : ℝ) (Set.Ioi 1)
  have hnum := tendsto_sub_one_mul_squarefreePartition_complexPath hu
  have hden := tendsto_sub_one_mul_squarefreePartition_complexPath
    (u := (0 : ℂ)) (by norm_num)
  have hzetaTwo : riemannZeta (2 : ℂ) ≠ 0 := by
    rw [riemannZeta_two]
    exact div_ne_zero (pow_ne_zero 2 (ofReal_ne_zero.mpr Real.pi_ne_zero))
      (by norm_num)
  have htarget : (1 : ℂ) / riemannZeta (2 : ℂ) ≠ 0 :=
    div_ne_zero one_ne_zero hzetaTwo
  have htarget' : (1 + (0 : ℂ))⁻¹ / riemannZeta (2 : ℂ) ≠ 0 := by
    simpa using htarget
  have hquot := hnum.div hden htarget'
  have hlimit :
      ((1 + u)⁻¹ / riemannZeta (2 : ℂ)) /
          ((1 + (0 : ℂ))⁻¹ / riemannZeta (2 : ℂ)) =
        (1 + u)⁻¹ := by
    have hc := one_add_ne_zero_of_re_nonneg hu
    simp only [add_zero, inv_one, one_div]
    field_simp [hc, hzetaTwo]
  rw [hlimit] at hquot
  refine Tendsto.congr' ?_ hquot
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  have heps : ((sigma - 1 : ℝ) : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (sub_ne_zero.mpr hsigma.ne')
  have hpart : GaloisForLFunctions.squarefreePartition (sigma : ℂ) ≠ 0 :=
    GaloisForLFunctions.squarefreePartition_ne_zero (by simpa using hsigma)
  simp only [GaloisForLFunctions.squarefreeBoundaryOverlap,
    soninComplexCriticalPath]
  have hpath : (sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ) =
      1 + (1 + u) * ((sigma - 1 : ℝ) : ℂ) := by
    push_cast
    ring
  have hzeroPath : 1 + (1 + (0 : ℂ)) * ((sigma - 1 : ℝ) : ℂ) =
      (sigma : ℂ) := by
    push_cast
    ring
  simp only [Pi.div_apply]
  rw [hpath, hzeroPath]
  field_simp [heps, hpart]

/-- Full holomorphic squarefree Fisher profile at the critical boundary. -/
theorem tendsto_squarefreeFisherScore_complexCritical
    {u : ℂ} (hu : 0 ≤ u.re) :
    Tendsto (fun sigma : ℝ =>
      GaloisForLFunctions.squarefreeFisherScore
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) u)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (2 * u / (1 + u) ^ 2)) := by
  let l := nhdsWithin (1 : ℝ) (Set.Ioi 1)
  have hoverlap := tendsto_squarefreeBoundaryOverlap_complexCritical hu
  have hbase := tendsto_sub_one_mul_squarefreeFixedCurrent_complexPath
    (u := (0 : ℂ)) (by norm_num)
  have hshift := tendsto_sub_one_mul_squarefreeFixedCurrent_complexPath hu
  have hdiff := hbase.sub hshift
  have htwo : Tendsto (fun _ : ℝ => (2 : ℂ)) l (nhds 2) :=
    tendsto_const_nhds
  have hmain : Tendsto (fun sigma : ℝ =>
      2 * GaloisForLFunctions.squarefreeBoundaryOverlap
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) u *
        (((sigma - 1 : ℝ) : ℂ) *
            GaloisForLFunctions.squarefreeFixedCurrent
              (soninComplexCriticalPath 0 sigma) -
          ((sigma - 1 : ℝ) : ℂ) *
            GaloisForLFunctions.squarefreeFixedCurrent
              (soninComplexCriticalPath u sigma))) l
      (nhds (2 * (1 + u)⁻¹ *
        ((1 + (0 : ℂ))⁻¹ - (1 + u)⁻¹))) :=
    (htwo.mul hoverlap).mul hdiff
  have hlimit : 2 * (1 + u)⁻¹ *
        ((1 + (0 : ℂ))⁻¹ - (1 + u)⁻¹) =
      2 * u / (1 + u) ^ 2 := by
    have hc := one_add_ne_zero_of_re_nonneg hu
    field_simp [hc]
    ring
  rw [hlimit] at hmain
  refine Tendsto.congr' ?_ hmain
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  have hsigmaC : 1 < (sigma : ℂ).re := by simpa using hsigma
  have hshiftRe : 1 < ((sigma : ℂ) +
      u * ((sigma - 1 : ℝ) : ℂ)).re := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im]
    nlinarith
  rw [GaloisForLFunctions.squarefreeFisherScore_eq_fixedCurrent_difference
    hsigmaC hshiftRe]
  have hpath : (sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ) =
      soninComplexCriticalPath u sigma := by
    rw [soninComplexCriticalPath]
    push_cast
    ring
  rw [hpath, soninComplexCriticalPath_zero]
  ring

/-- Actual complex phase-damped Hilbert coefficient has the same holomorphic critical profile. -/
theorem tendsto_inner_fisherTangent_complexDamped_criticalSequence
    {u : ℂ} (hu : 0 ≤ u.re) :
    Tendsto (fun j : ℕ =>
      inner ℂ
        (infiniteMobiusCriticalFisherTangentLp
          (soninMobiusCriticalSigmaSequence j)
          (soninMobiusCriticalSigmaSequence_gt_one j))
        (infiniteMobiusCriticalComplexDampedSignedWeightLp
          (soninMobiusCriticalSigmaSequence j) u
          (soninMobiusCriticalSigmaSequence_gt_one j) hu))
      atTop (nhds (2 * u / (1 + u) ^ 2)) := by
  have hscore := (tendsto_squarefreeFisherScore_complexCritical hu).comp
    tendsto_soninMobiusCriticalSigmaSequence
  refine Tendsto.congr' ?_ hscore
  filter_upwards with j
  have hsigma := soninMobiusCriticalSigmaSequence_gt_one j
  have hshift : 1 <
      (((soninMobiusCriticalSigmaSequence j : ℝ) : ℂ) +
        u * (((soninMobiusCriticalSigmaSequence j - 1 : ℝ) : ℂ))).re := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im]
    nlinarith
  simpa only [Function.comp_apply] using
    (inner_fisherTangent_complexDamped_eq_squarefreeFisherScore
      hsigma hu hshift).symm

/-- Fixed complex Hardy-node score survives the non-equivariant Sonin pullback. -/
theorem tendsto_soninCofinal_complexFisherScore
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    Tendsto (fun N =>
      inner ℂ
        (soninCofinalSourceCorner a c d r hc hcd hr N
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma))
        (soninCofinalSourceCorner a c d r hc hcd hr N
          (infiniteMobiusCriticalComplexDampedSignedWeightLp
            sigma u hsigma hu)))
      atTop
      (nhds (inner ℂ
        (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
        (infiniteMobiusCriticalComplexDampedSignedWeightLp
          sigma u hsigma hu))) := by
  simp_rw [inner_soninCofinalSourceCorner_eq_pullback]
  have hpull : Tendsto (fun N =>
      soninCofinalPositiveSourcePullback a c d r hc hcd hr N
        (infiniteMobiusCriticalComplexDampedSignedWeightLp sigma u hsigma hu))
      atTop (nhds
        (infiniteMobiusCriticalComplexDampedSignedWeightLp sigma u hsigma hu)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact tendsto_norm_soninCofinalPositiveSourcePullback_sub
      a c d r ha hc hcd hda hr harc
        (infiniteMobiusCriticalComplexDampedSignedWeightLp sigma u hsigma hu)
  exact Filter.Tendsto.inner (𝕜 := ℂ)
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => infiniteMobiusCriticalFisherTangentLp sigma hsigma)
      atTop (nhds (infiniteMobiusCriticalFisherTangentLp sigma hsigma)))
    hpull

/-- Finite Sonin score at one critical level and one complex phase. -/
def soninCofinalCriticalComplexFisherScore
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (u : ℂ) (hu : 0 ≤ u.re) (j N : ℕ) : ℂ :=
  inner ℂ
    (soninCofinalSourceCorner a c d r hc hcd hr N
      (infiniteMobiusCriticalFisherTangentLp
        (soninMobiusCriticalSigmaSequence j)
        (soninMobiusCriticalSigmaSequence_gt_one j)))
    (soninCofinalSourceCorner a c d r hc hcd hr N
      (infiniteMobiusCriticalComplexDampedSignedWeightLp
        (soninMobiusCriticalSigmaSequence j) u
        (soninMobiusCriticalSigmaSequence_gt_one j) hu))

/-- One cofinal Sonin diagonal retains an arbitrary inward complex phase and
converges to its full holomorphic Fisher profile. -/
theorem exists_soninCofinalCriticalComplexFisherScore_diagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (u : ℂ) (hu : 0 ≤ u.re) :
    ∃ Nseq : ℕ → ℕ,
      (∀ j, j < Nseq j) ∧
      Tendsto (fun j => soninCofinalCriticalComplexFisherScore
        a c d r hc hcd hr u hu j (Nseq j))
        atTop (nhds (2 * u / (1 + u) ^ 2)) := by
  let sourceScore : ℕ → ℂ := fun j =>
    inner ℂ
      (infiniteMobiusCriticalFisherTangentLp
        (soninMobiusCriticalSigmaSequence j)
        (soninMobiusCriticalSigmaSequence_gt_one j))
      (infiniteMobiusCriticalComplexDampedSignedWeightLp
        (soninMobiusCriticalSigmaSequence j) u
        (soninMobiusCriticalSigmaSequence_gt_one j) hu)
  let F : ℕ → ℕ → ℝ := fun j N =>
    dist (soninCofinalCriticalComplexFisherScore
      a c d r hc hcd hr u hu j N) (sourceScore j)
  have happrox : ∀ j : ℕ, ∀ ε > 0, ∃ M, j < M ∧ F j M < ε := by
    intro j ε hε
    have hfixed := tendsto_soninCofinal_complexFisherScore
      a c d r ha hc hcd hda hr harc
      (soninMobiusCriticalSigmaSequence j) u
      (soninMobiusCriticalSigmaSequence_gt_one j) hu
    rw [Metric.tendsto_atTop] at hfixed
    obtain ⟨N, hN⟩ := hfixed ε hε
    refine ⟨max N (j + 1), by omega, ?_⟩
    exact hN _ (le_max_left _ _)
  obtain ⟨Nseq, hcofinal, herror⟩ :=
    GaloisForLFunctions.RHTower.exists_diagonal_lt happrox
  refine ⟨Nseq, hcofinal, ?_⟩
  have hsource : Tendsto sourceScore atTop
      (nhds (2 * u / (1 + u) ^ 2)) := by
    exact tendsto_inner_fisherTangent_complexDamped_criticalSequence hu
  exact GaloisForLFunctions.RHTower.tendsto_of_dist_lt_inv hsource herror

/-- Reflection-odd complex-phase Fisher profile. -/
def soninCriticalPhaseOddFisherProfile (t : ℝ) : ℂ :=
  4 * I * t * (1 - t ^ 2) / (1 + t ^ 2) ^ 2

theorem soninCriticalPhaseOddFisherProfile_eq_difference (t : ℝ) :
    soninCriticalPhaseOddFisherProfile t =
      2 * (I * t) / (1 + I * t) ^ 2 -
        2 * (-I * t) / (1 - I * t) ^ 2 := by
  rw [soninCriticalPhaseOddFisherProfile]
  have hplus : (1 : ℂ) + I * t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hminus : (1 : ℂ) - I * t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hrealR : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have hreal : (1 + (t : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hrealR
  field_simp [hplus, hminus, hreal]
  ring_nf
  simp [I_sq]
  ring

theorem soninCriticalPhaseOddFisherProfile_eq_zero_iff
    {t : ℝ} (ht : |t| < 1) :
    soninCriticalPhaseOddFisherProfile t = 0 ↔ t = 0 := by
  constructor
  · intro hz
    rw [soninCriticalPhaseOddFisherProfile] at hz
    have hbaseR : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
    have hbase : (1 + (t : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hbaseR
    have hden : (1 + (t : ℂ) ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hbase
    have hnum := (div_eq_zero_iff.mp hz).resolve_right hden
    simp only [mul_eq_zero, ofReal_eq_zero, I_ne_zero,
      OfNat.ofNat_ne_zero, false_or] at hnum
    rcases hnum with ht0 | hfactor
    · exact ht0
    · have hfactorR : 1 - t ^ 2 = 0 := by exact_mod_cast hfactor
      have hsquare : t ^ 2 = 1 := by linarith
      have hsqlt : t ^ 2 < 1 := by
        nlinarith [sq_abs t, abs_nonneg t]
      linarith
  · rintro rfl
    simp [soninCriticalPhaseOddFisherProfile]

/-- Shared-depth signed score retaining the two complex phase orientations. -/
def soninCofinalCriticalPhaseOddFisherScore
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (t : ℝ) (j N : ℕ) : ℂ :=
  soninCofinalCriticalComplexFisherScore
      a c d r hc hcd hr (I * t) (by simp) j N -
    soninCofinalCriticalComplexFisherScore
      a c d r hc hcd hr (-I * t) (by simp) j N

/-- SOURCE-ORIENTATION PRODUCER: one common cofinal finite Sonin schedule
retains both reflection orientations and converges to the explicit odd
horizontal profile.  In the retained strip this profile annihilates exactly
the neutral class. -/
theorem exists_soninCofinalCriticalPhaseOddFisherScore_diagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (t : ℝ) :
    ∃ Nseq : ℕ → ℕ,
      (∀ j, j < Nseq j) ∧
      Tendsto (fun j => soninCofinalCriticalPhaseOddFisherScore
        a c d r hc hcd hr t j (Nseq j))
        atTop (nhds (soninCriticalPhaseOddFisherProfile t)) := by
  let plusSource : ℕ → ℂ := fun j =>
    inner ℂ
      (infiniteMobiusCriticalFisherTangentLp
        (soninMobiusCriticalSigmaSequence j)
        (soninMobiusCriticalSigmaSequence_gt_one j))
      (infiniteMobiusCriticalComplexDampedSignedWeightLp
        (soninMobiusCriticalSigmaSequence j) (I * t)
        (soninMobiusCriticalSigmaSequence_gt_one j) (by simp))
  let minusSource : ℕ → ℂ := fun j =>
    inner ℂ
      (infiniteMobiusCriticalFisherTangentLp
        (soninMobiusCriticalSigmaSequence j)
        (soninMobiusCriticalSigmaSequence_gt_one j))
      (infiniteMobiusCriticalComplexDampedSignedWeightLp
        (soninMobiusCriticalSigmaSequence j) (-I * t)
        (soninMobiusCriticalSigmaSequence_gt_one j) (by simp))
  let sourceOdd : ℕ → ℂ := fun j => plusSource j - minusSource j
  let F : ℕ → ℕ → ℝ := fun j N =>
    dist (soninCofinalCriticalPhaseOddFisherScore
      a c d r hc hcd hr t j N) (sourceOdd j)
  have happrox : ∀ j : ℕ, ∀ ε > 0, ∃ M, j < M ∧ F j M < ε := by
    intro j ε hε
    have hplus := tendsto_soninCofinal_complexFisherScore
      a c d r ha hc hcd hda hr harc
      (soninMobiusCriticalSigmaSequence j) (I * t)
      (soninMobiusCriticalSigmaSequence_gt_one j) (by simp)
    have hminus := tendsto_soninCofinal_complexFisherScore
      a c d r ha hc hcd hda hr harc
      (soninMobiusCriticalSigmaSequence j) (-I * t)
      (soninMobiusCriticalSigmaSequence_gt_one j) (by simp)
    have hodd : Tendsto (fun N =>
        soninCofinalCriticalPhaseOddFisherScore
          a c d r hc hcd hr t j N) atTop (nhds (sourceOdd j)) := by
      exact hplus.sub hminus
    rw [Metric.tendsto_atTop] at hodd
    obtain ⟨N, hN⟩ := hodd ε hε
    refine ⟨max N (j + 1), by omega, ?_⟩
    exact hN _ (le_max_left _ _)
  obtain ⟨Nseq, hcofinal, herror⟩ :=
    GaloisForLFunctions.RHTower.exists_diagonal_lt happrox
  refine ⟨Nseq, hcofinal, ?_⟩
  have hplusSource : Tendsto plusSource atTop
      (nhds (2 * (I * t) / (1 + I * t) ^ 2)) :=
    tendsto_inner_fisherTangent_complexDamped_criticalSequence (by simp)
  have hminusSource : Tendsto minusSource atTop
      (nhds (2 * (-I * t) / (1 - I * t) ^ 2)) := by
    convert tendsto_inner_fisherTangent_complexDamped_criticalSequence
      (u := -I * t) (by simp) using 1
    all_goals ring_nf
  have hsourceOdd : Tendsto sourceOdd atTop
      (nhds (soninCriticalPhaseOddFisherProfile t)) := by
    rw [soninCriticalPhaseOddFisherProfile_eq_difference]
    exact hplusSource.sub hminusSource
  exact GaloisForLFunctions.RHTower.tendsto_of_dist_lt_inv hsourceOdd herror

/-! ## Multiplicity-labelled Xi specialization -/

/-- Signed Sonin phase profile attached before summing any Xi divisor copies. -/
def xiZeroSoninCriticalPhaseOddFisherProfile (q : XiZeroCopy) : ℂ :=
  soninCriticalPhaseOddFisherProfile
    (primeDepthBVWoldXiCenteredRate q.1)

/-- The new signed Sonin source profile has exactly the horizontal Xi radical. -/
theorem xiZeroSoninCriticalPhaseOddFisherProfile_eq_zero_iff
    (q : XiZeroCopy) :
    xiZeroSoninCriticalPhaseOddFisherProfile q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [xiZeroSoninCriticalPhaseOddFisherProfile,
    soninCriticalPhaseOddFisherProfile_eq_zero_iff
      (sourceHorizontalXiCenteredRate_abs_lt_one q),
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Every multiplicity-labelled Xi divisor copy has one common finite Sonin
schedule carrying both reflected complex phases.  Its limit vanishes exactly
when that copy is on the critical line. -/
theorem exists_xiZeroSoninCofinalCriticalPhaseOddFisherScore_diagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (q : XiZeroCopy) :
    ∃ Nseq : ℕ → ℕ,
      (∀ j, j < Nseq j) ∧
      Tendsto (fun j => soninCofinalCriticalPhaseOddFisherScore
        a c d r hc hcd hr (primeDepthBVWoldXiCenteredRate q.1)
          j (Nseq j))
        atTop (nhds (xiZeroSoninCriticalPhaseOddFisherProfile q)) ∧
      (xiZeroSoninCriticalPhaseOddFisherProfile q = 0 ↔
        (q.1 : ℂ).re = 1 / 2) := by
  obtain ⟨Nseq, hcofinal, hlimit⟩ :=
    exists_soninCofinalCriticalPhaseOddFisherScore_diagonal
      a c d r ha hc hcd hda hr harc
        (primeDepthBVWoldXiCenteredRate q.1)
  exact ⟨Nseq, hcofinal, hlimit,
    xiZeroSoninCriticalPhaseOddFisherProfile_eq_zero_iff q⟩

/-- **Horizontal-carrier identification.**  The signed Sonin phase and the
complete source-zero horizontal carrier have the same zero fibre, copy by
copy and before any multiplicity sum.  This joins the analytic Sonin limit to
the resolution/prime-Bockstein carrier without a bounded scalar reader. -/
theorem xiZeroSoninCriticalPhaseOddFisherProfile_eq_zero_iff_sourceCarrier
    (K : ℕ) (q : XiZeroCopy) :
    xiZeroSoninCriticalPhaseOddFisherProfile q = 0 ↔
      sourceZeroHorizontalCarrierAt K q = 0 := by
  rw [xiZeroSoninCriticalPhaseOddFisherProfile_eq_zero_iff,
    sourceZeroHorizontalCarrierAt_eq_zero_iff]

/-- **Same-carrier orientation identification.**  Vanishing of the signed
Sonin phase is exactly equality of the two coefficient-faithful deconvolved
reflection transports in their common prime carrier. -/
theorem xiZeroSoninCriticalPhaseOddFisherProfile_eq_zero_iff_orientationClass
    (q : XiZeroCopy) :
    xiZeroSoninCriticalPhaseOddFisherProfile q = 0 ↔
      fisherDeconvolvedOrientationClass
          (primeDepthBVWoldXiCenteredRate q.1) =
        fisherDeconvolvedOrientationClass
          (-primeDepthBVWoldXiCenteredRate q.1) := by
  rw [xiZeroSoninCriticalPhaseOddFisherProfile_eq_zero_iff,
    fisherDeconvolvedOrientationClass_eq_reflected_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Global vanishing law for the signed, multiplicity-resolved Sonin phase
profile.  This is stated separately so a future arithmetic producer has one
precise conclusion to discharge. -/
def XiZeroSoninCriticalPhaseOddFisherVanishes : Prop :=
  ∀ q : XiZeroCopy, xiZeroSoninCriticalPhaseOddFisherProfile q = 0

/-- Exact endpoint audit: global annihilation of the signed Sonin phase
profile is RH.  The preceding theorems construct the observable and its
cofinal physical carrier; they do not assume this vanishing law. -/
theorem xiZeroSoninCriticalPhaseOddFisherVanishes_iff_riemannHypothesis :
    XiZeroSoninCriticalPhaseOddFisherVanishes ↔ RiemannHypothesis := by
  constructor
  · intro h
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hzero
    let rhoSupport : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    let q : XiZeroCopy :=
      ⟨rhoSupport, ⟨0, xiSupportMultiplicity_pos rhoSupport⟩⟩
    exact (xiZeroSoninCriticalPhaseOddFisherProfile_eq_zero_iff q).1 (h q)
  · intro hRH q
    apply (xiZeroSoninCriticalPhaseOddFisherProfile_eq_zero_iff q).2
    exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH)
      (q.1 : ℂ) (xi_eq_zero_of_mem_divisor_support q.1)

end RHTower
