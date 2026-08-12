import GaloisForLFunctions.RHTower.SoninCofinalReporterClockCommutatorSeam

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
  have htwoFlux : Tendsto (fun sigma : ℝ =>
      infinitePrimeFlux
        (2 * soninComplexCriticalPath u sigma)) l
      (nhds (infinitePrimeFlux (2 : ℂ))) := by
    have hcont := (GaloisForLFunctions.differentiableAt_infinitePrimeFlux_two_mul
      (s := (1 : ℂ)) (by norm_num)).continuousAt.tendsto
    have hcomp := hcont.comp hpath
    change Tendsto (fun sigma : ℝ => infinitePrimeFlux
      (2 * soninComplexCriticalPath u sigma)) l
      (nhds (infinitePrimeFlux (2 : ℂ))) at hcomp
    exact hcomp
  have hcorrection : Tendsto (fun sigma : ℝ =>
      (soninComplexCriticalPath u sigma - 1) *
        (2 * infinitePrimeFlux
          (2 * soninComplexCriticalPath u sigma))) l (nhds 0) := by
    have htwo := tendsto_const_nhds.mul htwoFlux
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
  change (((sigma - 1 : ℝ) : ℂ) *
      GaloisForLFunctions.squarefreePartition
        (1 + (1 + u) * ((sigma - 1 : ℝ) : ℂ))) /
      (((sigma - 1 : ℝ) : ℂ) *
        GaloisForLFunctions.squarefreePartition
          (1 + (1 + (0 : ℂ)) * ((sigma - 1 : ℝ) : ℂ))) =
    GaloisForLFunctions.squarefreePartition
        (1 + (1 + u) * ((sigma - 1 : ℝ) : ℂ)) /
      GaloisForLFunctions.squarefreePartition (sigma : ℂ)
  rw [hzeroPath]
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

end RHTower
