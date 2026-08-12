import GaloisForLFunctions.RHTower.SoninCofinalReporterClockCommutatorSeam

/-!
# Signed complex-phase Sonin--Fisher splice

The real Fisher landing is positive and therefore erases reflection orientation.  This module
retains the unitary logarithmic phase before scalarization.  It first proves the complex critical
Euler limit along every fixed inward direction and then extracts the reflection-odd `+it/-it`
coordinate.  On the Xi strip that odd coordinate vanishes only at neutral horizontal grade.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- Complex critical ray with direction `1+u`. -/
def soninComplexCriticalPath (u : ℂ) (sigma : ℝ) : ℂ :=
  1 + (1 + u) * ((sigma - 1 : ℝ) : ℂ)

private theorem one_add_ne_zero_of_re_nonneg {u : ℂ} (hu : 0 ≤ u.re) :
    1 + u ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [add_re, one_re, zero_re] at hre
  linarith

theorem tendsto_soninComplexCriticalPath_punctured
    {u : ℂ} (hu : 0 ≤ u.re) :
    Tendsto (soninComplexCriticalPath u)
      (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 1 ({1} : Set ℂ)ᶜ) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hbase : Tendsto (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
      have hcont : Continuous (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ)) := by
        fun_prop
      exact (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    simpa [soninComplexCriticalPath] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hbase)
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
  have hpath : Tendsto (soninComplexCriticalPath u)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    have hbase : Tendsto (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
      have hcont : Continuous (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ)) := by
        fun_prop
      exact (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    simpa [soninComplexCriticalPath] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hbase)
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
  have hmain := (tendsto_const_nhds.mul hres).div hden hzetaTwo
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

end RHTower
