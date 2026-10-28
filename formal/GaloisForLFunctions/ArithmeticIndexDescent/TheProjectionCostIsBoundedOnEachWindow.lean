import GaloisForLFunctions.ArithmeticIndexDescent.ArithmeticSectionProjection
import GaloisForLFunctions.ArithmeticIndexDescent.TheSourceKernelIsLocallyBounded
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw

/-!
# Uniform cost of section projection on a fixed arithmetic window

The complete source kernel bounds mixed energy by absolute mass. Cauchy–Schwarz
on the arithmetic support window and the source square-mass floor then bound
the energy removed by every finite section projection. The bound is independent
of dimension, profile derivatives and coefficient conditioning. It depends on
the window and on the fixed ambient test.
-/

open MeasureTheory RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics

/-- Every arithmetic section is supported in the actual logarithmic source window. -/
theorem arithmeticSectionTest_eq_zero_off_window {N : ℕ} {w : ℝ}
    (p : arithmeticSectionTests N w) {u : ℝ}
    (hu : u ∉ Set.Icc 0 (Real.log N + w)) : p.1.1 u = 0 := by
  obtain ⟨G, _, hs, he⟩ := p.2
  rw [he]
  apply Finset.sum_eq_zero
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hlog0 := Real.log_natCast_nonneg n
  have hlogN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
  apply hs n
  intro hm
  exact hu ⟨by linarith only [hm.1, hlog0], by linarith only [hm.2, hlogN]⟩

theorem arithmeticSectionTest_eq_zero_of_abs_gt {N : ℕ} {w : ℝ}
    (p : arithmeticSectionTests N w) {u : ℝ}
    (hu : Real.log N + w < |u|) : p.1.1 u = 0 := by
  apply arithmeticSectionTest_eq_zero_off_window p
  intro hm
  rw [abs_of_nonneg hm.1] at hu
  exact (not_lt_of_ge hm.2) hu

/-- Every projected test remains an actual arithmetic section. -/
theorem arithmeticSectionProjection_mem {ι : Type*} [Fintype ι]
    {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N)
    (f : ι → arithmeticSectionTests N w) (g : realTests) :
    arithmeticSectionProjection hN hw0 hw f g ∈ arithmeticSectionTests N w := by
  obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
  rw [hc]
  exact (arithmeticSectionTests N w).sum_mem fun i _ =>
    (arithmeticSectionTests N w).smul_mem (c i) (f i).2

/-- The fixed-window source bound pays every finite projection, including redundant families. -/
theorem exists_uniform_arithmeticSectionProjection_energy_bound
    {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N) (g : realTests) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ι : Type) [Fintype ι] (f : ι → arithmeticSectionTests N w),
      realWeilForm (arithmeticSectionProjection hN hw0 hw f g)
        (arithmeticSectionProjection hN hw0 hw f g) ≤ B := by
  let L := Real.log N + w
  have hL : 0 < L := add_pos_of_nonneg_of_pos (Real.log_natCast_nonneg N) hw0
  obtain ⟨C, hC, hbound⟩ := exists_sourceKernel_window_bound g L
  refine ⟨2 * L * C ^ 2, mul_nonneg (mul_nonneg (by norm_num) hL.le) (sq_nonneg C), ?_⟩
  intro ι _ f
  let p := arithmeticSectionProjection hN hw0 hw f g
  have hp : p ∈ arithmeticSectionTests N w := arithmeticSectionProjection_mem hN hw0 hw f g
  have hs (u : ℝ) (hu : L < |u|) : p.1 u = 0 :=
    arithmeticSectionTest_eq_zero_of_abs_gt ⟨p, hp⟩ hu
  have hfloor : (∫ u, p.1 u ^ 2) ≤ realWeilForm p p :=
    integral_sq_le_weilPair_arithmeticSection hN hw0 hw ⟨p, hp⟩
  have hE : 0 ≤ realWeilForm p p := arithmeticSectionProjection_energy_nonneg hN hw0 hw f g
  have hmass : 0 ≤ ∫ u, |p.1 u| := integral_nonneg fun u => abs_nonneg (p.1 u)
  have hpair : realWeilForm p g = realWeilForm p p := by
    obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
    have horth := arithmeticSectionProjection_orthogonal hN hw0 hw f c g
    rw [← hc, map_sub] at horth
    exact sub_eq_zero.mp horth
  have hEbound : realWeilForm p p ≤ C * ∫ u, |p.1 u| := by
    have h := hbound p hs
    rw [hpair, abs_of_nonneg hE] at h
    exact h
  have hsq : realWeilForm p p ^ 2 ≤ C ^ 2 * (∫ u, |p.1 u|) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hEbound)
      (add_nonneg (mul_nonneg hC hmass) hE)]
  have hCS : (∫ u, |p.1 u|) ^ 2 ≤ 2 * L * ∫ u, p.1 u ^ 2 := by
    have h := sq_integral_norm_le_of_abs_support (cx_contDiff p.2.1).continuous hL
      (fun u hu => by simp only [cx, hs u hu, Complex.ofReal_zero])
    simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
  have hbudget : realWeilForm p p ^ 2 ≤ (2 * L * C ^ 2) * realWeilForm p p := by
    calc
      _ ≤ C ^ 2 * (∫ u, |p.1 u|) ^ 2 := hsq
      _ ≤ C ^ 2 * (2 * L * ∫ u, p.1 u ^ 2) := mul_le_mul_of_nonneg_left hCS (sq_nonneg C)
      _ ≤ C ^ 2 * (2 * L * realWeilForm p p) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfloor (mul_nonneg (by norm_num) hL.le)) (sq_nonneg C)
      _ = _ := by ring
  by_cases hzero : realWeilForm p p = 0
  · rw [hzero]
    exact mul_nonneg (mul_nonneg (by norm_num) hL.le) (sq_nonneg C)
  · have hpos := lt_of_le_of_ne hE (Ne.symm hzero)
    by_contra h
    have hbad := mul_pos (sub_pos.mpr (lt_of_not_ge h)) hpos
    nlinarith only [hbudget, hbad]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_uniform_arithmeticSectionProjection_energy_bound
