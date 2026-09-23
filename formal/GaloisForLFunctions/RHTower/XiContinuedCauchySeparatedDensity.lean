import GaloisForLFunctions.RHTower.XiWeilCauchyLpContinuity
import GaloisForLFunctions.RHTower.XiHurwitzOrientationCauchyClosure

/-!
# Self-separated density in the continued Xi Cauchy source core

Every continued-source Cauchy generator is an `ell^(2 : ℕ)` limit of continued-source generators whose
pole is not fixed by conjugation.  Thus the real-pole collision in the divided-difference source
formula is removable at the level of Hilbert closure: move a real pole vertically inside the
centered strip, use local Xi-zero isolation to retain regularity, and invoke norm continuity of the
Cauchy evaluation vector.
-/

open Complex Metric Function Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- A regular centered-strip point automatically lies in the full two-sided continued
prime--Gamma Cauchy domain. -/
theorem ccmContinuedCauchyDomain_of_regular_mem_centeredStrip
    {z : ℂ} (hzlo : -(1 / 2 : ℝ) < z.im) (hzhi : z.im < 1 / 2)
    (hz : XiC z ≠ 0) :
    CCMContinuedCauchyDomain z := by
  have hs0 : 0 < (1 / 2 + z * I).re := by
    simp [mul_re]
    linarith
  have hs1re : (1 / 2 + z * I).re < 1 := by
    simp [mul_re]
    linarith
  have ht0 : 0 < (1 / 2 + (starRingEnd ℂ) z * I).re := by
    simp [mul_re]
    linarith
  have ht1re : (1 / 2 + (starRingEnd ℂ) z * I).re < 1 := by
    simp [mul_re]
    linarith
  have htz : XiC ((starRingEnd ℂ) z) ≠ 0 := by
    rw [XiC_conj]
    exact (map_ne_zero (starRingEnd ℂ)).2 hz
  refine ⟨hs0, ?_, ?_, ht0, ?_, ?_⟩
  · intro h
    rw [h] at hs1re
    norm_num at hs1re
  · intro hzero
    apply hz
    exact (xi_zero_iff_zeta_zero_of_mem_strip hs0 hs1re).mpr hzero
  · intro h
    rw [h] at ht1re
    norm_num at ht1re
  · intro hzero
    apply htz
    exact (xi_zero_iff_zeta_zero_of_mem_strip ht0 ht1re).mpr hzero

/-- Every continued-source Cauchy generator is an `ell²` limit of continued-source generators
whose pole is not fixed by conjugation. -/
theorem exists_selfSeparatedContinuedCauchyLp_tendsto
    (z : XiContinuedCauchyPoint) :
    ∃ w : ℕ → XiContinuedCauchyPoint,
      (∀ n, (w n : ℂ) ≠ (starRingEnd ℂ) (w n : ℂ)) ∧
      Tendsto (fun n ↦ (w n : ℂ)) atTop (nhds (z : ℂ)) ∧
      Tendsto (fun n ↦ xiWeilContinuedCauchyLp (w n)) atTop
        (nhds (xiWeilContinuedCauchyLp z)) := by
  by_cases hzIm : (z : ℂ).im = 0
  · obtain ⟨delta, hdelta, hgap⟩ := exists_xiSpectralPoint_gap (z : ℂ)
    let c : ℝ := min (delta / 2) (1 / 4)
    have hc : 0 < c := lt_min (half_pos hdelta) (by norm_num)
    have hcdelta : c ≤ delta / 2 := min_le_left _ _
    have hcquarter : c ≤ 1 / 4 := min_le_right _ _
    let r : ℕ → ℝ := fun n ↦ c / (n + 1 : ℕ)
    have hrpos : ∀ n, 0 < r n := fun n ↦ div_pos hc (by positivity)
    have hrc : ∀ n, r n ≤ c := by
      intro n
      have hden : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
      exact div_le_self hc.le hden
    let wval : ℕ → ℂ := fun n ↦ (z : ℂ) + I * (r n : ℂ)
    have hwval_im : ∀ n, (wval n).im = r n := by
      intro n
      simp [wval, hzIm]
    have hwval_ne : ∀ n, wval n ≠ (z : ℂ) := by
      intro n h
      have him := congrArg Complex.im h
      rw [hwval_im n, hzIm] at him
      exact (hrpos n).ne' him
    have hwval_norm : ∀ n, ‖wval n - (z : ℂ)‖ = r n := by
      intro n
      simp [wval, Complex.norm_real, abs_of_pos (hrpos n)]
    have hwregular : ∀ n, XiC (wval n) ≠ 0 := by
      intro n hzero
      obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (wval n)).mp hzero
      have hqne : xiSpectralPoint q ≠ (z : ℂ) := hq.trans_ne (hwval_ne n)
      have hqgap := hgap q hqne
      rw [hq, hwval_norm n] at hqgap
      linarith [hrc n, hcdelta]
    have hwdomain : ∀ n, CCMContinuedCauchyDomain (wval n) := by
      intro n
      apply ccmContinuedCauchyDomain_of_regular_mem_centeredStrip
      · rw [hwval_im n]
        linarith [hrpos n]
      · rw [hwval_im n]
        linarith [hrc n, hcquarter]
      · exact hwregular n
    let w : ℕ → XiContinuedCauchyPoint := fun n ↦
      ⟨⟨wval n, hwregular n⟩, hwdomain n⟩
    have hrtend : Tendsto r atTop (nhds 0) := by
      exact (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat 1)
    have hwtend : Tendsto (fun n ↦ (w n : ℂ)) atTop (nhds (z : ℂ)) := by
      change Tendsto wval atTop (nhds (z : ℂ))
      simpa [wval] using tendsto_const_nhds.add
        (tendsto_const_nhds.mul (Complex.ofRealCLM.continuous.tendsto 0 |>.comp hrtend))
    refine ⟨w, ?_, hwtend, ?_⟩
    · intro n hconj
      have him : (w n : ℂ).im = 0 := Complex.conj_eq_iff_im.mp hconj.symm
      change (wval n).im = 0 at him
      rw [hwval_im n] at him
      exact (hrpos n).ne' him
    · exact tendsto_xiWeilCauchyLp hwtend
  · let w : ℕ → XiContinuedCauchyPoint := fun _ ↦ z
    refine ⟨w, ?_, tendsto_const_nhds, ?_⟩
    · intro n hconj
      apply hzIm
      exact Complex.conj_eq_iff_im.mp hconj.symm
    · exact tendsto_const_nhds

/-- Continued-source poles with the conjugation diagonal removed. -/
abbrev XiSelfSeparatedContinuedCauchyPoint :=
  {z : XiContinuedCauchyPoint //
    (z : ℂ) ≠ (starRingEnd ℂ) (z : ℂ)}

def xiWeilSelfSeparatedContinuedCauchyLp
    (z : XiSelfSeparatedContinuedCauchyPoint) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilContinuedCauchyLp z.1

def xiWeilSelfSeparatedContinuedCauchyAlgebraicSubspace :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Submodule.span ℂ (Set.range xiWeilSelfSeparatedContinuedCauchyLp)

theorem xiWeilContinuedCauchyLp_mem_selfSeparatedClosure
    (z : XiContinuedCauchyPoint) :
    xiWeilContinuedCauchyLp z ∈
      xiWeilSelfSeparatedContinuedCauchyAlgebraicSubspace.topologicalClosure := by
  obtain ⟨w, hwsep, _hwpoint, hwlim⟩ :=
    exists_selfSeparatedContinuedCauchyLp_tendsto z
  let ws : ℕ → XiSelfSeparatedContinuedCauchyPoint := fun n ↦
    ⟨w n, hwsep n⟩
  apply (Submodule.isClosed_topologicalClosure
    xiWeilSelfSeparatedContinuedCauchyAlgebraicSubspace).mem_of_tendsto hwlim
  exact Eventually.of_forall fun n ↦
    xiWeilSelfSeparatedContinuedCauchyAlgebraicSubspace.le_topologicalClosure
      (Submodule.subset_span ⟨ws n, rfl⟩)

/-- Removing the conjugation diagonal does not change the continued Cauchy Hilbert closure. -/
theorem selfSeparatedContinuedCauchy_topologicalClosure_eq :
    xiWeilSelfSeparatedContinuedCauchyAlgebraicSubspace.topologicalClosure =
      xiWeilContinuedCauchyHilbertSubspace := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨z, rfl⟩
      exact xiWeilContinuedCauchyAlgebraicSubspace.le_topologicalClosure
        (Submodule.subset_span ⟨z.1, rfl⟩)
    · exact Submodule.isClosed_topologicalClosure _
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨z, rfl⟩
      exact xiWeilContinuedCauchyLp_mem_selfSeparatedClosure z
    · exact Submodule.isClosed_topologicalClosure _

/-- The canonical Hurwitz orientation vector is already captured after deleting every real
Cauchy pole from the continued source generating set. -/
theorem xiHurwitzOrientationVector_mem_selfSeparatedContinuedCauchyClosure :
    xiHurwitzOrientationVector ∈
      xiWeilSelfSeparatedContinuedCauchyAlgebraicSubspace.topologicalClosure := by
  rw [selfSeparatedContinuedCauchy_topologicalClosure_eq]
  exact xiHurwitzOrientationVector_mem_continuedCauchyHilbertSubspace

end

end RHTower
