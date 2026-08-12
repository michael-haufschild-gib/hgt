import GaloisForLFunctions.RHTower.CCMRestrictedWeilFriedrichsOperator

/-!
# Aperture monotonicity of the exact restricted CCM Weil form

The source form domains are nested with aperture.  This file proves the nesting on the literal
weighted Fourier domain, then identifies every source term under that inclusion.  The only new
prime indices at a larger aperture have logarithmic displacement beyond the smaller support
diameter, so their two translation pairings vanish exactly.  The variational characterization of
the canonical Friedrichs ground energy then gives its monotonicity.
-/

open MeasureTheory Set Filter
open scoped ENNReal InnerProduct BigOperators

noncomputable section

namespace RHTower

private theorem indicatorCutoff_central_eq_self_of_le
    {a b : ℝ} (hab : a ≤ b) (f : SoninL2)
    (hf : indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f = f) :
    indicatorCutoff (centralInterval b) (measurableSet_centralInterval b) f = f := by
  apply Lp.ext
  have hfix :
      (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f :
          ℝ → ℂ) =ᵐ[volume] f := by
    rw [hf]
  filter_upwards [
    indicatorCutoff_ae (centralInterval b) (measurableSet_centralInterval b) f,
    indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) f,
    hfix] with x hb ha hfixx
  rw [hb]
  by_cases hxb : x ∈ centralInterval b
  · rw [Set.indicator_of_mem hxb]
  · have hxa : x ∉ centralInterval a := by
      intro hxa
      apply hxb
      rw [centralInterval] at hxa ⊢
      constructor <;> linarith [hxa.1, hxa.2]
    rw [Set.indicator_of_notMem hxb]
    have hzero : f x = 0 := by
      rw [ha, Set.indicator_of_notMem hxa] at hfixx
      exact hfixx.symm
    rw [hzero]

private theorem ccmArchimedeanFormDomain_mem_of_le
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain a) :
    u.1 ∈ (ccmArchimedeanSupportDefect b).ker := by
  rw [LinearMap.mem_ker]
  change (1 - indicatorCutoff (centralInterval b.1)
    (measurableSet_centralInterval b.1))
      (ccmArchimedeanFourierToTime u.1) = 0
  rw [sub_apply, one_apply_eq_self, sub_eq_zero]
  have hfa : indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1)
        (ccmArchimedeanFourierToTime u.1) =
      ccmArchimedeanFourierToTime u.1 := by
    have hu := u.property
    rw [LinearMap.mem_ker] at hu
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1))
        (ccmArchimedeanFourierToTime u.1) = 0 at hu
    rw [sub_apply, one_apply_eq_self, sub_eq_zero] at hu
    exact hu.symm
  exact (indicatorCutoff_central_eq_self_of_le hab _ hfa).symm

/-- Every smaller-aperture form vector has a larger-aperture representative with identical
weighted Fourier data. -/
theorem exists_ccmArchimedeanFormDomain_extension
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain a) :
    ∃ v : CCMArchimedeanFormDomain b, v.1 = u.1 :=
  ⟨⟨u.1, ccmArchimedeanFormDomain_mem_of_le hab u⟩, rfl⟩

end RHTower
