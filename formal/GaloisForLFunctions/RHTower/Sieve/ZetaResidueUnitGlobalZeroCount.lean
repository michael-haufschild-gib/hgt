import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorZeroDensityLinearExponent
import GaloisForLFunctions.RHTower.XiZeroDensity
import GaloisForLFunctions.RHTower.ModulusSlopeField
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- In the open critical strip, the entire residue unit and completed Xi have the same
finite analytic multiplicity. -/
theorem analyticOrderAt_zetaResidueUnit_eq_xi_of_mem_strip
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    analyticOrderAt zetaResidueUnit rho = analyticOrderAt RHTower.xi rho := by
  have hrho1 : rho ≠ 1 := by
    intro h
    rw [h] at hstrip
    norm_num at hstrip
  have hlinear : AnalyticAt ℂ (fun z : ℂ => z - 1) rho := by fun_prop
  have hzeta : AnalyticAt ℂ riemannZeta rho := analyticOn_riemannZeta rho hrho1
  calc
    analyticOrderAt zetaResidueUnit rho =
        analyticOrderAt (fun z : ℂ => (z - 1) * riemannZeta z) rho :=
      analyticOrderAt_congr (zetaResidueUnit_eventuallyEq hrho1)
    _ = analyticOrderAt riemannZeta rho := by
      change analyticOrderAt ((fun z : ℂ => z - 1) * riemannZeta) rho = _
      rw [analyticOrderAt_mul hlinear hzeta,
        hlinear.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hrho1), zero_add]
    _ = analyticOrderAt RHTower.xi rho :=
      (RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip).symm

/-- The total analytic multiplicity of residue-unit zeros in any positive-abscissa Route-T
rectangle is `O(T log T)`, uniformly in the left edge. -/
theorem exists_zetaResidueUnitClosedRectangleMultiplicity_le_global :
    ∃ C : ℝ, 0 < C ∧ ∀ {c T : ℝ}, 0 < c → c ≤ 1 → 1 ≤ T →
      (∑ w ∈ zetaResidueUnitClosedRectangleZeros
          ((c : ℂ) + (-T : ℝ) * I) ((4 : ℂ) + T * I),
        ((analyticOrderAt zetaResidueUnit w).toNat : ℝ)) ≤
          C * (T + 4) * Real.log (T + 5) := by
  obtain ⟨C, hC, hgrowth⟩ := RHTower.xi_zeroCount_growth
  refine ⟨C, hC, ?_⟩
  intro c T hc hc1 hT
  let Z : Finset ℂ := zetaResidueUnitClosedRectangleZeros
    ((c : ℂ) + (-T : ℝ) * I) ((4 : ℂ) + T * I)
  let D := MeromorphicOn.divisor RHTower.xi (closedBall (2 : ℂ) (T + 3))
  have hS := D.finiteSupport (isCompact_closedBall (2 : ℂ) (T + 3))
  have hdata : ∀ w ∈ Z,
      0 < w.re ∧ w.re < 1 ∧ |w.im| ≤ T ∧ RHTower.xi w = 0 := by
    intro w hw
    have hwmem := mem_zetaResidueUnitClosedRectangleZeros.mp hw
    have hwK := Complex.mem_reProdIm.mp hwmem.1
    have hwre : w.re ∈ Set.Icc c 4 := by
      simpa [Z, uIcc_of_le (by linarith : c ≤ (4 : ℝ))] using hwK.1
    have hwim : w.im ∈ Set.Icc (-T) T := by
      simpa [Z, uIcc_of_le (by linarith : -T ≤ T)] using hwK.2
    have hw1 : w ≠ 1 := by
      intro heq
      rw [heq, zetaResidueUnit_one] at hwmem
      norm_num at hwmem
    have hzeta : riemannZeta w = 0 := by
      by_contra hne
      exact ((zetaResidueUnit_ne_zero_iff hw1).2 hne) hwmem.2
    have hwre1 : w.re < 1 := by
      by_contra hcon
      exact (riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcon)) hzeta
    have hstrip : 0 < w.re ∧ w.re < 1 := ⟨hc.trans_le hwre.1, hwre1⟩
    exact ⟨hstrip.1, hstrip.2, (abs_le.2 hwim),
      (RHTower.xi_zero_iff_zeta_zero_of_mem_strip hstrip.1 hstrip.2).2 hzeta⟩
  have hball : ∀ w ∈ Z, w ∈ closedBall (2 : ℂ) (T + 3) := by
    intro w hw
    obtain ⟨hw0, hw1, hwim, _⟩ := hdata w hw
    rw [mem_closedBall, dist_eq_norm]
    have hre : |(w - 2).re| ≤ 2 := by
      rw [Complex.sub_re]
      norm_num
      rw [abs_le]
      constructor <;> linarith
    have him : |(w - 2).im| ≤ T := by
      simpa using hwim
    calc
      ‖w - 2‖ ≤ |(w - 2).re| + |(w - 2).im| := norm_le_abs_re_add_abs_im _
      _ ≤ 2 + T := add_le_add hre him
      _ ≤ T + 3 := by linarith
  have horder : ∀ w ∈ Z,
      analyticOrderAt zetaResidueUnit w = analyticOrderAt RHTower.xi w := by
    intro w hw
    exact analyticOrderAt_zetaResidueUnit_eq_xi_of_mem_strip
      ⟨(hdata w hw).1, (hdata w hw).2.1⟩
  have hsub : Z ⊆ hS.toFinset := by
    intro w hw
    have hDw : D w = ((analyticOrderAt RHTower.xi w).toNat : ℤ) := by
      exact RHTower.xi_divisor_closedBall_eq_order_toNat (hball w hw)
    rw [Set.Finite.mem_toFinset, Function.mem_support, hDw]
    exact_mod_cast RHTower.xi_order_toNat_ne_zero (hdata w hw).2.2.2
  have hsumD : (∑ᶠ w, D w) = ∑ w ∈ hS.toFinset, D w := by
    exact finsum_eq_sum_of_support_subset _ (by rw [Set.Finite.coe_toFinset])
  have hfinite :
      (∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℤ)) ≤
        ∑ w ∈ hS.toFinset, D w := by
    calc
      (∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℤ)) =
          ∑ w ∈ Z, D w := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [horder w hw]
        exact (RHTower.xi_divisor_closedBall_eq_order_toNat (hball w hw)).symm
      _ ≤ ∑ w ∈ hS.toFinset, D w := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro w hwS _
        have hwdom : w ∈ closedBall (2 : ℂ) (T + 3) :=
          D.supportWithinDomain (by rwa [Set.Finite.mem_toFinset] at hwS)
        rw [RHTower.xi_divisor_closedBall_eq_order_toNat hwdom]
        positivity
  have hfiniteReal :
      (∑ w ∈ Z, ((analyticOrderAt zetaResidueUnit w).toNat : ℝ)) ≤
        (((∑ᶠ w, D w : ℤ) : ℝ)) := by
    rw [hsumD]
    exact_mod_cast hfinite
  have hgrowth := hgrowth (T + 3) (by linarith)
  simpa only [Z, D, show (1 : ℝ) + (T + 3) = T + 4 by ring,
    show (2 : ℝ) + (T + 3) = T + 5 by ring] using hfiniteReal.trans hgrowth

end

end RHTower.Sieve
