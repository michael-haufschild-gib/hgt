import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedFockRankQuantum
import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge
import GaloisForLFunctions.RHTower.XiHorizontalCollisionGaussHodgePrimeCurrent

/-!
# EWQ completed-Fock reflection census

This module welds the completed Euler--Wick Fock operator to the canonical horizontal-collision
census.  Each divisor point contributes the discrete rank quantum `0` on the critical line and
`2` off it.  Weighting strict-right packets by squared analytic multiplicity gives exactly the
canonical Xi reflection self-intersection charge in every finite strip window.

The equality is unconditional and coefficient-faithful: it uses actual Xi divisor support,
analytic orders, and the algebraic rank of the full completed-Fock color defect.  It supplies a
noncommutative operator realization of the indivisible two-unit HC quantum.
-/

open Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The discrete algebraic rank quantum of the reflected completed EWQ Fock color. -/
def eulerWickXiDivisorCompletedFockRankQuantum
    (rho : _root_.RHTower.XiDivisorSupport) : ℕ :=
  by
    classical
    exact if _root_.RHTower.HasRankLE
        (eulerWickXiDivisorCompletedFockRankDefect rho) 1 then 0 else 2

@[simp] theorem eulerWickXiDivisorCompletedFockRankQuantum_eq_zero_iff
    (rho : _root_.RHTower.XiDivisorSupport) :
    eulerWickXiDivisorCompletedFockRankQuantum rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  classical
  by_cases hline : (rho : ℂ).re = 1 / 2
  · have hrank :=
      (eulerWickXiDivisorCompletedFockRankDefect_hasRankLE_one_iff rho).2 hline
    constructor
    · intro _
      exact hline
    · intro _
      simp [eulerWickXiDivisorCompletedFockRankQuantum, hrank]
  · have hrank : ¬ _root_.RHTower.HasRankLE
        (eulerWickXiDivisorCompletedFockRankDefect rho) 1 := by
      intro hrank
      exact hline
        ((eulerWickXiDivisorCompletedFockRankDefect_hasRankLE_one_iff rho).1 hrank)
    constructor
    · intro hzero
      simp [eulerWickXiDivisorCompletedFockRankQuantum, hrank] at hzero
    · intro hre
      exact (hline hre).elim

@[simp] theorem eulerWickXiDivisorCompletedFockRankQuantum_eq_two_iff
    (rho : _root_.RHTower.XiDivisorSupport) :
    eulerWickXiDivisorCompletedFockRankQuantum rho = 2 ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  classical
  by_cases hline : (rho : ℂ).re = 1 / 2
  · have hrank :=
      (eulerWickXiDivisorCompletedFockRankDefect_hasRankLE_one_iff rho).2 hline
    constructor
    · intro htwo
      simp [eulerWickXiDivisorCompletedFockRankQuantum, hrank] at htwo
    · intro hoff
      exact (hoff hline).elim
  · have hrank : ¬ _root_.RHTower.HasRankLE
        (eulerWickXiDivisorCompletedFockRankDefect rho) 1 := by
      intro hrank
      exact hline
        ((eulerWickXiDivisorCompletedFockRankDefect_hasRankLE_one_iff rho).1 hrank)
    constructor
    · intro _
      exact hline
    · intro _
      simp [eulerWickXiDivisorCompletedFockRankQuantum, hrank]

/-- Multiplicity-squared census of EWQ Fock rank quanta in a strict-right strip window. -/
def eulerWickXiCompletedFockRankQuantumCensus (T : ℝ) : ℕ :=
  ∑ rho ∈ (_root_.RHTower.xiStripWindowDivisorSupportFinset T).filter
      (fun rho : _root_.RHTower.XiDivisorSupport => 1 / 2 < (rho : ℂ).re),
    eulerWickXiDivisorCompletedFockRankQuantum rho *
      ((analyticOrderAt _root_.RHTower.xi (rho : ℂ)).toNat) ^ 2

private theorem xiStripWindowDivisorSupport_rightSquare_sum_eq
    (T : ℝ) :
    (∑ rho ∈ (_root_.RHTower.xiStripWindowDivisorSupportFinset T).filter
        (fun rho : _root_.RHTower.XiDivisorSupport => 1 / 2 < (rho : ℂ).re),
      ((analyticOrderAt _root_.RHTower.xi (rho : ℂ)).toNat) ^ 2) =
      _root_.RHTower.xiStripWindowRightSquareOrder T := by
  classical
  rw [_root_.RHTower.xiStripWindowRightSquareOrder]
  refine Finset.sum_bij (fun rho _ => (rho : ℂ)) ?_ ?_ ?_ ?_
  · intro rho hrho
    rw [Finset.mem_filter] at hrho ⊢
    exact ⟨(_root_.RHTower.mem_xiStripWindowDivisorSupportFinset.mp hrho.1), hrho.2⟩
  · intro rho _ sigma _ hcoe
    exact Subtype.ext hcoe
  · intro z hz
    rw [Finset.mem_filter] at hz
    let rho : _root_.RHTower.XiDivisorSupport :=
      ⟨z, _root_.RHTower.mem_xi_divisor_support_of_eq_zero
        (((_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hz.1).2)⟩
    refine ⟨rho, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨_root_.RHTower.mem_xiStripWindowDivisorSupportFinset.mpr hz.1, hz.2⟩
  · intro rho _
    rfl

/-- The completed EWQ Fock rank census is exactly the canonical reflection collision charge. -/
theorem eulerWickXiCompletedFockRankQuantumCensus_eq_reflectionSelfIntersectionCharge
    (T : ℝ) :
    eulerWickXiCompletedFockRankQuantumCensus T =
      _root_.RHTower.xiReflectionSelfIntersectionCharge T := by
  classical
  rw [eulerWickXiCompletedFockRankQuantumCensus,
    _root_.RHTower.xiReflectionSelfIntersectionCharge]
  have hterm : ∀ rho ∈
      (_root_.RHTower.xiStripWindowDivisorSupportFinset T).filter
        (fun rho : _root_.RHTower.XiDivisorSupport => 1 / 2 < (rho : ℂ).re),
      eulerWickXiDivisorCompletedFockRankQuantum rho = 2 := by
    intro rho hrho
    rw [eulerWickXiDivisorCompletedFockRankQuantum_eq_two_iff]
    exact ne_of_gt (Finset.mem_filter.mp hrho).2
  calc
    (∑ rho ∈ (_root_.RHTower.xiStripWindowDivisorSupportFinset T).filter
        (fun rho : _root_.RHTower.XiDivisorSupport => 1 / 2 < (rho : ℂ).re),
      eulerWickXiDivisorCompletedFockRankQuantum rho *
        ((analyticOrderAt _root_.RHTower.xi (rho : ℂ)).toNat) ^ 2) =
        ∑ rho ∈ (_root_.RHTower.xiStripWindowDivisorSupportFinset T).filter
          (fun rho : _root_.RHTower.XiDivisorSupport => 1 / 2 < (rho : ℂ).re),
        2 * ((analyticOrderAt _root_.RHTower.xi (rho : ℂ)).toNat) ^ 2 := by
          apply Finset.sum_congr rfl
          intro rho hrho
          rw [hterm rho hrho]
    _ = 2 * (∑ rho ∈ (_root_.RHTower.xiStripWindowDivisorSupportFinset T).filter
          (fun rho : _root_.RHTower.XiDivisorSupport => 1 / 2 < (rho : ℂ).re),
        ((analyticOrderAt _root_.RHTower.xi (rho : ℂ)).toNat) ^ 2) := by
          rw [Finset.mul_sum]
    _ = 2 * _root_.RHTower.xiStripWindowRightSquareOrder T := by
          rw [xiStripWindowDivisorSupport_rightSquare_sum_eq]

end

end GaloisForLFunctions.RHTower
