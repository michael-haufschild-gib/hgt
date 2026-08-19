import GaloisForLFunctions.RHTower.BurnolCoPoissonConormalReflectionCover
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# Completed zero jets of literal Burnol co-Poisson windows

For every positive logarithmic subwindow, this file proves on the actual
Gamma-completed Sonine evaluation that the zero jets below the exact zeta
multiplicity vanish, while the leading jet does not.  The proof uses the
literal completed evaluation, equality with the co-Poisson formula on the
open strip, and locality of iterated derivatives.  Thus it does not assume a
parameter-differentiation theorem for an improper integral.

This is the source-side jet law required by Burnol's evaluator systems.  It
does not prove his aperture completeness/minimality or identify the closure
of all zero-jet evaluators with the full Hilbert-space complement.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The actual Gamma-completed Mellin evaluation of Burnol's logarithmic
co-Poisson subwindow `[exp (-L), 1]`. -/
def burnolCoPoissonExpWindowCompletedEvaluation (L : ℝ) (hL : 0 ≤ L) (w : ℂ) : ℂ :=
  soninMellinEvaluation w
    (((coPoissonSubWindowSonin (Real.exp_pos (-L))
      (Real.exp_le_one_iff.mpr (by linarith [hL])) :
        soninExtendedSpace (subWindowAperture (Real.exp (-L)) 1)) : evenSubspace) : SoninL2)

/-- On the open strip, the literal completed source evaluation is the Gamma
completion times the exact co-Poisson zeta germ. -/
theorem burnolCoPoissonExpWindowCompletedEvaluation_eq
    {L : ℝ} (hL : 0 < L) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    burnolCoPoissonExpWindowCompletedEvaluation L hL.le w =
      mellinCompletionFactor w * burnolCoPoissonExpWindowZetaMellinGerm L w := by
  simpa only [burnolCoPoissonExpWindowCompletedEvaluation] using
    soninMellinEvaluation_coPoissonExpWindowSonin hL hw0 hw1

/-- The archimedean completion is analytic throughout the open right
half-plane. -/
theorem analyticAt_mellinCompletionFactor_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ mellinCompletionFactor w := by
  change AnalyticAt ℂ
    (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) w
  apply AnalyticAt.mul
  · have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hdiff : Differentiable ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) := by
      exact Differentiable.const_cpow (differentiable_neg.div_const 2) (Or.inl hpi)
    exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff) w (Set.mem_univ _)
  · have hpos : 0 < (w / 2).re := by
      rw [div_re]
      norm_num
      linarith
    refine AnalyticAt.comp (g := Complex.Gamma) (f := fun z : ℂ => z / 2) (x := w) ?_ ?_
    · exact HTGeometry.analyticAt_Gamma_of_re_pos hpos
    · fun_prop

/-- Every derivative below the exact zeta multiplicity vanishes for the
uncompleted germ of the literal subwindow. -/
theorem iteratedDeriv_burnolCoPoissonExpWindowZetaMellinGerm_eq_zero_of_lt
    (L : ℝ) (rho : XiDivisorSupport) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) :
    iteratedDeriv j (burnolCoPoissonExpWindowZetaMellinGerm L) (rho : ℂ) = 0 := by
  have hne1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact (ne_of_lt (xi_divisor_support_re_mem_open_unit rho).2) hre
  have hzeta : ContDiffAt ℂ j riemannZeta (rho : ℂ) :=
    (analyticOn_riemannZeta (rho : ℂ) hne1).contDiffAt
  have hne0 : (rho : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact (ne_of_gt (xi_divisor_support_re_mem_open_unit rho).1) hre
  have hgauge : ContDiffAt ℂ j
      (fun w : ℂ => (Complex.exp ((L : ℂ) * w) - 1) / w) (rho : ℂ) := by
    apply ContDiffAt.div
    · fun_prop
    · fun_prop
    · exact hne0
  change iteratedDeriv j
      (riemannZeta * fun w : ℂ => (Complex.exp ((L : ℂ) * w) - 1) / w)
        (rho : ℂ) = 0
  rw [iteratedDeriv_mul hzeta hgauge]
  apply Finset.sum_eq_zero
  intro i hi
  have hile : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hilt : i < burnolCoPoissonXiConormalOrder rho := lt_of_le_of_lt hile hj
  rw [(riemannZeta_exact_jet_at_burnolCoPoissonXiConormalOrder rho).1 i hilt]
  simp

/-- Multiplication by the analytic nonzero Gamma completion preserves all
lower vanishing jets of a literal Burnol subwindow. -/
theorem iteratedDeriv_mellinCompletionFactor_mul_burnolCoPoissonExpWindowZetaMellinGerm_eq_zero_of_lt
    (L : ℝ) (rho : XiDivisorSupport) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) :
    iteratedDeriv j
      (mellinCompletionFactor * burnolCoPoissonExpWindowZetaMellinGerm L) (rho : ℂ) = 0 := by
  have hcomp : ContDiffAt ℂ j mellinCompletionFactor (rho : ℂ) :=
    (analyticAt_mellinCompletionFactor_of_re_pos
      (xi_divisor_support_re_mem_open_unit rho).1).contDiffAt
  have hne1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact (ne_of_lt (xi_divisor_support_re_mem_open_unit rho).2) hre
  have hne0 : (rho : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact (ne_of_gt (xi_divisor_support_re_mem_open_unit rho).1) hre
  have hgerm : ContDiffAt ℂ j (burnolCoPoissonExpWindowZetaMellinGerm L) (rho : ℂ) := by
    change ContDiffAt ℂ j
      (riemannZeta * fun w : ℂ => (Complex.exp ((L : ℂ) * w) - 1) / w) (rho : ℂ)
    apply ContDiffAt.mul
    · exact (analyticOn_riemannZeta (rho : ℂ) hne1).contDiffAt
    · apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · exact hne0
  rw [iteratedDeriv_mul hcomp hgerm]
  apply Finset.sum_eq_zero
  intro i hi
  have hjsub : j - i < burnolCoPoissonXiConormalOrder rho :=
    lt_of_le_of_lt (Nat.sub_le _ _) hj
  rw [iteratedDeriv_burnolCoPoissonExpWindowZetaMellinGerm_eq_zero_of_lt L rho hjsub]
  simp

/-- The leading completed jet of every positive logarithmic subwindow is
nonzero at each Xi divisor, so its zero order is exactly the zeta
multiplicity. -/
theorem iteratedDeriv_mellinCompletionFactor_mul_burnolCoPoissonExpWindowZetaMellinGerm_ne_zero
    (L : ℝ) (hL : 0 < L) (rho : XiDivisorSupport) :
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
      (mellinCompletionFactor * burnolCoPoissonExpWindowZetaMellinGerm L) (rho : ℂ) ≠ 0 := by
  let m := burnolCoPoissonXiConormalOrder rho
  have hcomp : ContDiffAt ℂ m mellinCompletionFactor (rho : ℂ) :=
    (analyticAt_mellinCompletionFactor_of_re_pos
      (xi_divisor_support_re_mem_open_unit rho).1).contDiffAt
  have hne1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact (ne_of_lt (xi_divisor_support_re_mem_open_unit rho).2) hre
  have hne0 : (rho : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact (ne_of_gt (xi_divisor_support_re_mem_open_unit rho).1) hre
  have hgerm : ContDiffAt ℂ m (burnolCoPoissonExpWindowZetaMellinGerm L) (rho : ℂ) := by
    change ContDiffAt ℂ m
      (riemannZeta * fun w : ℂ => (Complex.exp ((L : ℂ) * w) - 1) / w) (rho : ℂ)
    apply ContDiffAt.mul
    · exact (analyticOn_riemannZeta (rho : ℂ) hne1).contDiffAt
    · apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · exact hne0
  have hcomp_ne : mellinCompletionFactor (rho : ℂ) ≠ 0 :=
    mellinCompletionFactor_ne_zero (xi_divisor_support_re_mem_open_unit rho).1
  have hgerm_ne : iteratedDeriv m (burnolCoPoissonExpWindowZetaMellinGerm L) (rho : ℂ) ≠ 0 := by
    rw [iteratedDeriv_burnolCoPoissonExpWindowZetaMellinGerm]
    exact burnolCoPoissonSubWindowConormalCoefficient_ne_zero hL
      (xi_divisor_support_re_mem_open_unit rho).1 (burnolCoPoissonXiConormalLead_ne_zero rho)
  rw [iteratedDeriv_mul hcomp hgerm]
  rw [Finset.sum_eq_single 0]
  · simpa [m] using mul_ne_zero hcomp_ne hgerm_ne
  · intro i hi hi0
    have hi_le : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have him : m - i < m := by omega
    rw [iteratedDeriv_burnolCoPoissonExpWindowZetaMellinGerm_eq_zero_of_lt L rho him]
    simp
  · simp

/-- The actual completed co-Poisson source has all zero jets below the exact
zeta multiplicity. -/
theorem iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_eq_zero_of_lt
    (L : ℝ) (hL : 0 < L) (rho : XiDivisorSupport) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) :
    iteratedDeriv j (burnolCoPoissonExpWindowCompletedEvaluation L hL.le) (rho : ℂ) = 0 := by
  let U : Set ℂ := {w | 0 < w.re ∧ w.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hrhoU : (rho : ℂ) ∈ U := xi_divisor_support_re_mem_open_unit rho
  have hEq : Set.EqOn (burnolCoPoissonExpWindowCompletedEvaluation L hL.le)
      (mellinCompletionFactor * burnolCoPoissonExpWindowZetaMellinGerm L) U := by
    intro w hw
    exact burnolCoPoissonExpWindowCompletedEvaluation_eq hL hw.1 hw.2
  rw [hEq.iteratedDeriv_of_isOpen hUopen j hrhoU]
  exact iteratedDeriv_mellinCompletionFactor_mul_burnolCoPoissonExpWindowZetaMellinGerm_eq_zero_of_lt
    L rho hj

/-- The leading zero jet of the actual completed co-Poisson source is
nonzero.  Together with the preceding theorem, this realizes literal exact
multiplicity on every logarithmic source window. -/
theorem iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_ne_zero
    (L : ℝ) (hL : 0 < L) (rho : XiDivisorSupport) :
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
      (burnolCoPoissonExpWindowCompletedEvaluation L hL.le) (rho : ℂ) ≠ 0 := by
  let U : Set ℂ := {w | 0 < w.re ∧ w.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hrhoU : (rho : ℂ) ∈ U := xi_divisor_support_re_mem_open_unit rho
  have hEq : Set.EqOn (burnolCoPoissonExpWindowCompletedEvaluation L hL.le)
      (mellinCompletionFactor * burnolCoPoissonExpWindowZetaMellinGerm L) U := by
    intro w hw
    exact burnolCoPoissonExpWindowCompletedEvaluation_eq hL hw.1 hw.2
  rw [hEq.iteratedDeriv_of_isOpen hUopen (burnolCoPoissonXiConormalOrder rho) hrhoU]
  exact iteratedDeriv_mellinCompletionFactor_mul_burnolCoPoissonExpWindowZetaMellinGerm_ne_zero
    L hL rho

end
end RHTower
