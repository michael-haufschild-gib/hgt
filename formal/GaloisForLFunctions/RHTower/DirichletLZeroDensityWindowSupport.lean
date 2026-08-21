/-
# Finite multiplicity support for centered Dirichlet-L zero windows

The zero-density counts are divisor `finsum`s.  A well-spaced representative
argument needs finite zero data instead.  This module extracts the finite
support of the analytic completed-Dirichlet-L divisor in every centered
vertical window, proves every support point lies in that window with positive
multiplicity, and rewrites the literal zero count as its exact finite
multiplicity sum.

No RH, GRH, zero enumeration hypothesis, local density estimate, or
zero-detection premise is used.
-/

import GaloisForLFunctions.RHTower.DirichletLZeroDensityVerticalWindow

open Complex Metric

noncomputable section

namespace RHTower

/-- The zero divisor of a completed nonprincipal Dirichlet L-function has
finite support inside every centered vertical window. -/
theorem completedLFunction_zeroDensityVerticalWindow_divisor_support_finite
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
      (cglZeroDensityVerticalWindow σ τ H)).support.Finite := by
  let f := DirichletCharacter.completedLFunction χ.1
  let V := cglZeroDensityVerticalWindow σ τ H
  let U := completedLFunctionZeroDensityBox σ (|τ| + H)
  let D := closedBall (2 : ℂ) (4 + |σ| + |(|τ| + (H : ℝ))|)
  have hVU : V ⊆ U := cglZeroDensityVerticalWindow_subset_zeroDensityBox σ τ H
  have hUD : U ⊆ D := by
    exact completedLFunction_zeroDensityBox_subset_disc σ (|τ| + H)
  have hVD : V ⊆ D := fun z hz => hUD (hVU hz)
  have hf : AnalyticOnNhd ℂ f Set.univ := completedLFunction_analyticOnNhd n χ
  exact (hf.mono (Set.subset_univ D)).meromorphicOn.divisor_support_finite_of_subset
    (isCompact_closedBall ..) hVD

/-- The finite set of distinct divisor points in a centered zero window. -/
noncomputable def cglZeroDensityVerticalWindowZeroSupport
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) : Finset ℂ :=
  (completedLFunction_zeroDensityVerticalWindow_divisor_support_finite n χ σ τ H).toFinset

/-- The signed divisor multiplicity of a completed Dirichlet-L zero in a
centered vertical window.  Analyticity makes it nonnegative; support points
have strictly positive multiplicity. -/
def cglZeroDensityVerticalWindowMultiplicity
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) (z : ℂ) : ℤ :=
  MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
    (cglZeroDensityVerticalWindow σ τ H) z

/-- Support membership is exactly nonzero divisor multiplicity. -/
theorem mem_cglZeroDensityVerticalWindowZeroSupport_iff
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) (z : ℂ) :
    z ∈ cglZeroDensityVerticalWindowZeroSupport n χ σ τ H ↔
      cglZeroDensityVerticalWindowMultiplicity n χ σ τ H z ≠ 0 := by
  unfold cglZeroDensityVerticalWindowZeroSupport
    cglZeroDensityVerticalWindowMultiplicity
  simp only [Set.Finite.mem_toFinset, Function.mem_support]

/-- Every distinct divisor point selected by the finite support lies in the
corresponding centered vertical zero window. -/
theorem cglZeroDensityVerticalWindowZeroSupport_subset_window
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    ↑(cglZeroDensityVerticalWindowZeroSupport n χ σ τ H) ⊆
      cglZeroDensityVerticalWindow σ τ H := by
  intro z hz
  have hne := (mem_cglZeroDensityVerticalWindowZeroSupport_iff n χ σ τ H z).mp hz
  by_contra hzV
  apply hne
  unfold cglZeroDensityVerticalWindowMultiplicity
  rw [MeromorphicOn.divisor_def, if_neg]
  intro h
  exact hzV h.2

/-- A distinct completed-Dirichlet-L zero in a centered vertical window,
certified by the finite divisor support. -/
abbrev CGLZeroDensityVerticalWindowZeroSupportPoint
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :=
  ↑(cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)

/-- Every certified centered-window support point is an actual zero of the
completed Dirichlet L-function.  This rules out spurious divisor points by
using analyticity on the connected complex plane and nonvanishing at `2`. -/
theorem cglZeroDensityVerticalWindowZeroSupportPoint_isZero
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (z : CGLZeroDensityVerticalWindowZeroSupportPoint n χ σ τ H) :
    DirichletCharacter.completedLFunction χ.1 z.1 = 0 := by
  apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
  intro horder
  change (analyticOrderAt (DirichletCharacter.completedLFunction χ.1) z.1).toNat = 0 at horder
  have hAtTwo : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ.1) (2 : ℂ) :=
    completedLFunction_analyticOnNhd n χ 2 (by simp)
  have horderTwo : analyticOrderAt (DirichletCharacter.completedLFunction χ.1) (2 : ℂ) = 0 :=
    hAtTwo.analyticOrderAt_eq_zero.mpr (completedLFunction_two_ne_zero n χ)
  have hfinite : analyticOrderAt (DirichletCharacter.completedLFunction χ.1) z.1 ≠ ⊤ :=
    AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
      (completedLFunction_analyticOnNhd n χ) isPreconnected_univ (by simp) (by simp)
      (by rw [horderTwo]; exact ENat.zero_ne_top)
  have horder' : analyticOrderAt (DirichletCharacter.completedLFunction χ.1) z = 0 := by
    rcases ENat.toNat_eq_zero.mp horder with hzero | htop
    · exact hzero
    · exact (hfinite htop).elim
  have hzV := cglZeroDensityVerticalWindowZeroSupport_subset_window n χ σ τ H z.2
  have hne := (mem_cglZeroDensityVerticalWindowZeroSupport_iff n χ σ τ H z.1).mp z.2
  apply hne
  unfold cglZeroDensityVerticalWindowMultiplicity
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    ((completedLFunction_analyticOnNhd n χ).mono (Set.subset_univ _)) hzV]
  simp [horder']

/-- Every support point has strictly positive divisor multiplicity. -/
theorem cglZeroDensityVerticalWindowMultiplicity_pos
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (z : ℂ) (hz : z ∈ cglZeroDensityVerticalWindowZeroSupport n χ σ τ H) :
    0 < cglZeroDensityVerticalWindowMultiplicity n χ σ τ H z := by
  have hnonneg : 0 ≤ cglZeroDensityVerticalWindowMultiplicity n χ σ τ H z := by
    unfold cglZeroDensityVerticalWindowMultiplicity
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      ((completedLFunction_analyticOnNhd n χ).mono (Set.subset_univ _)) z
  exact lt_of_le_of_ne hnonneg (Ne.symm
    ((mem_cglZeroDensityVerticalWindowZeroSupport_iff n χ σ τ H z).mp hz))

/-- The literal centered-window zero count is exactly the finite sum of its
positive support multiplicities. -/
theorem completedLFunction_zeroDensityVerticalWindowCount_eq_sum_multiplicity
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H =
      ∑ z ∈ cglZeroDensityVerticalWindowZeroSupport n χ σ τ H,
        (cglZeroDensityVerticalWindowMultiplicity n χ σ τ H z : ℝ) := by
  unfold completedLFunctionZeroDensityVerticalWindowCount
  rw [finsum_eq_sum _
    (completedLFunction_zeroDensityVerticalWindow_divisor_support_finite n χ σ τ H)]
  simp only [cglZeroDensityVerticalWindowZeroSupport,
    cglZeroDensityVerticalWindowMultiplicity, Int.cast_sum]

end RHTower
