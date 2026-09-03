import GaloisForLFunctions.RHTower.XiPoleClearedFirstTraceRootReduction
import GaloisForLFunctions.RHTower.PoleFactorCayleySqrtApproximation
import GaloisForLFunctions.Bottcher.FigureEight

/-!
# Cayley-seam form of the first arithmetic half-divisor problem

The pole-factor coordinate

```text
w = (s - 2) / s
```

maps the strict half-plane `Re s > 1/2` biholomorphically onto the disk `|w + 1| < 2`.
The Euler chamber `Re s > 1` is exactly the unit disk `|w| < 1`.  Hence the missing arithmetic
square root is an analytic continuation from the unit disk across its internal circle into the
larger tangent disk.

This module records that geometry and proves the exact square-root equivalence.  It does not assume
or produce the continuation.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry
open HedenmalmThetaSource

noncomputable section

/-- Cayley image of `rightHalf`. -/
def poleFactorCayleyRightDomain : Set ℂ := ball (-1 : ℂ) 2

/-- Inverse of the pole-factor Cayley coordinate. -/
def poleFactorCayleyInv (w : ℂ) : ℂ := 2 / (1 - w)

private theorem re_cayleyInv_pos {u : ℂ} (hu : ‖u‖ < 1) :
    0 < ((1 + u) / (1 - u)).re := by
  have hne : u ≠ 1 := by
    intro h
    rw [h, norm_one] at hu
    exact lt_irrefl 1 hu
  have hd : (1 : ℂ) - u ≠ 0 := fun h => hne (by linear_combination -h)
  have hden : (0 : ℝ) < Complex.normSq (1 - u) := Complex.normSq_pos.mpr hd
  have hsq : Complex.normSq u < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg u]
  rw [Complex.div_re]
  have hnum : (1 + u).re * (1 - u).re / Complex.normSq (1 - u)
      + (1 + u).im * (1 - u).im / Complex.normSq (1 - u)
      = (1 - Complex.normSq u) / Complex.normSq (1 - u) := by
    rw [← add_div]
    congr 1
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [hnum]
  exact div_pos (by linarith) hden

private theorem re_cayleyInv_nonneg {u : ℂ} (hu : ‖u‖ ≤ 1) (hu1 : u ≠ 1) :
    0 ≤ ((1 + u) / (1 - u)).re := by
  have hd : (1 : ℂ) - u ≠ 0 := fun h => hu1 (by linear_combination -h)
  have hden : (0 : ℝ) < Complex.normSq (1 - u) := Complex.normSq_pos.mpr hd
  have hsq : Complex.normSq u ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg u]
  rw [Complex.div_re]
  have hnum : (1 + u).re * (1 - u).re / Complex.normSq (1 - u)
      + (1 + u).im * (1 - u).im / Complex.normSq (1 - u)
      = (1 - Complex.normSq u) / Complex.normSq (1 - u) := by
    rw [← add_div]
    congr 1
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [hnum]
  exact div_nonneg (by linarith) hden.le

theorem poleFactorCayley_eq_affine_cayleyRight {s : ℂ} (hs : s ∈ rightHalf) :
    poleFactorCayley s = 2 * cayleyRight (2 * s - 1) - 1 := by
  have hsre : 1 / 2 < s.re := mem_rightHalf.mp hs
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hsre
  simp only [poleFactorCayley, cayleyRight]
  field_simp [hs0]
  ring

/-- The pole-factor Cayley coordinate maps `rightHalf` into its exact larger disk. -/
theorem poleFactorCayley_mem_rightDomain {s : ℂ} (hs : s ∈ rightHalf) :
    poleFactorCayley s ∈ poleFactorCayleyRightDomain := by
  have hsre : 1 / 2 < s.re := mem_rightHalf.mp hs
  have hzre : 0 < (2 * s - 1).re := by
    norm_num [Complex.mul_re]
    linarith
  have hv := norm_cayleyRight_lt_one hzre
  rw [poleFactorCayleyRightDomain, mem_ball, Complex.dist_eq]
  rw [poleFactorCayley_eq_affine_cayleyRight hs]
  have hid : 2 * cayleyRight (2 * s - 1) - 1 - (-1 : ℂ) =
      2 * cayleyRight (2 * s - 1) := by ring
  rw [hid, norm_mul]
  norm_num at *
  linarith

/-- Every point of the larger Cayley disk has a nonzero inverse denominator. -/
theorem one_sub_ne_zero_of_mem_poleFactorCayleyRightDomain
    {w : ℂ} (hw : w ∈ poleFactorCayleyRightDomain) :
    (1 : ℂ) - w ≠ 0 := by
  intro h
  have hw1 : w = 1 := by linear_combination -h
  subst w
  norm_num [poleFactorCayleyRightDomain, mem_ball, Complex.dist_eq] at hw

/-- The inverse Cayley coordinate maps the larger disk back into `rightHalf`. -/
theorem poleFactorCayleyInv_mem_rightHalf
    {w : ℂ} (hw : w ∈ poleFactorCayleyRightDomain) :
    poleFactorCayleyInv w ∈ rightHalf := by
  let u : ℂ := (w + 1) / 2
  have hdist : ‖w + 1‖ < 2 := by
    rw [poleFactorCayleyRightDomain, mem_ball, Complex.dist_eq] at hw
    simpa [sub_eq_add_neg, add_comm] using hw
  have hu : ‖u‖ < 1 := by
    dsimp [u]
    rw [norm_div]
    norm_num at *
    linarith
  have huz := re_cayleyInv_pos hu
  have heq : poleFactorCayleyInv w = ((1 + u) / (1 - u) + 1) / 2 := by
    have hden : (1 : ℂ) - w ≠ 0 :=
      one_sub_ne_zero_of_mem_poleFactorCayleyRightDomain hw
    have hu1 : u ≠ 1 := by
      intro h
      rw [h, norm_one] at hu
      exact lt_irrefl 1 hu
    have h1u : (1 : ℂ) - u ≠ 0 := fun h => hu1 (by linear_combination -h)
    dsimp only [poleFactorCayleyInv]
    field_simp [hden, h1u]
    dsimp [u]
    ring
  rw [mem_rightHalf, heq]
  have div_two_re (z : ℂ) : (z / 2).re = z.re / 2 := by
    norm_num [Complex.div_re]
  rw [div_two_re, Complex.add_re, Complex.one_re]
  linarith

@[simp] theorem poleFactorCayleyInv_poleFactorCayley
    {s : ℂ} (hs : s ∈ rightHalf) :
    poleFactorCayleyInv (poleFactorCayley s) = s := by
  have hsre : 1 / 2 < s.re := mem_rightHalf.mp hs
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hsre
  simp only [poleFactorCayleyInv, poleFactorCayley, cayleyRight]
  field_simp [hs0]
  ring

@[simp] theorem poleFactorCayley_poleFactorCayleyInv
    {w : ℂ} (hw : w ∈ poleFactorCayleyRightDomain) :
    poleFactorCayley (poleFactorCayleyInv w) = w := by
  have hden : (1 : ℂ) - w ≠ 0 :=
    one_sub_ne_zero_of_mem_poleFactorCayleyRightDomain hw
  simp only [poleFactorCayley, poleFactorCayleyInv, cayleyRight]
  field_simp [hden]
  ring

theorem analyticOnNhd_poleFactorCayleyInv_rightDomain :
    AnalyticOnNhd ℂ poleFactorCayleyInv poleFactorCayleyRightDomain := by
  intro w hw
  exact analyticAt_const.div (analyticAt_const.sub analyticAt_id)
    (one_sub_ne_zero_of_mem_poleFactorCayleyRightDomain hw)

/-- The Euler chamber is the unit subdisk in the same coordinate. -/
theorem poleFactorCayleyInv_mem_farHalf {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    poleFactorCayleyInv w ∈ farHalf := by
  have hnorm : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
  have hz := re_cayleyInv_pos hnorm
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have hw1 : w = 1 := by linear_combination -h
    subst w
    norm_num at hnorm
  have heq : poleFactorCayleyInv w = 1 + (1 + w) / (1 - w) := by
    dsimp [poleFactorCayleyInv]
    field_simp [hne]
    ring
  rw [mem_farHalf, heq]
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem poleFactorCayley_mem_unitBall {s : ℂ} (hs : s ∈ farHalf) :
    poleFactorCayley s ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball, dist_zero_right]
  exact norm_poleFactorCayley_lt_one (mem_farHalf.mp hs)

/-- On `rightHalf`, membership in the Euler chamber is exactly membership in the unit subdisk. -/
theorem poleFactorCayley_mem_unitBall_iff {s : ℂ} (hs : s ∈ rightHalf) :
    poleFactorCayley s ∈ ball (0 : ℂ) 1 ↔ s ∈ farHalf := by
  constructor
  · intro hw
    have hinv := poleFactorCayleyInv_mem_farHalf hw
    simpa [poleFactorCayleyInv_poleFactorCayley hs] using hinv
  · exact poleFactorCayley_mem_unitBall

/-- The closed unit disk maps to the classical zero-free half-plane, away from the tangent point
`w = 1`, which is already excluded by the larger open disk. -/
theorem one_le_re_poleFactorCayleyInv_of_norm_le_one
    {w : ℂ} (hw : w ∈ poleFactorCayleyRightDomain) (hnorm : ‖w‖ ≤ 1) :
    1 ≤ (poleFactorCayleyInv w).re := by
  have hw1 : w ≠ 1 := by
    intro h
    subst w
    norm_num [poleFactorCayleyRightDomain, mem_ball, Complex.dist_eq] at hw
  have hz := re_cayleyInv_nonneg hnorm hw1
  have hden : (1 : ℂ) - w ≠ 0 :=
    one_sub_ne_zero_of_mem_poleFactorCayleyRightDomain hw
  have heq : poleFactorCayleyInv w = 1 + (1 + w) / (1 - w) := by
    dsimp [poleFactorCayleyInv]
    field_simp [hden]
    ring
  rw [heq, Complex.add_re, Complex.one_re]
  linarith

/-- Pole-cleared valuation-one field in the larger Cayley disk. -/
def poleClearedFirstTraceCayleyField (w : ℂ) : ℂ :=
  poleClearedFirstTraceExponentialContinuation (poleFactorCayleyInv w)

/-- Fixed arithmetic Euler half-germ transported to the Cayley unit disk. -/
def poleClearedPrimeZetaHalfEulerCayleyGerm (w : ℂ) : ℂ :=
  poleClearedPrimeZetaHalfEulerGerm (poleFactorCayleyInv w)

theorem analyticOnNhd_poleClearedFirstTraceCayleyField :
    AnalyticOnNhd ℂ poleClearedFirstTraceCayleyField poleFactorCayleyRightDomain := by
  intro w hw
  exact (analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf
    (poleFactorCayleyInv w) (poleFactorCayleyInv_mem_rightHalf hw)).comp
      (analyticOnNhd_poleFactorCayleyInv_rightDomain w hw)

theorem analyticOnNhd_poleClearedPrimeZetaHalfEulerCayleyGerm_unitBall :
    AnalyticOnNhd ℂ poleClearedPrimeZetaHalfEulerCayleyGerm (ball (0 : ℂ) 1) := by
  intro w hw
  have hnorm : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have hw1 : w = 1 := by linear_combination -h
    subst w
    norm_num at hnorm
  have hinv : AnalyticAt ℂ poleFactorCayleyInv w :=
    analyticAt_const.div (analyticAt_const.sub analyticAt_id) hne
  exact (analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf
    (poleFactorCayleyInv w) (poleFactorCayleyInv_mem_farHalf hw)).comp hinv

theorem poleClearedFirstTraceExponentialContinuation_ne_zero_of_xi_ne_zero
    {s : ℂ} (hs : s ∈ rightHalf) (hxi : xi s ≠ 0) :
    poleClearedFirstTraceExponentialContinuation s ≠ 0 := by
  have hpole : squarefreeMobiusCriticalPoleUnit s ≠ 0 := by
    intro hpole0
    have hfac := xi_eq_xiSquarefreePoleComplement_mul_squarefreeMobiusCriticalPoleUnit hs
    rw [hpole0, mul_zero] at hfac
    exact hxi hfac
  rw [poleClearedFirstTraceExponentialContinuation]
  exact div_ne_zero hpole (squarefreeCarlemanDet_ne_zero _)

theorem poleClearedFirstTraceExponentialContinuation_ne_zero_of_one_le_re
    {s : ℂ} (hs : 1 ≤ s.re) :
    poleClearedFirstTraceExponentialContinuation s ≠ 0 := by
  have hsright : s ∈ rightHalf := by
    rw [mem_rightHalf]
    linarith
  exact poleClearedFirstTraceExponentialContinuation_ne_zero_of_xi_ne_zero hsright
    (xi_ne_zero_of_one_le_re hs)

/-- The transported field is nonzero on the closed Euler disk inside the larger Cayley domain. -/
theorem poleClearedFirstTraceCayleyField_ne_zero_of_norm_le_one
    {w : ℂ} (hw : w ∈ poleFactorCayleyRightDomain) (hnorm : ‖w‖ ≤ 1) :
    poleClearedFirstTraceCayleyField w ≠ 0 := by
  have hre := one_le_re_poleFactorCayleyInv_of_norm_le_one hw hnorm
  exact poleClearedFirstTraceExponentialContinuation_ne_zero_of_one_le_re hre

/-- Every finite point on or inside the arithmetic unit seam has a nonvanishing local analytic
square root. Thus the Euler boundary itself creates no local branch obstruction. -/
theorem exists_local_analytic_sqrt_poleClearedFirstTraceCayleyField_of_norm_le_one
    {w : ℂ} (hw : w ∈ poleFactorCayleyRightDomain) (hnorm : ‖w‖ ≤ 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ g w ≠ 0 ∧
      ∀ᶠ z in 𝓝 w, g z ^ 2 = poleClearedFirstTraceCayleyField z := by
  exact Bottcher.exists_analyticAt_sq_eq
    (analyticOnNhd_poleClearedFirstTraceCayleyField w hw)
    (poleClearedFirstTraceCayleyField_ne_zero_of_norm_le_one hw hnorm)

/-- Exact Cayley-seam formulation of the first arithmetic square-root problem. -/
theorem exists_rightHalf_sqrt_poleClearedFirstTrace_iff_cayleySeam :
    (∃ e : ℂ → ℂ,
      AnalyticOnNhd ℂ e rightHalf ∧
        ∀ s ∈ rightHalf, e s ^ 2 = poleClearedFirstTraceExponentialContinuation s) ↔
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g poleFactorCayleyRightDomain ∧
        ∀ w ∈ poleFactorCayleyRightDomain,
          g w ^ 2 = poleClearedFirstTraceCayleyField w := by
  constructor
  · rintro ⟨e, he, hesq⟩
    refine ⟨fun w => e (poleFactorCayleyInv w), ?_, ?_⟩
    · intro w hw
      exact (he (poleFactorCayleyInv w) (poleFactorCayleyInv_mem_rightHalf hw)).comp
        (analyticOnNhd_poleFactorCayleyInv_rightDomain w hw)
    · intro w hw
      exact hesq (poleFactorCayleyInv w) (poleFactorCayleyInv_mem_rightHalf hw)
  · rintro ⟨g, hg, hgsq⟩
    refine ⟨fun s => g (poleFactorCayley s), ?_, ?_⟩
    · intro s hs
      exact (hg (poleFactorCayley s) (poleFactorCayley_mem_rightDomain hs)).comp
        (analyticOnNhd_poleFactorCayley_rightHalf s hs)
    · intro s hs
      have hsq := hgsq (poleFactorCayley s) (poleFactorCayley_mem_rightDomain hs)
      simpa [poleClearedFirstTraceCayleyField, poleFactorCayleyInv_poleFactorCayley hs]
        using hsq

/-- `RHLadder 1` is exactly analytic square-root continuation across the internal Cayley seam. -/
theorem rhLadder_one_iff_poleClearedFirstTrace_cayleySeam :
    RHLadder 1 ↔
      ∃ g : ℂ → ℂ,
        AnalyticOnNhd ℂ g poleFactorCayleyRightDomain ∧
          ∀ w ∈ poleFactorCayleyRightDomain,
            g w ^ 2 = poleClearedFirstTraceCayleyField w := by
  rw [rhLadder_one_iff_poleClearedFirstTrace_sqrt,
    exists_rightHalf_sqrt_poleClearedFirstTrace_iff_cayleySeam]

/-- Exact arithmetic seam criterion: the fixed Euler half-germ extends from the unit disk to a
square root on the full larger Cayley disk iff `RHLadder 1` holds. -/
theorem rhLadder_one_iff_poleClearedPrimeZetaHalfEuler_cayleySeam_extends :
    RHLadder 1 ↔
      ∃ g : ℂ → ℂ,
        AnalyticOnNhd ℂ g poleFactorCayleyRightDomain ∧
          (∀ w ∈ poleFactorCayleyRightDomain,
            g w ^ 2 = poleClearedFirstTraceCayleyField w) ∧
          EqOn g poleClearedPrimeZetaHalfEulerCayleyGerm (ball (0 : ℂ) 1) := by
  rw [rhLadder_one_iff_poleClearedPrimeZetaHalfEulerGerm_extends]
  constructor
  · rintro ⟨e, he, hesq, heuler⟩
    refine ⟨fun w => e (poleFactorCayleyInv w), ?_, ?_, ?_⟩
    · intro w hw
      exact (he (poleFactorCayleyInv w) (poleFactorCayleyInv_mem_rightHalf hw)).comp
        (analyticOnNhd_poleFactorCayleyInv_rightDomain w hw)
    · intro w hw
      exact hesq (poleFactorCayleyInv w) (poleFactorCayleyInv_mem_rightHalf hw)
    · intro w hw
      exact heuler (poleFactorCayleyInv_mem_farHalf hw)
  · rintro ⟨g, hg, hgsq, heuler⟩
    refine ⟨fun s => g (poleFactorCayley s), ?_, ?_, ?_⟩
    · intro s hs
      exact (hg (poleFactorCayley s) (poleFactorCayley_mem_rightDomain hs)).comp
        (analyticOnNhd_poleFactorCayley_rightHalf s hs)
    · intro s hs
      have hsq := hgsq (poleFactorCayley s) (poleFactorCayley_mem_rightDomain hs)
      simpa [poleClearedFirstTraceCayleyField, poleFactorCayleyInv_poleFactorCayley hs]
        using hsq
    · intro s hs
      have hmatch := heuler (poleFactorCayley_mem_unitBall hs)
      simpa [poleClearedPrimeZetaHalfEulerCayleyGerm,
        poleFactorCayleyInv_poleFactorCayley (farHalf_subset_rightHalf hs)] using hmatch

end

end RHTower
