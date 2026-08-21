import GaloisForLFunctions.RHTower.CCMActualHeadMatchedBoundaryCoverageSeam

/-!
# Rigid matched-to-quantile transport in exponential polar coordinate

The local mass-matched cell and the monotone quantile cell attached to one critical Mellin atom
look unrelated in logarithmic height. In the canonical polar mass coordinate

`Y(h) = 2 exp(h / 2)`,

both are intervals of exactly the same length `criticalMellinAtomWeight n`. Their comparison is
therefore one rigid translation. This module identifies that translation exactly.

For a positive integer `n`, let `R_n` be the outgoing completed critical-Mellin error at `log n`.
The matched-to-quantile displacement `delta_n` satisfies

`delta_n = -R_n - matchedUpperExcess_n`,

where the local upper excess lies in `[0, criticalMellinAtomWeight n]`. Hence

`-R_n - criticalMellinAtomWeight n <= delta_n <= -R_n`.

This converts the matched coverage problem into a rigid-transport problem controlled by the
cumulative completed error up to one local atom. It makes no sign or RH claim.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Canonical exponential coordinate in which outgoing polar measure becomes Lebesgue measure. -/
def ccmActualHeadPolarMassCoordinate (h : ℝ) : ℝ :=
  2 * Real.exp (h / 2)

/-- Inverse logarithmic height coordinate on the positive polar mass ray. -/
def ccmActualHeadPolarHeightCoordinate (y : ℝ) : ℝ :=
  2 * Real.log (y / 2)

theorem ccmActualHeadPolarHeightCoordinate_massCoordinate (h : ℝ) :
    ccmActualHeadPolarHeightCoordinate (ccmActualHeadPolarMassCoordinate h) = h := by
  unfold ccmActualHeadPolarHeightCoordinate ccmActualHeadPolarMassCoordinate
  rw [show 2 * Real.exp (h / 2) / 2 = Real.exp (h / 2) by ring,
    Real.log_exp]
  ring

/-- **Polar mass-coordinate substitution.** The growing exponential polar density is exactly the
Jacobian of `Y(h) = 2 exp(h/2)`, so weighted height integrals become unweighted coordinate
integrals on every oriented finite interval. -/
theorem intervalIntegral_exp_half_mul_eq_polarMassCoordinate
    (lo hi : ℝ) (G : ℝ → ℝ) (hG : Continuous G) :
    (∫ h in lo..hi, Real.exp (h / 2) * G h) =
      ∫ y in ccmActualHeadPolarMassCoordinate lo..
          ccmActualHeadPolarMassCoordinate hi,
        G (ccmActualHeadPolarHeightCoordinate y) := by
  let Y : ℝ → ℝ := ccmActualHeadPolarMassCoordinate
  let Y' : ℝ → ℝ := fun h => Real.exp (h / 2)
  let H : ℝ → ℝ := ccmActualHeadPolarHeightCoordinate
  let g : ℝ → ℝ := fun y => G (H y)
  have hderiv : ∀ h ∈ uIcc lo hi, HasDerivAt Y (Y' h) h := by
    intro h hh
    dsimp only [Y, Y']
    unfold ccmActualHeadPolarMassCoordinate
    apply (((Real.hasDerivAt_exp (h / 2)).comp h
      ((hasDerivAt_id h).div_const 2)).const_mul 2).congr_deriv
    ring
  have hderivCont : ContinuousOn Y' (uIcc lo hi) := by
    dsimp only [Y']
    fun_prop
  have hg : ContinuousOn g (Y '' uIcc lo hi) := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := hy
    have hYpos : 0 < Y h := by
      dsimp only [Y]
      unfold ccmActualHeadPolarMassCoordinate
      positivity
    have hH : ContinuousAt H (Y h) := by
      dsimp only [H]
      unfold ccmActualHeadPolarHeightCoordinate
      have hdiv : ContinuousAt (fun y : ℝ => y / 2) (Y h) :=
        continuousAt_id.div_const 2
      have hlog : ContinuousAt Real.log (Y h / 2) :=
        Real.continuousAt_log
          (div_ne_zero hYpos.ne' (by norm_num : (2 : ℝ) ≠ 0))
      have hlogdiv : ContinuousAt (fun y : ℝ => Real.log (y / 2)) (Y h) :=
        hlog.comp' (f := fun y : ℝ => y / 2) (x := Y h) hdiv
      exact hlogdiv.const_mul 2
    exact (hG.continuousAt.comp hH).continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hderivCont hg
  change (∫ h in lo..hi, (g ∘ Y) h * Y' h) =
    ∫ y in Y lo..Y hi, g y at hsub
  calc
    (∫ h in lo..hi, Real.exp (h / 2) * G h) =
        ∫ h in lo..hi, (g ∘ Y) h * Y' h := by
      apply intervalIntegral.integral_congr
      intro h hh
      dsimp only [g, Y, Y', H, Function.comp_apply]
      rw [ccmActualHeadPolarHeightCoordinate_massCoordinate]
      ring
    _ = ∫ y in Y lo..Y hi, g y := hsub
    _ = _ := by rfl

/-- Translation-defect profile pulled to exponential polar mass coordinate. -/
def ccmActualHeadPolarMassDefectProfile (f : SoninL2) (y : ℝ) : ℝ :=
  ccmActualHeadTranslationDefect (ccmActualHeadPolarHeightCoordinate y) f

/-- Outgoing polar defect carried by one monotone quantile cell. -/
def ccmActualHeadOutgoingQuantilePolarCell (n : ℕ) (f : SoninL2) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary n..
      ccmOutgoingPrimeQuantileBoundary (n + 1),
    Real.exp (h / 2) * ccmActualHeadTranslationDefect h f

/-- Lower endpoint of a matched symmetric cell in exponential polar mass coordinate. -/
def ccmActualHeadMatchedPolarLowerCoordinate (n : ℕ) : ℝ :=
  2 * Real.exp
    ((Real.log n - ccmActualHeadMatchedPrimePolarRadius n) / 2)

/-- Upper endpoint of a matched symmetric cell in exponential polar mass coordinate. -/
def ccmActualHeadMatchedPolarUpperCoordinate (n : ℕ) : ℝ :=
  2 * Real.exp
    ((Real.log n + ccmActualHeadMatchedPrimePolarRadius n) / 2)

/-- Monotone quantile boundary in exponential polar mass coordinate. -/
def ccmActualHeadQuantilePolarCoordinate (N : ℕ) : ℝ :=
  2 * Real.exp (ccmOutgoingPrimeQuantileBoundary N / 2)

/-- Rigid translation carrying the matched cell to its equal-mass quantile cell. -/
def ccmActualHeadMatchedQuantilePolarDisplacement (n : ℕ) : ℝ :=
  ccmActualHeadQuantilePolarCoordinate n -
    ccmActualHeadMatchedPolarLowerCoordinate n

/-- Completed critical-Mellin error after removal of the incoming Gamma tail. -/
def ccmActualHeadOutgoingNodeError (n : ℕ) : ℝ :=
  criticalMellinCompletedError (Real.log n) -
    2 * (1 - Real.exp (-(Real.log n / 2)))

theorem ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative (N : ℕ) :
    ccmActualHeadQuantilePolarCoordinate N =
      2 + ccmOutgoingPrimeCumulative N := by
  unfold ccmActualHeadQuantilePolarCoordinate
  rw [exp_half_ccmOutgoingPrimeQuantileBoundary]
  ring

/-- Every quantile cell has coordinate length exactly equal to its critical Mellin atom. -/
theorem ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight (n : ℕ) :
    ccmActualHeadQuantilePolarCoordinate (n + 1) -
        ccmActualHeadQuantilePolarCoordinate n =
      criticalMellinAtomWeight n := by
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative,
    ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative,
    ccmOutgoingPrimeCumulative_succ]
  ring

/-- Every symmetric matched cell has the same coordinate length as its quantile cell. -/
theorem ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight (n : ℕ) :
    ccmActualHeadMatchedPolarUpperCoordinate n -
        ccmActualHeadMatchedPolarLowerCoordinate n =
      criticalMellinAtomWeight n := by
  have hmass := integral_exp_half_matchedPrimePolarCell_eq_atomWeight n
  rw [intervalIntegral_exp_half_eq] at hmass
  simpa only [ccmActualHeadMatchedPolarUpperCoordinate,
    ccmActualHeadMatchedPolarLowerCoordinate] using hmass

/-- A matched polar cell is an unweighted defect integral on its mass-coordinate interval. -/
theorem ccmActualHeadMatchedPolarCell_eq_polarMassCoordinate
    (n : ℕ) (f : SoninL2) :
    ccmActualHeadOutgoingPolarSymmetricCell
        (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f =
      ∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
          ccmActualHeadMatchedPolarUpperCoordinate n,
        ccmActualHeadPolarMassDefectProfile f y := by
  have hE : Continuous fun h : ℝ => ccmActualHeadTranslationDefect h f := by
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
  unfold ccmActualHeadOutgoingPolarSymmetricCell
  simpa only [ccmActualHeadMatchedPolarLowerCoordinate,
    ccmActualHeadMatchedPolarUpperCoordinate, ccmActualHeadPolarMassCoordinate,
    ccmActualHeadPolarMassDefectProfile] using
      intervalIntegral_exp_half_mul_eq_polarMassCoordinate
        (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)
        (Real.log n + ccmActualHeadMatchedPrimePolarRadius n)
        (fun h => ccmActualHeadTranslationDefect h f) hE

/-- A quantile polar cell is the same unweighted defect profile on its quantile-coordinate
interval. -/
theorem ccmActualHeadOutgoingQuantilePolarCell_eq_polarMassCoordinate
    (n : ℕ) (f : SoninL2) :
    ccmActualHeadOutgoingQuantilePolarCell n f =
      ∫ y in ccmActualHeadQuantilePolarCoordinate n..
          ccmActualHeadQuantilePolarCoordinate (n + 1),
        ccmActualHeadPolarMassDefectProfile f y := by
  have hE : Continuous fun h : ℝ => ccmActualHeadTranslationDefect h f := by
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
  unfold ccmActualHeadOutgoingQuantilePolarCell
  simpa only [ccmActualHeadQuantilePolarCoordinate,
    ccmActualHeadPolarMassCoordinate, ccmActualHeadPolarMassDefectProfile] using
      intervalIntegral_exp_half_mul_eq_polarMassCoordinate
        (ccmOutgoingPrimeQuantileBoundary n)
        (ccmOutgoingPrimeQuantileBoundary (n + 1))
        (fun h => ccmActualHeadTranslationDefect h f) hE

/-- Equal coordinate lengths force lower- and upper-endpoint displacement to agree exactly. -/
theorem ccmActualHeadMatchedQuantilePolarDisplacement_eq_upper (n : ℕ) :
    ccmActualHeadMatchedQuantilePolarDisplacement n =
      ccmActualHeadQuantilePolarCoordinate (n + 1) -
        ccmActualHeadMatchedPolarUpperCoordinate n := by
  unfold ccmActualHeadMatchedQuantilePolarDisplacement
  have hq := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight n
  have hm := ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight n
  linarith

/-- Matched endpoints retain the arithmetic center as their geometric mean. -/
theorem ccmActualHeadMatchedPolarLower_mul_upper (n : ℕ) (hn : 0 < n) :
    ccmActualHeadMatchedPolarLowerCoordinate n *
        ccmActualHeadMatchedPolarUpperCoordinate n =
      4 * n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold ccmActualHeadMatchedPolarLowerCoordinate
    ccmActualHeadMatchedPolarUpperCoordinate
  calc
    2 * Real.exp ((Real.log n - ccmActualHeadMatchedPrimePolarRadius n) / 2) *
          (2 * Real.exp
            ((Real.log n + ccmActualHeadMatchedPrimePolarRadius n) / 2)) =
        4 * (Real.exp
            ((Real.log n - ccmActualHeadMatchedPrimePolarRadius n) / 2) *
          Real.exp
            ((Real.log n + ccmActualHeadMatchedPrimePolarRadius n) / 2)) := by ring
    _ = 4 * Real.exp
        ((Real.log n - ccmActualHeadMatchedPrimePolarRadius n) / 2 +
          (Real.log n + ccmActualHeadMatchedPrimePolarRadius n) / 2) := by
      rw [Real.exp_add]
    _ = 4 * Real.exp (Real.log n) := by
      congr 2
      ring
    _ = 4 * n := by rw [Real.exp_log hnpos]

/-- The arithmetic center lies between the two matched endpoints. -/
theorem ccmActualHeadMatchedPolarCenter_mem (n : ℕ) :
    ccmActualHeadMatchedPolarLowerCoordinate n ≤
        2 * Real.exp (Real.log n / 2) ∧
      2 * Real.exp (Real.log n / 2) ≤
        ccmActualHeadMatchedPolarUpperCoordinate n := by
  have hρ := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  constructor
  · unfold ccmActualHeadMatchedPolarLowerCoordinate
    gcongr
    linarith
  · unfold ccmActualHeadMatchedPolarUpperCoordinate
    gcongr
    linarith

/-- The local matched upper half-cell excess is between zero and one full atom weight. -/
theorem ccmActualHeadMatchedPolarUpperExcess_mem_atomWeight (n : ℕ) :
    0 ≤ ccmActualHeadMatchedPolarUpperCoordinate n -
        2 * Real.exp (Real.log n / 2) ∧
      ccmActualHeadMatchedPolarUpperCoordinate n -
          2 * Real.exp (Real.log n / 2) ≤
        criticalMellinAtomWeight n := by
  have hcenter := ccmActualHeadMatchedPolarCenter_mem n
  have hwidth := ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight n
  constructor <;> linarith

/-- Exact cumulative-error displacement of the upper quantile boundary from the arithmetic
center. -/
theorem two_exp_log_half_sub_quantile_succ_eq_outgoingNodeError
    (n : ℕ) (hn : 0 < n) :
    2 * Real.exp (Real.log n / 2) -
        ccmActualHeadQuantilePolarCoordinate (n + 1) =
      ccmActualHeadOutgoingNodeError n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : Real.exp (Real.log n) = (n : ℝ) := Real.exp_log hnpos
  have hterminal :=
    quantileTerminalMass_eq_completedError_sub_threshold (Real.log n)
  simp only [hexp, Nat.floor_natCast] at hterminal
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative]
  unfold ccmActualHeadOutgoingNodeError
  exact hterminal

/-- **Rigid matched-to-quantile transport law.** In exponential polar mass coordinate, the cell
translation is the negative outgoing completed error minus the local matched upper excess. -/
theorem ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess
    (n : ℕ) (hn : 0 < n) :
    ccmActualHeadMatchedQuantilePolarDisplacement n =
      -ccmActualHeadOutgoingNodeError n -
        (ccmActualHeadMatchedPolarUpperCoordinate n -
          2 * Real.exp (Real.log n / 2)) := by
  have hrigid := ccmActualHeadMatchedQuantilePolarDisplacement_eq_upper n
  have herror :=
    two_exp_log_half_sub_quantile_succ_eq_outgoingNodeError n hn
  linarith

/-- **One-atom completed-error corridor.** Rigid cell displacement differs from negative outgoing
completed error by a quantity between zero and exactly one critical Mellin atom. -/
theorem ccmActualHeadMatchedQuantilePolarDisplacement_mem_errorCorridor
    (n : ℕ) (hn : 0 < n) :
    -ccmActualHeadOutgoingNodeError n - criticalMellinAtomWeight n ≤
        ccmActualHeadMatchedQuantilePolarDisplacement n ∧
      ccmActualHeadMatchedQuantilePolarDisplacement n ≤
        -ccmActualHeadOutgoingNodeError n := by
  have hid :=
    ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess n hn
  have hexcess := ccmActualHeadMatchedPolarUpperExcess_mem_atomWeight n
  constructor <;> linarith

/-- Nonnegative outgoing error shifts the entire quantile cell weakly left of the matched cell. -/
theorem ccmActualHeadQuantilePolarCell_le_matchedPolarCell_of_outgoingNodeError_nonneg
    (n : ℕ) (hn : 0 < n) (herror : 0 ≤ ccmActualHeadOutgoingNodeError n) :
    ccmActualHeadQuantilePolarCoordinate n ≤
        ccmActualHeadMatchedPolarLowerCoordinate n ∧
      ccmActualHeadQuantilePolarCoordinate (n + 1) ≤
        ccmActualHeadMatchedPolarUpperCoordinate n := by
  have hcorridor :=
    ccmActualHeadMatchedQuantilePolarDisplacement_mem_errorCorridor n hn
  have hδ : ccmActualHeadMatchedQuantilePolarDisplacement n ≤ 0 := by linarith
  rw [ccmActualHeadMatchedQuantilePolarDisplacement_eq_upper] at hδ
  constructor
  · unfold ccmActualHeadMatchedQuantilePolarDisplacement at hcorridor
    linarith
  · linarith

/-- Error at most minus one atom shifts the entire matched cell weakly left of the quantile cell. -/
theorem ccmActualHeadMatchedPolarCell_le_quantilePolarCell_of_outgoingNodeError_le_neg_weight
    (n : ℕ) (hn : 0 < n)
    (herror : ccmActualHeadOutgoingNodeError n ≤ -criticalMellinAtomWeight n) :
    ccmActualHeadMatchedPolarLowerCoordinate n ≤
        ccmActualHeadQuantilePolarCoordinate n ∧
      ccmActualHeadMatchedPolarUpperCoordinate n ≤
        ccmActualHeadQuantilePolarCoordinate (n + 1) := by
  have hcorridor :=
    ccmActualHeadMatchedQuantilePolarDisplacement_mem_errorCorridor n hn
  have hδ : 0 ≤ ccmActualHeadMatchedQuantilePolarDisplacement n := by linarith
  have hδupper := hδ
  rw [ccmActualHeadMatchedQuantilePolarDisplacement_eq_upper] at hδupper
  constructor
  · unfold ccmActualHeadMatchedQuantilePolarDisplacement at hδ
    linarith
  · linarith

/-- A quantile polar cell is the matched mass-coordinate interval translated rigidly by the
completed-error displacement. -/
theorem ccmActualHeadOutgoingQuantilePolarCell_eq_matchedCoordinateTranslate
    (n : ℕ) (f : SoninL2) :
    ccmActualHeadOutgoingQuantilePolarCell n f =
      ∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
          ccmActualHeadMatchedPolarUpperCoordinate n,
        ccmActualHeadPolarMassDefectProfile f
          (ccmActualHeadMatchedQuantilePolarDisplacement n + y) := by
  rw [ccmActualHeadOutgoingQuantilePolarCell_eq_polarMassCoordinate]
  have hlo : ccmActualHeadQuantilePolarCoordinate n =
      ccmActualHeadMatchedQuantilePolarDisplacement n +
        ccmActualHeadMatchedPolarLowerCoordinate n := by
    unfold ccmActualHeadMatchedQuantilePolarDisplacement
    ring
  have hhi : ccmActualHeadQuantilePolarCoordinate (n + 1) =
      ccmActualHeadMatchedQuantilePolarDisplacement n +
        ccmActualHeadMatchedPolarUpperCoordinate n := by
    have hrigid := ccmActualHeadMatchedQuantilePolarDisplacement_eq_upper n
    linarith
  rw [hlo, hhi]
  exact (intervalIntegral.integral_comp_add_left
    (a := ccmActualHeadMatchedPolarLowerCoordinate n)
    (b := ccmActualHeadMatchedPolarUpperCoordinate n)
    (ccmActualHeadPolarMassDefectProfile f)
    (ccmActualHeadMatchedQuantilePolarDisplacement n)).symm

/-- **Cellwise matched/quantile coverage transport.** Their polar energies differ only by a rigid
translation of one common mass-coordinate interval. The translation is already trapped in the
one-atom completed-error corridor. -/
theorem ccmActualHeadMatchedPolarCell_sub_quantilePolarCell_eq_rigidTransport
    (n : ℕ) (f : SoninL2) :
    ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f -
        ccmActualHeadOutgoingQuantilePolarCell n f =
      (∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
          ccmActualHeadMatchedPolarUpperCoordinate n,
        ccmActualHeadPolarMassDefectProfile f y) -
      ∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
          ccmActualHeadMatchedPolarUpperCoordinate n,
        ccmActualHeadPolarMassDefectProfile f
          (ccmActualHeadMatchedQuantilePolarDisplacement n + y) := by
  rw [ccmActualHeadMatchedPolarCell_eq_polarMassCoordinate,
    ccmActualHeadOutgoingQuantilePolarCell_eq_matchedCoordinateTranslate]

private theorem sum_range_succ_eq_sum_Icc_two
    (M : ℕ) (H : ℕ → ℝ) (h0 : H 0 = 0) (h1 : H 1 = 0) :
    (∑ n ∈ Finset.range (M + 1), H n) = ∑ n ∈ Finset.Icc 2 M, H n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro n hnrange hnnot
    simp only [Finset.mem_range] at hnrange
    have hnlt : n < 2 := by
      by_contra h
      have hn2 : 2 ≤ n := Nat.le_of_not_gt h
      exact hnnot (Finset.mem_Icc.mpr ⟨hn2, by omega⟩)
    interval_cases n
    · exact h0
    · exact h1

/-- **Global rigid coverage decomposition.** The whole matched coverage seam is the finite sum of
cellwise rigid mass-coordinate translations, followed by one terminal quantile interval. Every
cell displacement in this formula is controlled by the one-atom completed-error corridor. -/
theorem ccmActualHeadMatchedPolarCoverageSeam_eq_rigidCellTransports_sub_terminal
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmActualHeadMatchedPolarCoverageSeam a f =
      (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        ((∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
              ccmActualHeadMatchedPolarUpperCoordinate n,
            ccmActualHeadPolarMassDefectProfile f.1 y) -
          ∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
              ccmActualHeadMatchedPolarUpperCoordinate n,
            ccmActualHeadPolarMassDefectProfile f.1
              (ccmActualHeadMatchedQuantilePolarDisplacement n + y))) -
      ∫ h in ccmOutgoingPrimeQuantileBoundary
          (Nat.floor (Real.exp (2 * a.1)) + 1)..(2 * a.1),
        Real.exp (h / 2) * ccmActualHeadTranslationDefect h f.1 := by
  let M := Nat.floor (Real.exp (2 * a.1))
  let N := M + 1
  let F := Finset.Icc 2 M
  let P : ℕ → ℝ := fun n => ccmActualHeadOutgoingPolarSymmetricCell
    (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1
  let Q : ℕ → ℝ := fun n => ccmActualHeadOutgoingQuantilePolarCell n f.1
  let W : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * ccmActualHeadTranslationDefect h f.1
  have hQ0 : Q 0 = 0 := by
    simp [Q, ccmActualHeadOutgoingQuantilePolarCell,
      ccmOutgoingPrimeQuantileBoundary, ccmOutgoingPrimeCumulative,
      criticalMellinAtomWeight]
  have hQ1 : Q 1 = 0 := by
    simp [Q, ccmActualHeadOutgoingQuantilePolarCell,
      ccmOutgoingPrimeQuantileBoundary, ccmOutgoingPrimeCumulative,
      Finset.sum_range_succ, criticalMellinAtomWeight,
      ArithmeticFunction.vonMangoldt]
  have hQsum : (∑ n ∈ Finset.range N, Q n) = ∑ n ∈ F, Q n := by
    dsimp only [N, F]
    exact sum_range_succ_eq_sum_Icc_two M Q hQ0 hQ1
  have hQpartition : (∑ n ∈ F, Q n) =
      ∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N, W h := by
    rw [← hQsum]
    simpa only [Q, W, ccmActualHeadOutgoingQuantilePolarCell] using
      (integral_exp_half_translationDefect_zero_to_quantileBoundary N f.1).symm
  have hW : Continuous W := by
    dsimp only [W]
    exact (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul
      ((((continuous_logTranslationCLM f.1).sub continuous_const).norm).pow 2)
  have hsplit : (∫ h in (0 : ℝ)..(2 * a.1), W h) =
      (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N, W h) +
        ∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1), W h :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hW.intervalIntegrable (μ := volume) 0
        (ccmOutgoingPrimeQuantileBoundary N))
      (hW.intervalIntegrable (μ := volume)
        (ccmOutgoingPrimeQuantileBoundary N) (2 * a.1))).symm
  unfold ccmActualHeadMatchedPolarCoverageSeam
  rw [ccmActualHeadOutgoingPolarEnergy,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [a.property])]
  change (∑ n ∈ F, P n) - (∫ h in (0 : ℝ)..(2 * a.1), W h) = _
  rw [hsplit, ← hQpartition]
  rw [show (∑ n ∈ F, P n) -
      ((∑ n ∈ F, Q n) +
        ∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1), W h) =
      (∑ n ∈ F, (P n - Q n)) -
        ∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1), W h by
    rw [Finset.sum_sub_distrib]
    ring]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro n hn
    dsimp only [P, Q]
    exact ccmActualHeadMatchedPolarCell_sub_quantilePolarCell_eq_rigidTransport n f.1
  · rfl

end RHTower
