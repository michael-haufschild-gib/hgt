import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceRecessionFlow
import GaloisForLFunctions.RHTower.XiShiftedHalfDensityAdjacentConnection

/-!
# Degree connection for the adaptive arithmetic source

The difference of neighboring norm-normalized canonical sources is a mixed degree--mass Ward
current.  Before mass evolution it contains three adjacent Jacobi beta edges.  Substitution of the
actual nonisospectral alpha flows cancels all of them.  What remains is the adjacent diagonal
midpoint Riccati term plus one alpha-gap/trace-load coupling.

At fixed degree its normalized recession increment is exactly one.  Thus neighboring source
ordering is eventually strict for every fixed pair; the remaining obstruction is uniformity along
a degree-changing schedule.
-/

open Filter Matrix Polynomial Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Expanded trace form of adaptive Jacobi source energy. -/
theorem adaptiveOrthoJacobiEnergy_eq_traceForm
    (s : ℕ → ℝ) (n : ℕ) :
    HTGeometry.adaptiveOrthoJacobiEnergy s n =
      (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ 2) +
      HTGeometry.monicOrthoAlpha s n *
        (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
      (n + 1 : ℝ) * HTGeometry.monicOrthoAlpha s n ^ 2 +
      2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
      (n + 1 : ℝ) *
        (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1)) := by
  have hpoint (j : ℕ) :
      (HTGeometry.monicOrthoAlpha s j + HTGeometry.monicOrthoAlpha s n / 2) ^ 2 =
        HTGeometry.monicOrthoAlpha s j ^ 2 +
          HTGeometry.monicOrthoAlpha s n * HTGeometry.monicOrthoAlpha s j +
          HTGeometry.monicOrthoAlpha s n ^ 2 / 4 := by ring
  rw [HTGeometry.adaptiveOrthoJacobiEnergy]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Raw neighboring-degree source-energy difference before using mass evolution. -/
theorem adaptiveOrthoJacobiEnergy_succ_sub_eq
    (s : ℕ → ℝ) (n : ℕ) :
    HTGeometry.adaptiveOrthoJacobiEnergy s (n + 1) -
        HTGeometry.adaptiveOrthoJacobiEnergy s n =
      (HTGeometry.monicOrthoAlpha s (n + 1) -
          HTGeometry.monicOrthoAlpha s n) *
        (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
      HTGeometry.monicOrthoAlpha s n * HTGeometry.monicOrthoAlpha s (n + 1) -
      (n : ℝ) * HTGeometry.monicOrthoAlpha s n ^ 2 +
      (n + 2 : ℝ) * HTGeometry.monicOrthoAlpha s (n + 1) ^ 2 +
      (1 - (n : ℝ)) * HTGeometry.monicOrthoBeta s n +
      HTGeometry.monicOrthoBeta s (n + 1) +
      (n + 2 : ℝ) * HTGeometry.monicOrthoBeta s (n + 2) := by
  rw [adaptiveOrthoJacobiEnergy_eq_traceForm,
    adaptiveOrthoJacobiEnergy_eq_traceForm]
  simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  ring

/-- **Beta-edge cancellation law.**  Neighboring adaptive source energies differ only through
the adjacent diagonal connection once actual mass evolution is inserted. -/
theorem xiShiftedAdaptiveOrthoJacobiEnergy_succ_sub_eq_diagonalConnection
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef) :
    let s := fun k => (xiShiftedReciprocalMoment y k).re
    HTGeometry.adaptiveOrthoJacobiEnergy s (n + 1) -
        HTGeometry.adaptiveOrthoJacobiEnergy s n =
      (HTGeometry.monicOrthoAlpha s (n + 1) - HTGeometry.monicOrthoAlpha s n) *
          (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
        HTGeometry.monicOrthoAlpha s n * HTGeometry.monicOrthoAlpha s (n + 1) -
        ((n : ℝ) + 1 / 2) * HTGeometry.monicOrthoAlpha s n ^ 2 +
        ((n : ℝ) + 3 / 2) * HTGeometry.monicOrthoAlpha s (n + 1) ^ 2 -
        1 / 2 *
          (deriv (fun v => xiShiftedCanonicalAdmissionAlpha v n) y +
            deriv (fun v => xiShiftedCanonicalAdmissionAlpha v (n + 1)) y) := by
  dsimp only
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hHn : (HTGeometry.momentHankelMatrix s (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hflowN := hasDerivAt_xiShiftedCanonicalAdmissionAlpha_eq_adjacentJacobiFlow
    hy hn hHn
  have hflowS := hasDerivAt_xiShiftedCanonicalAdmissionAlpha_eq_adjacentJacobiFlow
    hy (n := n + 1) (by omega) hH
  rw [hflowN.deriv, hflowS.deriv]
  have henergy := adaptiveOrthoJacobiEnergy_succ_sub_eq s n
  rw [henergy]
  push_cast
  ring

/-- Literal norm-normalized neighboring arithmetic sources differ by the same diagonal mass
connection.  Admission and source formation both occur before the quotient. -/
theorem xiShiftedCanonicalArithmeticSource_succ_sub_eq_diagonalConnection
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef) :
    let s := xiShiftedRealMomentSequence w
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial s (n + 1)) /
        (2 * HTGeometry.monicOrthoNormSq s (n + 1)) -
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial s n) /
        (2 * HTGeometry.monicOrthoNormSq s n) =
      (HTGeometry.monicOrthoAlpha s (n + 1) - HTGeometry.monicOrthoAlpha s n) *
          (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
        HTGeometry.monicOrthoAlpha s n * HTGeometry.monicOrthoAlpha s (n + 1) -
        ((n : ℝ) + 1 / 2) * HTGeometry.monicOrthoAlpha s n ^ 2 +
        ((n : ℝ) + 3 / 2) * HTGeometry.monicOrthoAlpha s (n + 1) ^ 2 -
        1 / 2 *
          (deriv (fun v => xiShiftedCanonicalAdmissionAlpha v n) (w ^ 2) +
            deriv (fun v => xiShiftedCanonicalAdmissionAlpha v (n + 1)) (w ^ 2)) := by
  dsimp only
  let s := xiShiftedRealMomentSequence w
  have hHn : (HTGeometry.momentHankelMatrix s (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hsourceN :=
    xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_jacobiEnergy
      hw hn hHn
  have hsourceS :=
    xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_jacobiEnergy
      hw (n := n + 1) (by omega) hH
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnormN : HTGeometry.monicOrthoNormSq s n ≠ 0 :=
    ne_of_gt (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega))
  have hnormS : HTGeometry.monicOrthoNormSq s (n + 1) ≠ 0 :=
    ne_of_gt (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega))
  rw [hsourceN, hsourceS]
  have hcancelN :
      (2 * HTGeometry.monicOrthoNormSq s n *
          HTGeometry.adaptiveOrthoJacobiEnergy s n) /
          (2 * HTGeometry.monicOrthoNormSq s n) =
        HTGeometry.adaptiveOrthoJacobiEnergy s n := by
    field_simp [hnormN]
  have hcancelS :
      (2 * HTGeometry.monicOrthoNormSq s (n + 1) *
          HTGeometry.adaptiveOrthoJacobiEnergy s (n + 1)) /
          (2 * HTGeometry.monicOrthoNormSq s (n + 1)) =
        HTGeometry.adaptiveOrthoJacobiEnergy s (n + 1) := by
    field_simp [hnormS]
  change
    (2 * HTGeometry.monicOrthoNormSq s (n + 1) *
          HTGeometry.adaptiveOrthoJacobiEnergy s (n + 1)) /
        (2 * HTGeometry.monicOrthoNormSq s (n + 1)) -
      (2 * HTGeometry.monicOrthoNormSq s n *
          HTGeometry.adaptiveOrthoJacobiEnergy s n) /
        (2 * HTGeometry.monicOrthoNormSq s n) = _
  rw [hcancelN, hcancelS]
  exact xiShiftedAdaptiveOrthoJacobiEnergy_succ_sub_eq_diagonalConnection
    (sq_pos_of_pos (by linarith : 0 < w)) hn hH

/-- **Midpoint/gap Ward law.**  The neighboring source increment is midpoint Riccati drift plus
one adjacent alpha-gap/trace-load coupling. -/
theorem xiShiftedCanonicalArithmeticSource_succ_sub_eq_midpointGap
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef) :
    let s := xiShiftedRealMomentSequence w
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial s (n + 1)) /
        (2 * HTGeometry.monicOrthoNormSq s (n + 1)) -
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial s n) /
        (2 * HTGeometry.monicOrthoNormSq s n) =
      1 / 2 *
          (HTGeometry.monicOrthoAlpha s n +
            HTGeometry.monicOrthoAlpha s (n + 1)) ^ 2 +
        (HTGeometry.monicOrthoAlpha s (n + 1) -
            HTGeometry.monicOrthoAlpha s n) *
          ((∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
            (n + 1 : ℝ) *
              (HTGeometry.monicOrthoAlpha s n +
                HTGeometry.monicOrthoAlpha s (n + 1))) -
        1 / 2 *
          (deriv (fun v => xiShiftedCanonicalAdmissionAlpha v n) (w ^ 2) +
            deriv (fun v => xiShiftedCanonicalAdmissionAlpha v (n + 1)) (w ^ 2)) := by
  dsimp only
  have h := xiShiftedCanonicalArithmeticSource_succ_sub_eq_diagonalConnection
    hw hn hH
  dsimp only at h
  rw [h]
  ring

/-- Exact neighboring-degree source monotonicity criterion in diagonal connection coordinates. -/
theorem xiShiftedCanonicalArithmeticSource_succ_ge_iff_midpointConnection
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef) :
    let s := xiShiftedRealMomentSequence w
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial s n) /
        (2 * HTGeometry.monicOrthoNormSq s n) ≤
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial s (n + 1)) /
        (2 * HTGeometry.monicOrthoNormSq s (n + 1)) ↔
      1 / 2 *
          (deriv (fun v => xiShiftedCanonicalAdmissionAlpha v n) (w ^ 2) +
            deriv (fun v => xiShiftedCanonicalAdmissionAlpha v (n + 1)) (w ^ 2)) ≤
        1 / 2 *
            (HTGeometry.monicOrthoAlpha s n +
              HTGeometry.monicOrthoAlpha s (n + 1)) ^ 2 +
          (HTGeometry.monicOrthoAlpha s (n + 1) -
              HTGeometry.monicOrthoAlpha s n) *
            ((∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
              (n + 1 : ℝ) *
                (HTGeometry.monicOrthoAlpha s n +
                  HTGeometry.monicOrthoAlpha s (n + 1))) := by
  dsimp only
  rw [sub_nonneg.symm,
    xiShiftedCanonicalArithmeticSource_succ_sub_eq_midpointGap hw hn hH]
  constructor <;> intro h <;> linarith

/-- Fixed neighboring degree has unit normalized source increment at recession. -/
theorem tendsto_relativeArithmeticSource_succ_sub_one
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto
      (fun w : ℝ =>
        XiShiftedCanonicalAdmission.relativeArithmeticSource w (n + 1) -
          XiShiftedCanonicalAdmission.relativeArithmeticSource w n)
      atTop (nhds 1) := by
  have hs := XiShiftedCanonicalAdmission.tendsto_relativeArithmeticSource
    (n := n + 1) (by omega)
  have hnlim := XiShiftedCanonicalAdmission.tendsto_relativeArithmeticSource hn
  convert hs.sub hnlim using 1
  norm_num

/-- Every fixed adjacent pair of norm-normalized sources is eventually strictly degree ordered. -/
theorem relativeArithmeticSource_eventually_strictMono_succ
    {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ w : ℝ in atTop,
      XiShiftedCanonicalAdmission.relativeArithmeticSource w n <
        XiShiftedCanonicalAdmission.relativeArithmeticSource w (n + 1) := by
  have h := (tendsto_relativeArithmeticSource_succ_sub_one hn).eventually
    (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h] with w hw
  linarith

/-- Every fixed finite prefix of the norm-normalized arithmetic source tower is eventually a
strict degree staircase.  This is the strongest finite synchronization supplied by pointwise
recession; it deliberately makes no degree-uniform claim. -/
theorem relativeArithmeticSource_eventually_strictMono_forall_le
    (d : ℕ) :
    ∀ᶠ w : ℝ in atTop, ∀ n : ℕ, 0 < n → n ≤ d →
      XiShiftedCanonicalAdmission.relativeArithmeticSource w n <
        XiShiftedCanonicalAdmission.relativeArithmeticSource w (n + 1) := by
  have hstep : ∀ n ∈ Finset.Icc 1 d, ∀ᶠ w : ℝ in atTop,
      XiShiftedCanonicalAdmission.relativeArithmeticSource w n <
        XiShiftedCanonicalAdmission.relativeArithmeticSource w (n + 1) :=
    fun n hn => relativeArithmeticSource_eventually_strictMono_succ
      (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  filter_upwards [(eventually_all_finset (Finset.Icc 1 d)).mpr hstep] with w hw
  intro n hn hnd
  exact hw n (Finset.mem_Icc.mpr ⟨hn, hnd⟩)

end
end RHTower
