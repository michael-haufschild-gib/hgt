import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionGaussBulkEffectivityCoercivity

/-!
# Adjacent admission edge paid by two literal arithmetic source actions

Fixed-degree effectivity misses renewal because a degree change replaces the admitted norm.
The shared Jacobi edge is the exact quotient of two neighboring canonical norms.  Its logarithmic
mass velocity is therefore the difference of their two source-paid effectivity currents.

Consequently two adjacent adaptive mixed/completed `P^sharp` bulks control the shared edge across
every common positive chamber.  This is a cross-degree arithmetic action: both amplitudes are
admitted and both completed sources are formed before any reflection or degree aggregation.
-/

open Matrix Polynomial MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Shared multiplicative edge between neighboring canonical admissions. -/
def xiShiftedCanonicalAdmissionAdjacentEdge (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionNorm y n /
    xiShiftedCanonicalAdmissionNorm y (n - 1)

/-- Inside a positive chamber, the shared admission quotient is literally current monic Jacobi
edge. -/
theorem xiShiftedCanonicalAdmissionAdjacentEdge_eq_monicOrthoBeta
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionAdjacentEdge y n =
      HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hprev : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (m + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  rw [xiShiftedCanonicalAdmissionAdjacentEdge]
  simp only [Nat.succ_sub_one]
  rw [
    xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH,
    xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hprev]
  rfl

/-- The neighboring admission norm is positive wherever the common higher block is positive. -/
private theorem xiShiftedCanonicalAdmissionNorm_prev_pos_of_add_two_posDef
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionNorm y (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hprev : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (m + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  simp only [Nat.succ_sub_one]
  rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hprev]
  exact HTGeometry.monicOrthoNorm_pos_below
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hprev) (by omega)

/-- Current admission norm is positive wherever its `(n+2)` block is positive. -/
private theorem xiShiftedCanonicalAdmissionNorm_pos_of_add_two_posDef
    {y : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionNorm y n := by
  rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
  exact HTGeometry.monicOrthoNorm_pos_below
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)

/-- **Adjacent mass--degree curvature law.**  Logarithmic velocity of shared Jacobi edge is exact
difference of neighboring source-paid effectivity rates. -/
theorem hasDerivAt_log_xiShiftedCanonicalAdmissionAdjacentEdge
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 1 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => Real.log (xiShiftedCanonicalAdmissionAdjacentEdge v n))
      (xiShiftedCanonicalAdmissionEffectivityRate y (n - 1) -
        xiShiftedCanonicalAdmissionEffectivityRate y n) y := by
  have hprev : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) ((n - 1) + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hN := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul
    hy (by omega : 0 < n) hH
  have hP := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul
    hy (by omega : 0 < n - 1) hprev
  have hNpos := xiShiftedCanonicalAdmissionNorm_pos_of_add_two_posDef hH
  have hPpos := xiShiftedCanonicalAdmissionNorm_prev_pos_of_add_two_posDef
    (by omega : 0 < n) hH
  have hedge : 0 < xiShiftedCanonicalAdmissionAdjacentEdge y n := by
    exact div_pos hNpos hPpos
  have hratio := hN.div hP hPpos.ne'
  have hlog := hratio.log hedge.ne'
  apply hlog.congr_deriv
  change
    ((-xiShiftedCanonicalAdmissionEffectivityRate y n *
            xiShiftedCanonicalAdmissionNorm y n *
          xiShiftedCanonicalAdmissionNorm y (n - 1) -
        xiShiftedCanonicalAdmissionNorm y n *
          (-xiShiftedCanonicalAdmissionEffectivityRate y (n - 1) *
            xiShiftedCanonicalAdmissionNorm y (n - 1))) /
          xiShiftedCanonicalAdmissionNorm y (n - 1) ^ 2) /
        (xiShiftedCanonicalAdmissionNorm y n /
          xiShiftedCanonicalAdmissionNorm y (n - 1)) = _
  field_simp [hNpos.ne', hPpos.ne']
  ring

/-- **Adjacent arithmetic source action.**  Across a common positive chamber, motion of shared
Jacobi edge is paid by two neighboring literal adaptive mixed/completed `P^sharp` bulks.  This
compares admission across a degree change and uses no source monotonicity premise. -/
theorem log_adjacentEdge_sub_log_adjacentEdge_sq_le_two_literalArithmeticGaussBulk_actions
    {a b : ℝ} (hab : a ≤ b) (ha : 1 / 4 < a) {n : ℕ} (hn : 3 ≤ n)
    (hH : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (Real.log (xiShiftedCanonicalAdmissionAdjacentEdge b n) -
        Real.log (xiShiftedCanonicalAdmissionAdjacentEdge a n)) ^ 2 ≤
      2 * (b - a) *
        (xiShiftedAdmissionEffectivityCauchyWeight n *
            (∫ y in a..b, xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n) +
          xiShiftedAdmissionEffectivityCauchyWeight (n - 1) *
            (∫ y in a..b,
              xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y (n - 1))) := by
  have hHprev : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) ((n - 1) + 2)).PosDef := by
    intro y hy
    exact xiShiftedMomentHankel_posDef_of_le (by omega) (hH y hy)
  have hnAction :=
    log_norm_sub_log_norm_sq_le_literalArithmeticGaussBulk_action_of_posDef
      hab ha (n := n) (by omega) hH
  have hprevAction :=
    log_norm_sub_log_norm_sq_le_literalArithmeticGaussBulk_action_of_posDef
      hab ha (n := n - 1) (by omega) hHprev
  have haMem : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbMem : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hNa := xiShiftedCanonicalAdmissionNorm_pos_of_add_two_posDef (hH a haMem)
  have hNb := xiShiftedCanonicalAdmissionNorm_pos_of_add_two_posDef (hH b hbMem)
  have hPa := xiShiftedCanonicalAdmissionNorm_prev_pos_of_add_two_posDef
    (by omega : 0 < n) (hH a haMem)
  have hPb := xiShiftedCanonicalAdmissionNorm_prev_pos_of_add_two_posDef
    (by omega : 0 < n) (hH b hbMem)
  let x := Real.log (xiShiftedCanonicalAdmissionNorm b n) -
    Real.log (xiShiftedCanonicalAdmissionNorm a n)
  let z := Real.log (xiShiftedCanonicalAdmissionNorm b (n - 1)) -
    Real.log (xiShiftedCanonicalAdmissionNorm a (n - 1))
  have hedgeLog :
      Real.log (xiShiftedCanonicalAdmissionAdjacentEdge b n) -
          Real.log (xiShiftedCanonicalAdmissionAdjacentEdge a n) = x - z := by
    dsimp only [x, z]
    simp only [xiShiftedCanonicalAdmissionAdjacentEdge]
    rw [Real.log_div hNb.ne' hPb.ne', Real.log_div hNa.ne' hPa.ne']
    ring
  have hquad : (x - z) ^ 2 ≤ 2 * (x ^ 2 + z ^ 2) := by
    nlinarith [sq_nonneg (x + z)]
  have hsum := add_le_add hnAction hprevAction
  change x ^ 2 + z ^ 2 ≤ _ at hsum
  calc
    (Real.log (xiShiftedCanonicalAdmissionAdjacentEdge b n) -
        Real.log (xiShiftedCanonicalAdmissionAdjacentEdge a n)) ^ 2 =
        (x - z) ^ 2 := by rw [hedgeLog]
    _ ≤ 2 * (x ^ 2 + z ^ 2) := hquad
    _ ≤ 2 *
        ((b - a) * xiShiftedAdmissionEffectivityCauchyWeight n *
            (∫ y in a..b, xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n) +
          (b - a) * xiShiftedAdmissionEffectivityCauchyWeight (n - 1) *
            (∫ y in a..b,
              xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y (n - 1))) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 2 * (b - a) *
        (xiShiftedAdmissionEffectivityCauchyWeight n *
            (∫ y in a..b, xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n) +
          xiShiftedAdmissionEffectivityCauchyWeight (n - 1) *
            (∫ y in a..b,
              xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y (n - 1))) := by ring

/-- Jacobi-coordinate form of adjacent arithmetic action.  The controlled quantity is the actual
shared Christoffel edge, not an auxiliary norm quotient. -/
theorem log_monicOrthoBeta_sub_log_monicOrthoBeta_sq_le_two_literalArithmeticGaussBulk_actions
    {a b : ℝ} (hab : a ≤ b) (ha : 1 / 4 < a) {n : ℕ} (hn : 3 ≤ n)
    (hH : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (Real.log (HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment b k).re) n) -
        Real.log (HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment a k).re) n)) ^ 2 ≤
      2 * (b - a) *
        (xiShiftedAdmissionEffectivityCauchyWeight n *
            (∫ y in a..b, xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y n) +
          xiShiftedAdmissionEffectivityCauchyWeight (n - 1) *
            (∫ y in a..b,
              xiShiftedCanonicalAdmissionLiteralGaussBulkAtMass y (n - 1))) := by
  have haMem : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbMem : b ∈ Icc a b := ⟨hab, le_rfl⟩
  rw [← xiShiftedCanonicalAdmissionAdjacentEdge_eq_monicOrthoBeta
      (by omega : 0 < n) (hH b hbMem),
    ← xiShiftedCanonicalAdmissionAdjacentEdge_eq_monicOrthoBeta
      (by omega : 0 < n) (hH a haMem)]
  exact
    log_adjacentEdge_sub_log_adjacentEdge_sq_le_two_literalArithmeticGaussBulk_actions
      hab ha hn hH

end

end RHTower
