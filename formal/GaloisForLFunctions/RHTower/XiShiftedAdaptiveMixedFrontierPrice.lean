import GaloisForLFunctions.RHTower.XiShiftedHankelFirstContactCurvatureQuotient

/-!
# Source-first adaptive mixed curvature price on shifted-Xi odd contact

The literal completed adaptive `P^sharp` source already lands on twice the first odd Padé defect.
The parity-complete contact law prices the square of that defect by actual integral Lipschitz cost.
This module identifies the two: square of the pre-aggregation arithmetic source is exactly the
curvature numerator paid by terminal-frontier displacement.

No orientation map, fixed reporter, numerical estimate, or RH premise enters.
-/

open Matrix Polynomial

namespace RHTower

noncomputable section

/-- Integral-Lipschitz curvature price carried by the literal adaptive mixed/completed arithmetic
source at a proposed odd contact.  Both amplitudes enter source formation before aggregation. -/
noncomputable def xiShiftedAdaptiveMixedOddContactFrontierPrice
    (w : ℝ) (n m : ℕ) (c : Fin (n + 1) → ℝ) (B : Polynomial ℝ) : ℝ :=
  let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment (w ^ 2) j).re
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let U := P * X ^ m
  let V := P * X ^ (m + 1)
  let a := HTGeometry.momentInner s V V
  let A := xiShiftedAdaptiveNullPairPolynomial (w ^ 2) U V
  let x := Polynomial.toFn (n + m + 2) A
  ((xiShiftedNondegenerateNullFlagCompletedArithmeticSource
        w (n + m) U B / 2) ^ 2 *
      (2 * (|a| + 1) - a) / (|a| + 1) ^ 2) /
    xiShiftedMomentHankelQuadraticLipschitzWeight x

/-- **Exact arithmetic source law.**  On a higher odd null contact, the literal adaptive
mixed/completed `P^sharp` source is twice the first Padé defect, so its frontier price is exactly
the parity-complete null-pair curvature quotient. -/
theorem xiShiftedAdaptiveMixedOddContactFrontierPrice_eq_firstOddDefect
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ j < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c j = 0)
    (B : Polynomial ℝ) :
    let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment (w ^ 2) j).re
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let V := P * X ^ (m + 1)
    let δ := xiShiftedHankelBoundaryPadeDefect (w ^ 2) c
      (2 * n + (2 * m + 1))
    let a := HTGeometry.momentInner s V V
    let A := xiShiftedAdaptiveNullPairPolynomial (w ^ 2) (P * X ^ m) V
    let x := Polynomial.toFn (n + m + 2) A
    xiShiftedAdaptiveMixedOddContactFrontierPrice w n m c B =
      (δ ^ 2 * (2 * (|a| + 1) - a) / (|a| + 1) ^ 2) /
        xiShiftedMomentHankelQuadraticLipschitzWeight x := by
  have hsource :=
    xiShiftedNondegenerateNullFlagCompletedArithmeticSource_liftedNull_eq_two_mul_firstOddDefect
      hw (n := n) (m := m) hn c hlast hzero B
  dsimp only at hsource ⊢
  unfold xiShiftedAdaptiveMixedOddContactFrontierPrice
  dsimp only
  rw [hsource]
  ring

/-- Nonzero first odd arithmetic contact gives a strictly positive source-carried curvature
price.  Positivity includes the actual global integral Lipschitz denominator. -/
theorem xiShiftedAdaptiveMixedOddContactFrontierPrice_pos
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ j < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c j = 0)
    (hfirst : xiShiftedHankelBoundaryPadeDefect (w ^ 2) c
      (2 * n + (2 * m + 1)) ≠ 0)
    (B : Polynomial ℝ) :
    0 < xiShiftedAdaptiveMixedOddContactFrontierPrice w n m c B := by
  let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment (w ^ 2) j).re
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let U := P * X ^ m
  let V := P * X ^ (m + 1)
  let δ := xiShiftedHankelBoundaryPadeDefect (w ^ 2) c
    (2 * n + (2 * m + 1))
  let a := HTGeometry.momentInner s V V
  let A := xiShiftedAdaptiveNullPairPolynomial (w ^ 2) U V
  let x := Polynomial.toFn (n + m + 2) A
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hU : U.natDegree < n + m + 2 := by
    dsimp only [U]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m), hPdeg,
      Polynomial.natDegree_X_pow]
    omega
  have hV : V.natDegree < n + m + 2 := by
    dsimp only [V]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow (m + 1)), hPdeg,
      Polynomial.natDegree_X_pow]
    omega
  have hUU : HTGeometry.momentInner s U U = 0 := by
    simpa only [s, U, P] using
      (momentInner_liftedNullPair_eq_zero_of_odd_contact
        c hlast hzero (i := m) (j := m) (by omega))
  have hUVeq : HTGeometry.momentInner s U V = δ := by
    simpa only [s, U, V, P, δ] using
      (momentInner_liftedNullPair_eq_first_odd_defect
        c hlast hzero (i := m) (j := m + 1) (by omega))
  have hUV : HTGeometry.momentInner s U V ≠ 0 := by
    rw [hUVeq]
    exact hfirst
  have hAdeg : A.natDegree < n + m + 2 :=
    natDegree_xiShiftedAdaptiveNullPairPolynomial_lt hU hV
  have hneg : xiShiftedMomentHankelQuadratic (w ^ 2) (n + m + 2) x < 0 := by
    rw [xiShiftedMomentHankelQuadratic_toFn_eq_momentInner hAdeg]
    exact momentInner_xiShiftedAdaptiveNullPairPolynomial_self_neg U V hUU hUV
  have hw0 : 0 < w := by linarith
  have hweight : 0 < xiShiftedMomentHankelQuadraticLipschitzWeight x :=
    xiShiftedMomentHankelQuadraticLipschitzWeight_pos_of_neg
      (sq_pos_of_pos hw0) x hneg
  have hδ : 0 < δ ^ 2 := sq_pos_of_ne_zero (by simpa only [δ] using hfirst)
  have hfactor : 0 < 2 * (|a| + 1) - a := by
    linarith [le_abs_self a, abs_nonneg a]
  have hden : 0 < (|a| + 1) ^ 2 := sq_pos_of_pos (by positivity)
  rw [xiShiftedAdaptiveMixedOddContactFrontierPrice_eq_firstOddDefect
    hw hn c hlast hzero B]
  exact div_pos (div_pos (mul_pos hδ hfactor) hden) hweight

/-- Literal source-carried curvature price is paid by the same finite-degree terminal frontier. -/
theorem add_xiShiftedAdaptiveMixedOddContactFrontierPrice_le_terminalFrontier
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ j < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c j = 0)
    (hfirst : xiShiftedHankelBoundaryPadeDefect (w ^ 2) c
      (2 * n + (2 * m + 1)) ≠ 0)
    (B : Polynomial ℝ) :
    w ^ 2 + xiShiftedAdaptiveMixedOddContactFrontierPrice w n m c B ≤
      xiShiftedHigherBlockTerminalFrontier (n + m) := by
  have hw0 : 0 < w := by linarith
  rw [xiShiftedAdaptiveMixedOddContactFrontierPrice_eq_firstOddDefect
    hw hn c hlast hzero B]
  exact
    add_firstOddPadeDefectAdaptiveEnergy_div_lipschitzWeight_le_terminalFrontier_sharp
      (y := w ^ 2) (sq_pos_of_pos hw0) c hlast hzero hfirst

/-- **Closed source-first odd-contact certificate.**  Completed adaptive `P^sharp` source creates
a strictly positive, exactly priced terminal-frontier displacement before reflection aggregation. -/
theorem xiShiftedAdaptiveMixedOddContactFrontierPrice_pos_and_le_terminalFrontier
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ j < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ 2) c j = 0)
    (hfirst : xiShiftedHankelBoundaryPadeDefect (w ^ 2) c
      (2 * n + (2 * m + 1)) ≠ 0)
    (B : Polynomial ℝ) :
    0 < xiShiftedAdaptiveMixedOddContactFrontierPrice w n m c B ∧
      w ^ 2 + xiShiftedAdaptiveMixedOddContactFrontierPrice w n m c B ≤
        xiShiftedHigherBlockTerminalFrontier (n + m) := by
  exact ⟨xiShiftedAdaptiveMixedOddContactFrontierPrice_pos
      hw hn c hlast hzero hfirst B,
    add_xiShiftedAdaptiveMixedOddContactFrontierPrice_le_terminalFrontier
      hw hn c hlast hzero hfirst B⟩

end

end RHTower
