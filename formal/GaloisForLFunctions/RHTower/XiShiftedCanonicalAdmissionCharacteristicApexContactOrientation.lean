import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexChristoffelEnergy

/-!
# Oriented characteristic-apex contacts

The pure top-edge Christoffel law reduces Route U to the normalized adjacent-degree apex product.
This module determines its exact first-order behavior at every positive-degree apex contact.  If
`A_n(y) = 0`, finite-block no-common-root gives `A_{n+1}(y) ≠ 0`, while characteristic transport
gives `A_n'(y) = -2n A_{n+1}(y)`.  Consequently

`d/dy [A_{n+1} A_n / N_n] = -2n A_{n+1}² / N_n < 0`.

The same cancellation in projective coordinates is amplitude- and norm-free:

`d/dy [A_n / A_{n+1}] = -2n`.

Thus every positive-degree characteristic contact has one universal projective orientation.  The
source-native parabolic versions below discharge finite Hankel positivity from the shifted-Xi
degree horizon.
-/

open Complex Matrix Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Norm-normalized product on the top degree edge `n ↔ n+1`. -/
def xiShiftedCanonicalAdmissionApexNormalizedTopProduct (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionApexValue y (n + 1) *
    xiShiftedCanonicalAdmissionApexValue y n /
      xiShiftedCanonicalAdmissionNorm y n

/-- Projective coordinate whose zeros are degree-`n` contacts away from the adjacent-degree poles. -/
def xiShiftedCanonicalAdmissionApexProjectiveTopRatio (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionApexValue y n /
    xiShiftedCanonicalAdmissionApexValue y (n + 1)

/-- At a degree-`n` contact, the actual canonical degree-`n+1` apex value is nonzero.  This upgrades
finite monic-orthogonal no-common-root to the moving canonical admissions at both degrees. -/
theorem xiShiftedCanonicalAdmissionApexValue_succ_ne_zero_of_contact
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y n = 0) :
    xiShiftedCanonicalAdmissionApexValue y (n + 1) ≠ 0 := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hHn : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hHnext : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) ((n + 1) + 2)).PosDef := by
    simpa only [Nat.add_assoc] using hH
  have hNextEq :
      (HTGeometry.monicOrtho s (n + 1)).eval y⁻¹ =
        xiShiftedCanonicalAdmissionApexValue y (n + 1) := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHnext]
  have htrans := xiShiftedCanonicalAdmissionApexValue_contact_transverse
    hy hn hHn hcontact
  simp only [s] at hNextEq
  rw [hNextEq] at htrans
  intro hzero
  apply htrans.2
  rw [hzero, mul_zero]

/-- Exact derivative of the normalized top product at a positive-degree characteristic contact. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexNormalizedTopProduct_contact
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y n = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexNormalizedTopProduct v n)
      (-2 * (n : ℝ) * xiShiftedCanonicalAdmissionApexValue y (n + 1) ^ (2 : ℕ) /
        xiShiftedCanonicalAdmissionNorm y n) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hHn : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hHnext : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) ((n + 1) + 2)).PosDef := by
    simpa only [Nat.add_assoc] using hH
  have hNextEq :
      (HTGeometry.monicOrtho s (n + 1)).eval y⁻¹ =
        xiShiftedCanonicalAdmissionApexValue y (n + 1) := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHnext]
  have hAn := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_contact
    hy hn hHn hcontact
  simp only [s] at hNextEq
  rw [hNextEq] at hAn
  have hAnext := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_raw
    (n := n + 1) hy hH
  have hNorm := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_jacobiFlow
    hy hn hHn
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hHn
  have hNormEq : xiShiftedCanonicalAdmissionNorm y n =
      HTGeometry.monicOrthoNormSq s n := by
    simpa only [s] using xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hHn
  have hNormPos : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    rw [hNormEq]
    exact HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hQuot := (hAnext.mul hAn).div hNorm hNormPos.ne'
  refine hQuot.congr_deriv ?_
  simp only [Pi.mul_apply, hcontact, mul_zero, zero_mul, sub_zero]
  field_simp [hNormPos.ne']
  ring

/-- The normalized top product crosses downward at every positive-degree contact. -/
theorem xiShiftedCanonicalAdmissionApexNormalizedTopProduct_contact_derivative_neg
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y n = 0) :
    -2 * (n : ℝ) * xiShiftedCanonicalAdmissionApexValue y (n + 1) ^ (2 : ℕ) /
        xiShiftedCanonicalAdmissionNorm y n < 0 := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hHn : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hNextNe := xiShiftedCanonicalAdmissionApexValue_succ_ne_zero_of_contact
    hy hn hH hcontact
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hHn
  have hNormEq : xiShiftedCanonicalAdmissionNorm y n =
      HTGeometry.monicOrthoNormSq s n := by
    simpa only [s] using xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hHn
  have hNormPos : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    rw [hNormEq]
    exact HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsq : 0 < xiShiftedCanonicalAdmissionApexValue y (n + 1) ^ (2 : ℕ) :=
    sq_pos_of_ne_zero hNextNe
  have hneg : -2 * (n : ℝ) < 0 := by nlinarith
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hsq) hNormPos

/-- Closed finite-chamber contact orientation: exact derivative and its strict sign. -/
theorem xiShiftedCanonicalAdmissionApexNormalizedTopProduct_contact_oriented
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y n = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexNormalizedTopProduct v n)
        (-2 * (n : ℝ) * xiShiftedCanonicalAdmissionApexValue y (n + 1) ^ (2 : ℕ) /
          xiShiftedCanonicalAdmissionNorm y n) y ∧
      -2 * (n : ℝ) * xiShiftedCanonicalAdmissionApexValue y (n + 1) ^ (2 : ℕ) /
          xiShiftedCanonicalAdmissionNorm y n < 0 := by
  exact ⟨hasDerivAt_xiShiftedCanonicalAdmissionApexNormalizedTopProduct_contact
      hy hn hH hcontact,
    xiShiftedCanonicalAdmissionApexNormalizedTopProduct_contact_derivative_neg
      hy hn hH hcontact⟩

/-- Universal projective contact law.  Both norm and adjacent-degree amplitude cancel. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_contact
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y n = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexProjectiveTopRatio v n)
      (-2 * (n : ℝ)) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hHn : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hHnext : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) ((n + 1) + 2)).PosDef := by
    simpa only [Nat.add_assoc] using hH
  have hNextEq :
      (HTGeometry.monicOrtho s (n + 1)).eval y⁻¹ =
        xiShiftedCanonicalAdmissionApexValue y (n + 1) := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHnext]
  have hAn := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_contact
    hy hn hHn hcontact
  simp only [s] at hNextEq
  rw [hNextEq] at hAn
  have hAnext := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_raw
    (n := n + 1) hy hH
  have hNextNe := xiShiftedCanonicalAdmissionApexValue_succ_ne_zero_of_contact
    hy hn hH hcontact
  have hQuot := hAn.div hAnext hNextNe
  refine hQuot.congr_deriv ?_
  simp only [hcontact, zero_mul, sub_zero]
  field_simp [hNextNe]

/-- Source-native parabolic contact orientation.  The degree horizon supplies the whole
`n+3` moment block needed to differentiate both adjacent canonical admissions. -/
theorem xiShiftedCanonicalAdmissionApexNormalizedTopProduct_contact_oriented_of_parabolicDegreeHorizon
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hy : routeUParabolicDegreeHorizon * (((n + 3 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ y)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y n = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexNormalizedTopProduct v n)
        (-2 * (n : ℝ) * xiShiftedCanonicalAdmissionApexValue y (n + 1) ^ (2 : ℕ) /
          xiShiftedCanonicalAdmissionNorm y n) y ∧
      -2 * (n : ℝ) * xiShiftedCanonicalAdmissionApexValue y (n + 1) ^ (2 : ℕ) /
          xiShiftedCanonicalAdmissionNorm y n < 0 := by
  have hy0 : 0 < y := lt_of_lt_of_le
    (mul_pos routeUParabolicDegreeHorizon_pos (sq_pos_of_pos (by positivity))) hy
  have hy' : routeUParabolicDegreeHorizon *
      ((((n + 1) + 2 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ y := by
    simpa only [Nat.add_assoc] using hy
  have hH' := xiShiftedMomentHankelMatrix_posDef_of_parabolicDegreeHorizon (n + 1) hy'
  have hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) ((n + 1) + 2)).PosDef at hH'
    simpa only [Nat.add_assoc] using hH'
  exact xiShiftedCanonicalAdmissionApexNormalizedTopProduct_contact_oriented
    hy0 hn hH hcontact

/-- Source-native universal projective slope at a positive-degree characteristic contact. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_contact_of_parabolicDegreeHorizon
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hy : routeUParabolicDegreeHorizon * (((n + 3 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ y)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y n = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexProjectiveTopRatio v n)
      (-2 * (n : ℝ)) y := by
  have hy0 : 0 < y := lt_of_lt_of_le
    (mul_pos routeUParabolicDegreeHorizon_pos (sq_pos_of_pos (by positivity))) hy
  have hy' : routeUParabolicDegreeHorizon *
      ((((n + 1) + 2 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ y := by
    simpa only [Nat.add_assoc] using hy
  have hH' := xiShiftedMomentHankelMatrix_posDef_of_parabolicDegreeHorizon (n + 1) hy'
  have hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) ((n + 1) + 2)).PosDef at hH'
    simpa only [Nat.add_assoc] using hH'
  exact hasDerivAt_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_contact
    hy0 hn hH hcontact

end

end RHTower
