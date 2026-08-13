import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexTransport

/-!
# Finite characteristic-apex energy and exact degree-boundary flux

The moving-apex transport is triangular in admission degree, but an unweighted square sum does not
expose its global conservation law.  Dividing the degree-`n` apex square by `n` times the canonical
orthogonal norm makes every interior adjacent-degree coupling telescope.  The resulting finite
energy has exactly one bottom flux, one top flux, and an explicit Jacobi-diagonal bulk term.
-/

open Complex Matrix Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Degree-`n` moving-apex energy shell.  The global energy below only uses positive `n`. -/
def xiShiftedCanonicalAdmissionApexEnergyShell (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionApexValue y n ^ 2 /
    ((n : ℝ) * xiShiftedCanonicalAdmissionNorm y n)

/-- Flux through the degree edge `n ↔ n+1`. -/
def xiShiftedCanonicalAdmissionApexDegreeFlux (y : ℝ) (n : ℕ) : ℝ :=
  2 * xiShiftedCanonicalAdmissionApexValue y (n + 1) *
      xiShiftedCanonicalAdmissionApexValue y n /
    xiShiftedCanonicalAdmissionNorm y n

/-- Literal Jacobi-diagonal production in the degree-`n` energy shell. -/
def xiShiftedCanonicalAdmissionApexBulkProduction (y : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.monicOrthoAlpha
      (fun k => (xiShiftedReciprocalMoment y k).re) n *
    xiShiftedCanonicalAdmissionApexEnergyShell y n

/-- Finite characteristic-apex energy through positive degrees `1,...,N`. -/
def xiShiftedCanonicalAdmissionApexEnergy (y : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N,
    xiShiftedCanonicalAdmissionApexEnergyShell y (i + 1)

/-- Averaging the backward and forward characteristic laws removes the moving-apex drift and
puts adjacent degrees in skew Jacobi form. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_skewJacobiTransport
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexValue v n)
      ((HTGeometry.monicOrthoFirstCoeff
          (fun k => (xiShiftedReciprocalMoment y k).re) n -
        (n : ℝ) * HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) n) *
          xiShiftedCanonicalAdmissionApexValue y n +
        (n : ℝ) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
          xiShiftedCanonicalAdmissionApexValue y (n - 1) -
        (n : ℝ) * xiShiftedCanonicalAdmissionApexValue y (n + 1)) y := by
  have hprev := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_prev hy hn hH
  have hnext := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_next hy hn hH
  have hHprev : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n - 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hHnext : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hPprev :
      (HTGeometry.monicOrtho
        (fun k => (xiShiftedReciprocalMoment y k).re) (n - 1)).eval y⁻¹ =
        xiShiftedCanonicalAdmissionApexValue y (n - 1) := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef hHprev]
  have hPnext :
      (HTGeometry.monicOrtho
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).eval y⁻¹ =
        xiShiftedCanonicalAdmissionApexValue y (n + 1) := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef hHnext]
  rw [hPprev] at hprev
  rw [hPnext] at hnext
  have heq := hprev.unique hnext
  refine hprev.congr_deriv ?_
  linear_combination (heq) / 2

/-- Every energy shell is nonnegative on its finite positive Hankel chamber. -/
theorem xiShiftedCanonicalAdmissionApexEnergyShell_nonneg
    {y : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 ≤ xiShiftedCanonicalAdmissionApexEnergyShell y n := by
  have hnorm : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
  exact div_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hnorm.le)

/-- The finite characteristic-apex energy is nonnegative on the common positive block. -/
theorem xiShiftedCanonicalAdmissionApexEnergy_nonneg
    {y : ℝ} (N : ℕ)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef) :
    0 ≤ xiShiftedCanonicalAdmissionApexEnergy y N := by
  rw [xiShiftedCanonicalAdmissionApexEnergy]
  apply Finset.sum_nonneg
  intro i hi
  exact xiShiftedCanonicalAdmissionApexEnergyShell_nonneg
    (xiShiftedMomentHankel_posDef_of_le
      (by have := Finset.mem_range.mp hi; omega) hH)

/-- **Local continuity equation in admission degree.**  Norm flow cancels the subleading
coefficient, the Jacobi norm ratio converts the backward edge to the preceding degree flux, and
the only remaining bulk term is the literal diagonal Jacobi coordinate. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexEnergyShell
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexEnergyShell v n)
      (xiShiftedCanonicalAdmissionApexBulkProduction y n +
        xiShiftedCanonicalAdmissionApexDegreeFlux y (n - 1) -
        xiShiftedCanonicalAdmissionApexDegreeFlux y n) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hA :=
    hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_skewJacobiTransport hy hn hH
  have hN := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_jacobiFlow hy hn hH
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hHprev : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) ((n - 1) + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hNormEq : xiShiftedCanonicalAdmissionNorm y n =
      HTGeometry.monicOrthoNormSq s n := by
    simpa only [s] using xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH
  have hNormPrevEq : xiShiftedCanonicalAdmissionNorm y (n - 1) =
      HTGeometry.monicOrthoNormSq s (n - 1) := by
    simpa only [s] using xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hHprev
  have hNormPos : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    rw [hNormEq]
    exact HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hNormPrevPos : 0 < xiShiftedCanonicalAdmissionNorm y (n - 1) := by
    rw [hNormPrevEq]
    exact HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hBeta := HTGeometry.monicOrthoNormSq_mul_nextBeta hbelow
    (n := n - 1) (by omega)
  have hBetaNorm :
      xiShiftedCanonicalAdmissionNorm y (n - 1) *
          HTGeometry.monicOrthoBeta s n =
        xiShiftedCanonicalAdmissionNorm y n := by
    rw [hNormEq, hNormPrevEq]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hBeta
  rw [← hNormEq] at hN
  have hDen := hN.const_mul (n : ℝ)
  have hSq := hA.pow 2
  have hQuot := hSq.div hDen
    (mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn)) hNormPos.ne')
  refine hQuot.congr_deriv ?_
  simp only [xiShiftedCanonicalAdmissionApexEnergyShell,
    xiShiftedCanonicalAdmissionApexBulkProduction,
    xiShiftedCanonicalAdmissionApexDegreeFlux,
    Nat.sub_add_cancel (by omega : 1 ≤ n)]
  simp only [s] at hBetaNorm
  field_simp [hNormPos.ne', hNormPrevPos.ne',
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]
  simp only [Pi.pow_apply]
  push_cast
  linear_combination (2 * (n : ℝ) * xiShiftedCanonicalAdmissionApexValue y n *
    xiShiftedCanonicalAdmissionApexValue y (n - 1)) * hBetaNorm

private theorem sum_range_degreeFlux_sub_succ (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (f i - f (i + 1))) = f 0 - f N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- **Exact finite characteristic-apex energy balance.**  Every interior degree flux cancels.
The derivative consists only of Jacobi-diagonal bulk production, bottom injection, and top escape.
This is the finite global budget absent from the individual contact laws. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexEnergy
    {y : ℝ} (hy : 0 < y) (N : ℕ)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexEnergy v N)
      ((∑ i ∈ Finset.range N,
          xiShiftedCanonicalAdmissionApexBulkProduction y (i + 1)) +
        xiShiftedCanonicalAdmissionApexDegreeFlux y 0 -
        xiShiftedCanonicalAdmissionApexDegreeFlux y N) y := by
  have hsum : HasDerivAt (fun v =>
      ∑ i ∈ Finset.range N,
        xiShiftedCanonicalAdmissionApexEnergyShell v (i + 1))
      (∑ i ∈ Finset.range N,
        (xiShiftedCanonicalAdmissionApexBulkProduction y (i + 1) +
          xiShiftedCanonicalAdmissionApexDegreeFlux y i -
          xiShiftedCanonicalAdmissionApexDegreeFlux y (i + 1))) y := by
    apply HasDerivAt.fun_sum
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    have hHi : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) ((i + 1) + 2)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hH
    have hshell := hasDerivAt_xiShiftedCanonicalAdmissionApexEnergyShell
      hy (n := i + 1) (by omega) hHi
    simpa only [Nat.add_sub_cancel] using hshell
  refine hsum.congr_deriv ?_
  rw [show (∑ i ∈ Finset.range N,
        (xiShiftedCanonicalAdmissionApexBulkProduction y (i + 1) +
          xiShiftedCanonicalAdmissionApexDegreeFlux y i -
          xiShiftedCanonicalAdmissionApexDegreeFlux y (i + 1))) =
      (∑ i ∈ Finset.range N,
        xiShiftedCanonicalAdmissionApexBulkProduction y (i + 1)) +
      ∑ i ∈ Finset.range N,
        (xiShiftedCanonicalAdmissionApexDegreeFlux y i -
          xiShiftedCanonicalAdmissionApexDegreeFlux y (i + 1)) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring]
  rw [sum_range_degreeFlux_sub_succ]
  ring

end

end RHTower
