import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexEnergy

/-!
# Radial Christoffel energy at the shifted-Xi characteristic apex

The degree-weighted apex energy leaves a Jacobi-diagonal bulk term and two boundary fluxes.
That bulk is not intrinsic.  For the unweighted norm-normalized shells, the three-term recurrence
splits the Jacobi diagonal into two half-edge currents.  Degree zero supplies exactly the missing
negative half-current.  Consequently every bulk and lower-boundary contribution cancels in the
full Christoffel sum.

After the radial normalization by `y`, the derivative is a single top-edge observable:

`d/dy [(1/y) ∑_{n=0}^N A_n(y)^(2 : ℕ) / N_n(y)]
  = -((N+1/2)/y) F_N(y)`.

The sum is proved equal to the diagonal finite Christoffel--Darboux kernel.  Thus the remaining
Route-U orientation problem is localized exactly to the sign of one adjacent-degree apex product;
no hidden bulk production or bottom injection survives.
-/

open Complex Matrix Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Norm-normalized degree shell of the moving characteristic apex. -/
def xiShiftedCanonicalAdmissionApexChristoffelShell (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionApexValue y n ^ (2 : ℕ) /
    xiShiftedCanonicalAdmissionNorm y n

/-- Full finite diagonal Christoffel energy through degree `N`, including degree zero. -/
def xiShiftedCanonicalAdmissionApexChristoffelEnergy (y : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    xiShiftedCanonicalAdmissionApexChristoffelShell y n

/-- Radially normalized finite Christoffel energy. -/
def xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy (y : ℝ) (N : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionApexChristoffelEnergy y N / y

/-- Before using the three-term recurrence, a positive-degree unweighted shell has Jacobi bulk
plus degree-weighted incoming and outgoing edge currents. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexChristoffelShell_eq_rawJacobiBalance
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexChristoffelShell v n)
      (HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
          xiShiftedCanonicalAdmissionApexChristoffelShell y n +
        (n : ℝ) * xiShiftedCanonicalAdmissionApexDegreeFlux y (n - 1) -
        (n : ℝ) * xiShiftedCanonicalAdmissionApexDegreeFlux y n) y := by
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
  have hSq := hA.pow 2
  have hQuot := hSq.div hN hNormPos.ne'
  refine hQuot.congr_deriv ?_
  simp only [xiShiftedCanonicalAdmissionApexChristoffelShell,
    xiShiftedCanonicalAdmissionApexDegreeFlux]
  simp only [s] at hBetaNorm
  simp only [Pi.pow_apply, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  field_simp [hNormPos.ne', hNormPrevPos.ne']
  push_cast
  linear_combination
    (2 * (n : ℝ) * xiShiftedCanonicalAdmissionApexValue y n *
      xiShiftedCanonicalAdmissionApexValue y (n - 1)) * hBetaNorm

/-- The finite Jacobi recurrence converts the diagonal shell term into radial transport minus one
half of each adjacent edge flux. -/
theorem xiShiftedCanonicalAdmissionApexAlpha_mul_christoffelShell_eq_radial_sub_halfFluxes
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
        xiShiftedCanonicalAdmissionApexChristoffelShell y n =
      y⁻¹ * xiShiftedCanonicalAdmissionApexChristoffelShell y n -
        (1 / 2) * xiShiftedCanonicalAdmissionApexDegreeFlux y (n - 1) -
        (1 / 2) * xiShiftedCanonicalAdmissionApexDegreeFlux y n := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hHprev : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) ((n - 1) + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hHprevPoly : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n - 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hHcurPoly : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hHnextPoly : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).PosDef :=
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
  have hPrev : (HTGeometry.monicOrtho s (n - 1)).eval y⁻¹ =
      xiShiftedCanonicalAdmissionApexValue y (n - 1) := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef hHprevPoly]
  have hCur : (HTGeometry.monicOrtho s n).eval y⁻¹ =
      xiShiftedCanonicalAdmissionApexValue y n := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef hHcurPoly]
  have hNext : (HTGeometry.monicOrtho s (n + 1)).eval y⁻¹ =
      xiShiftedCanonicalAdmissionApexValue y (n + 1) := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef hHnextPoly]
  have hRecPoly := HTGeometry.X_mul_monicOrtho_below hbelow
    (n := n) (by omega : n + 1 ≤ n + 2)
  have hRec := congrArg (Polynomial.eval y⁻¹) hRecPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul] at hRec
  rw [hPrev, hCur, hNext] at hRec
  field_simp [hy.ne'] at hRec
  simp only [xiShiftedCanonicalAdmissionApexChristoffelShell,
    xiShiftedCanonicalAdmissionApexDegreeFlux]
  simp only [s] at hBetaNorm hRec
  simp only [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  field_simp [hy.ne', hNormPos.ne', hNormPrevPos.ne']
  linear_combination
    -(xiShiftedCanonicalAdmissionNorm y (n - 1) *
      xiShiftedCanonicalAdmissionApexValue y n) * hRec -
    (y * xiShiftedCanonicalAdmissionApexValue y n *
      xiShiftedCanonicalAdmissionApexValue y (n - 1)) * hBetaNorm

/-- Positive-degree local continuity equation after the Jacobi bulk has been absorbed into half-edge
currents. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexChristoffelShell_of_pos
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexChristoffelShell v n)
      (y⁻¹ * xiShiftedCanonicalAdmissionApexChristoffelShell y n +
        ((n : ℝ) - 1 / 2) * xiShiftedCanonicalAdmissionApexDegreeFlux y (n - 1) -
        ((n : ℝ) + 1 / 2) * xiShiftedCanonicalAdmissionApexDegreeFlux y n) y := by
  have hRaw :=
    hasDerivAt_xiShiftedCanonicalAdmissionApexChristoffelShell_eq_rawJacobiBalance
      hy hn hH
  have hCharacteristic :=
    xiShiftedCanonicalAdmissionApexAlpha_mul_christoffelShell_eq_radial_sub_halfFluxes
      hy hn hH
  refine hRaw.congr_deriv ?_
  rw [hCharacteristic]
  ring

/-- Degree zero supplies exactly the negative half-current needed to close the lower boundary. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexChristoffelShell_zero
    {y : ℝ} (hy : 0 < y)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) 2).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexChristoffelShell v 0)
      (y⁻¹ * xiShiftedCanonicalAdmissionApexChristoffelShell y 0 -
        (1 / 2) * xiShiftedCanonicalAdmissionApexDegreeFlux y 0) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hA0 (v : ℝ) : xiShiftedCanonicalAdmissionApexValue v 0 = 1 := by
    simp [xiShiftedCanonicalAdmissionApexValue,
      HTGeometry.monicMomentAdmissionPolynomial_eq]
  have hN0 (v : ℝ) : xiShiftedCanonicalAdmissionNorm v 0 =
      (xiShiftedReciprocalMoment v 0).re := by
    simp [xiShiftedCanonicalAdmissionNorm,
      HTGeometry.monicMomentAdmissionPolynomial_eq,
      HTGeometry.momentInner_def, HTGeometry.momentFunctional_one_eq]
  have hNormEq : xiShiftedCanonicalAdmissionNorm y 0 =
      HTGeometry.monicOrthoNormSq s 0 := by
    simpa only [s] using xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH
  have hNormPos : 0 < xiShiftedCanonicalAdmissionNorm y 0 := by
    rw [hNormEq]
    exact HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hs0 : s 0 ≠ 0 := by
    have h := hNormPos.ne'
    rw [hNormEq] at h
    simpa [HTGeometry.monicOrthoNormSq, HTGeometry.monicOrtho_zero,
      HTGeometry.momentInner_def, HTGeometry.momentFunctional_one_eq] using h
  have hAder : HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionApexValue v 0) 0 y := by
    rw [show (fun v => xiShiftedCanonicalAdmissionApexValue v 0) =
        (fun _ : ℝ => 1) by funext v; exact hA0 v]
    exact hasDerivAt_const y 1
  have hMoment := hasDerivAt_re_xiShiftedReciprocalMoment hy 0
  simp only [Nat.cast_zero, zero_add, neg_mul, one_mul] at hMoment
  have hNder : HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionNorm v 0)
      (-(xiShiftedReciprocalMoment y 1).re) y := by
    convert hMoment using 1
    funext v
    exact hN0 v
  have hAlphaNorm :
      HTGeometry.monicOrthoAlpha s 0 *
          xiShiftedCanonicalAdmissionNorm y 0 =
        (xiShiftedReciprocalMoment y 1).re := by
    rw [hNormEq]
    simp only [HTGeometry.monicOrthoAlpha, HTGeometry.monicOrthoNormSq,
      HTGeometry.monicOrtho_zero, HTGeometry.momentInner_def, one_mul]
    simp only [mul_one]
    rw [← pow_one Polynomial.X, HTGeometry.momentFunctional_X_pow,
      HTGeometry.momentFunctional_one_eq]
    exact div_mul_cancel₀ _ hs0
  have hSq := hAder.pow 2
  have hQuot := hSq.div hNder hNormPos.ne'
  have hRaw : HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionApexChristoffelShell v 0)
      (HTGeometry.monicOrthoAlpha s 0 *
        xiShiftedCanonicalAdmissionApexChristoffelShell y 0) y := by
    refine hQuot.congr_deriv ?_
    simp only [xiShiftedCanonicalAdmissionApexChristoffelShell,
      Pi.pow_apply, hA0, one_pow, Nat.cast_ofNat, zero_mul, mul_zero, zero_sub]
    field_simp [hNormPos.ne']
    nlinarith [hAlphaNorm]
  have hHone : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) 1).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hNext : (HTGeometry.monicOrtho s 1).eval y⁻¹ =
      xiShiftedCanonicalAdmissionApexValue y 1 := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho_of_hankelPosDef hHone]
  have hRecPoly := HTGeometry.X_mul_monicOrtho_below hbelow
    (n := 0) (by omega : 0 + 1 ≤ 2)
  simp only [Nat.zero_add, Nat.zero_sub] at hRecPoly
  have hRec := congrArg (Polynomial.eval y⁻¹) hRecPoly
  simp only [Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul,
    HTGeometry.monicOrtho_zero, Polynomial.eval_one, mul_one,
    HTGeometry.monicOrthoBeta, add_zero] at hRec
  simp only [s] at hNext hRec
  rw [hNext] at hRec
  have hCharacteristic :
      HTGeometry.monicOrthoAlpha s 0 *
          xiShiftedCanonicalAdmissionApexChristoffelShell y 0 =
        y⁻¹ * xiShiftedCanonicalAdmissionApexChristoffelShell y 0 -
          (1 / 2) * xiShiftedCanonicalAdmissionApexDegreeFlux y 0 := by
    simp only [xiShiftedCanonicalAdmissionApexChristoffelShell,
      xiShiftedCanonicalAdmissionApexDegreeFlux, hA0, one_pow, mul_one]
    field_simp [hy.ne', hNormPos.ne'] at hRec ⊢
    linear_combination -hRec
  refine hRaw.congr_deriv ?_
  exact hCharacteristic

private theorem sum_range_christoffelFlux_sub_succ (g : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (g i - g (i + 1))) = g 0 - g N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem sum_range_halfWeightedApexFlux_sub_succ (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (
      (((i + 1 : ℕ) : ℝ) - 1 / 2) * f i -
        (((i + 1 : ℕ) : ℝ) + 1 / 2) * f (i + 1))) =
      (1 / 2) * f 0 - ((N : ℝ) + 1 / 2) * f N := by
  have hcoeff (i : ℕ) :
      (((i + 1 : ℕ) : ℝ) - 1 / 2) = (i : ℝ) + 1 / 2 := by
    push_cast
    ring
  simp_rw [hcoeff]
  simpa only [Nat.cast_zero, zero_add] using
    sum_range_christoffelFlux_sub_succ
      (fun i => ((i : ℝ) + 1 / 2) * f i) N

/-- **Pure top-boundary Christoffel balance.**  Summing from degree zero through `N` cancels every
interior edge, while the degree-zero half-current cancels the lower edge exactly. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexChristoffelEnergy
    {y : ℝ} (hy : 0 < y) (N : ℕ)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexChristoffelEnergy v N)
      (y⁻¹ * xiShiftedCanonicalAdmissionApexChristoffelEnergy y N -
        ((N : ℝ) + 1 / 2) *
          xiShiftedCanonicalAdmissionApexDegreeFlux y N) y := by
  have hH0 : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) 2).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hZero :=
    hasDerivAt_xiShiftedCanonicalAdmissionApexChristoffelShell_zero hy hH0
  have hPositive : HasDerivAt (fun v =>
      ∑ i ∈ Finset.range N,
        xiShiftedCanonicalAdmissionApexChristoffelShell v (i + 1))
      (∑ i ∈ Finset.range N,
        (y⁻¹ * xiShiftedCanonicalAdmissionApexChristoffelShell y (i + 1) +
          (((i + 1 : ℕ) : ℝ) - 1 / 2) *
            xiShiftedCanonicalAdmissionApexDegreeFlux y i -
          (((i + 1 : ℕ) : ℝ) + 1 / 2) *
            xiShiftedCanonicalAdmissionApexDegreeFlux y (i + 1))) y := by
    apply HasDerivAt.fun_sum
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    have hHi : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) ((i + 1) + 2)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hH
    exact hasDerivAt_xiShiftedCanonicalAdmissionApexChristoffelShell_of_pos
      hy (by omega) hHi
  have hTotal := hPositive.add hZero
  rw [show (fun v => xiShiftedCanonicalAdmissionApexChristoffelEnergy v N) =
      (fun v =>
        (∑ i ∈ Finset.range N,
          xiShiftedCanonicalAdmissionApexChristoffelShell v (i + 1)) +
        xiShiftedCanonicalAdmissionApexChristoffelShell v 0) by
      funext v
      rw [xiShiftedCanonicalAdmissionApexChristoffelEnergy,
        Finset.sum_range_succ']]
  refine hTotal.congr_deriv ?_
  rw [show (∑ i ∈ Finset.range N,
        (y⁻¹ * xiShiftedCanonicalAdmissionApexChristoffelShell y (i + 1) +
          (((i + 1 : ℕ) : ℝ) - 1 / 2) *
            xiShiftedCanonicalAdmissionApexDegreeFlux y i -
          (((i + 1 : ℕ) : ℝ) + 1 / 2) *
            xiShiftedCanonicalAdmissionApexDegreeFlux y (i + 1))) =
      y⁻¹ * (∑ i ∈ Finset.range N,
        xiShiftedCanonicalAdmissionApexChristoffelShell y (i + 1)) +
        ∑ i ∈ Finset.range N,
          ((((i + 1 : ℕ) : ℝ) - 1 / 2) *
              xiShiftedCanonicalAdmissionApexDegreeFlux y i -
            (((i + 1 : ℕ) : ℝ) + 1 / 2) *
              xiShiftedCanonicalAdmissionApexDegreeFlux y (i + 1)) by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring]
  have hFlux := sum_range_halfWeightedApexFlux_sub_succ
    (fun n => xiShiftedCanonicalAdmissionApexDegreeFlux y n) N
  rw [hFlux]
  simp only [xiShiftedCanonicalAdmissionApexChristoffelEnergy,
    Finset.sum_range_succ']
  ring

/-- **Radial pure-boundary law.**  Dividing by `y` cancels the remaining homogeneous radial bulk;
only the top degree edge survives. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy
    {y : ℝ} (hy : 0 < y) (N : ℕ)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy v N)
      (-(((N : ℝ) + 1 / 2) / y) *
        xiShiftedCanonicalAdmissionApexDegreeFlux y N) y := by
  have hEnergy :=
    hasDerivAt_xiShiftedCanonicalAdmissionApexChristoffelEnergy hy N hH
  have hQuot := hEnergy.div (hasDerivAt_id y) hy.ne'
  refine hQuot.congr_deriv ?_
  simp only [id_eq]
  field_simp [hy.ne']
  ring

/-- The radial derivative written as its single adjacent-degree top product. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy_eq_topProduct
    {y : ℝ} (hy : 0 < y) (N : ℕ)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy v N)
      (-(((2 * N + 1 : ℕ) : ℝ) / y) *
        (xiShiftedCanonicalAdmissionApexValue y (N + 1) *
          xiShiftedCanonicalAdmissionApexValue y N /
          xiShiftedCanonicalAdmissionNorm y N)) y := by
  have h :=
    hasDerivAt_xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy hy N hH
  refine h.congr_deriv ?_
  simp only [xiShiftedCanonicalAdmissionApexDegreeFlux]
  push_cast
  ring

/-- The finite apex energy is literally the diagonal Christoffel--Darboux kernel at `X=1/y`. -/
theorem xiShiftedCanonicalAdmissionApexChristoffelEnergy_eq_cdKernel
    {y : ℝ} (N : ℕ)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef) :
    xiShiftedCanonicalAdmissionApexChristoffelEnergy y N =
      (HTGeometry.cdKernel
        (fun k => (xiShiftedReciprocalMoment y k).re) N y⁻¹).eval y⁻¹ := by
  rw [xiShiftedCanonicalAdmissionApexChristoffelEnergy,
    HTGeometry.cdKernel_eval_self]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k < N + 1 := Finset.mem_range.mp hk
  have hHk : (HTGeometry.momentHankelMatrix
      (fun j => (xiShiftedReciprocalMoment y j).re) (k + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hA : xiShiftedCanonicalAdmissionApexValue y k =
      (HTGeometry.monicOrtho
        (fun j => (xiShiftedReciprocalMoment y j).re) k).eval y⁻¹ := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHk]
  have hNorm := xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hHk
  rw [xiShiftedCanonicalAdmissionApexChristoffelShell, hA, hNorm,
    HTGeometry.monicOrthoNormSq]

/-- Strict positivity of the finite apex Christoffel energy on its finite Hankel chamber. -/
theorem xiShiftedCanonicalAdmissionApexChristoffelEnergy_pos
    {y : ℝ} (N : ℕ)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionApexChristoffelEnergy y N := by
  rw [xiShiftedCanonicalAdmissionApexChristoffelEnergy_eq_cdKernel N hH]
  exact HTGeometry.cdKernel_eval_self_pos_below
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) N (by omega) y⁻¹

/-- At a degree-`N` characteristic contact, the entire radial Christoffel energy is stationary.
The vanishing is global in degree but follows from the pure top-edge law. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy_eq_zero_of_contact
    {y : ℝ} (hy : 0 < y) (N : ℕ)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y N = 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy v N) 0 y := by
  have h :=
    hasDerivAt_xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy_eq_topProduct hy N hH
  simpa only [hcontact, mul_zero, zero_div, mul_zero, neg_zero] using h

/-- **Source-native parabolic radial law.**  The shifted-Xi degree horizon supplies the finite
positive chamber, leaving no Hankel-positivity premise. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy_of_parabolicDegreeHorizon
    {y : ℝ} (N : ℕ)
    (hy : routeUParabolicDegreeHorizon * (((N + 2 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ y) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy v N)
      (-(((N : ℝ) + 1 / 2) / y) *
        xiShiftedCanonicalAdmissionApexDegreeFlux y N) y := by
  have hy0 : 0 < y := lt_of_lt_of_le
    (mul_pos routeUParabolicDegreeHorizon_pos (sq_pos_of_pos (by positivity))) hy
  have hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef := by
    have hH' := xiShiftedMomentHankelMatrix_posDef_of_parabolicDegreeHorizon N hy
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef at hH'
    exact hH'
  exact hasDerivAt_xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy hy0 N hH

/-- Source-native parabolic law in the explicit adjacent-degree top-product form. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy_eq_topProduct_of_parabolicDegreeHorizon
    {y : ℝ} (N : ℕ)
    (hy : routeUParabolicDegreeHorizon * (((N + 2 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ y) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy v N)
      (-(((2 * N + 1 : ℕ) : ℝ) / y) *
        (xiShiftedCanonicalAdmissionApexValue y (N + 1) *
          xiShiftedCanonicalAdmissionApexValue y N /
          xiShiftedCanonicalAdmissionNorm y N)) y := by
  have hy0 : 0 < y := lt_of_lt_of_le
    (mul_pos routeUParabolicDegreeHorizon_pos (sq_pos_of_pos (by positivity))) hy
  have hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef := by
    have hH' := xiShiftedMomentHankelMatrix_posDef_of_parabolicDegreeHorizon N hy
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (N + 2)).PosDef at hH'
    exact hH'
  exact
    hasDerivAt_xiShiftedCanonicalAdmissionApexRadialChristoffelEnergy_eq_topProduct
      hy0 N hH

end

end RHTower
