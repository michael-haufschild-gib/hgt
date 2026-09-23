import GaloisForLFunctions.RHTower.XiShiftedHalfDensityAdjacentConnection
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionSourceRecession
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionGaussRiccatiSource

/-!
# Recession connection for canonical shifted-Xi admission

The far-right recession admission and the actual inverse-Hankel moving admission are the same
flag in two coordinate gauges.  This module proves that identification exactly, transports the
coefficientwise arcsine recession back to actual mass, and combines it with the positive
half-density velocity to obtain a global terminal trace law.

For every fixed positive degree, the actual first subleading coefficient converges to zero.  On a
complete terminal positive chamber it is strictly increasing, hence it must remain strictly
negative throughout that chamber.  No fixed observation map or reflection aggregation occurs.
-/

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

theorem sourceCoordinateAdmission_monic
    {w : ℝ} (hw : w ≠ 0) {n : ℕ} (_hn : n ≠ 0) :
    (sourceCoordinateAdmission w n).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
  · rw [sourceCoordinateAdmission,
      Polynomial.natDegree_smul _ (inv_ne_zero (pow_ne_zero _ hw)),
      Polynomial.natDegree_comp,
      Polynomial.natDegree_C_mul_X (w ^ (2 : ℕ)) (pow_ne_zero _ hw),
      dimensionlessAdmission_natDegree, Nat.mul_one]
  · simp only [sourceCoordinateAdmission, Polynomial.coeff_smul,
      Polynomial.comp_C_mul_X_coeff]
    have htop : (dimensionlessAdmission w n).coeff n = 1 := by
      have hcoeff := (dimensionlessAdmission_monic w n).coeff_natDegree
      rw [dimensionlessAdmission_natDegree] at hcoeff
      exact hcoeff
    rw [htop]
    change (w ^ (2 * n))⁻¹ * (1 * (w ^ (2 : ℕ)) ^ n) = 1
    rw [one_mul, ← pow_mul]
    exact inv_mul_cancel₀ (pow_ne_zero _ hw)

theorem sourceCoordinateAdmission_natDegree
    {w : ℝ} (hw : w ≠ 0) {n : ℕ} (_hn : n ≠ 0) :
    (sourceCoordinateAdmission w n).natDegree = n := by
  rw [sourceCoordinateAdmission,
    Polynomial.natDegree_smul _ (inv_ne_zero (pow_ne_zero _ hw)),
    Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul_X (w ^ (2 : ℕ)) (pow_ne_zero _ hw),
    dimensionlessAdmission_natDegree, Nat.mul_one]

/-- Exact gauge equivalence between normalized recession admission and actual moving admission. -/
theorem sourceCoordinateAdmission_eq_actualAdmission
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hNdet : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) n).det ≠ 0)
    (hAdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n).det ≠ 0) :
    sourceCoordinateAdmission w n =
      HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  apply HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal hAdet
    (sourceCoordinateAdmission_monic hw0 (Nat.ne_of_gt hn))
    (sourceCoordinateAdmission_natDegree hw0 (Nat.ne_of_gt hn))
  intro i
  have hNzero :=
    HTGeometry.momentFunctional_X_pow_mul_monicMomentAdmissionPolynomial_eq_zero
      hNdet i
  change HTGeometry.momentFunctional (xiShiftedFarRightNormalizedMoment w)
      (X ^ (i : ℕ) * dimensionlessAdmission w n) = 0 at hNzero
  have hscale := momentFunctional_normalized_eq_massDilation hw
    (X ^ (i : ℕ) * dimensionlessAdmission w n)
  have hpoly :
      (X ^ (i : ℕ) * dimensionlessAdmission w n).comp
          (Polynomial.C (w ^ (2 : ℕ)) * X) =
        w ^ (2 * ((i : ℕ) + n)) •
          (X ^ (i : ℕ) * sourceCoordinateAdmission w n) := by
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]
    simp only [sourceCoordinateAdmission, Polynomial.smul_eq_C_mul]
    rw [mul_pow]
    have hiPow : (w ^ (2 : ℕ)) ^ (i : ℕ) = w ^ (2 * (i : ℕ)) := by
      rw [← pow_mul]
    have hCpow : (Polynomial.C (w ^ (2 : ℕ)) : Polynomial ℝ) ^ (i : ℕ) =
        Polynomial.C (w ^ (2 * (i : ℕ))) := by
      rw [← Polynomial.C_pow, hiPow]
    have hsum : 2 * ((i : ℕ) + n) = 2 * (i : ℕ) + 2 * n := by omega
    rw [hCpow, hsum, pow_add, Polynomial.C_mul]
    ring_nf
    have hcancelN : Polynomial.C (w ^ (n * 2)) *
        Polynomial.C (w⁻¹ ^ (n * 2)) = (1 : Polynomial ℝ) := by
      rw [← Polynomial.C_mul]
      rw [← mul_pow, mul_inv_cancel₀ hw0, one_pow]
      simp
    let A : Polynomial ℝ := Polynomial.C (w ^ ((i : ℕ) * 2)) * X ^ (i : ℕ) *
      (dimensionlessAdmission w n).comp (X * Polynomial.C (w ^ (2 : ℕ)))
    change A = A * Polynomial.C (w ^ (n * 2)) * Polynomial.C (w⁻¹ ^ (n * 2))
    symm
    calc
      A * Polynomial.C (w ^ (n * 2)) * Polynomial.C (w⁻¹ ^ (n * 2)) =
          A * (Polynomial.C (w ^ (n * 2)) * Polynomial.C (w⁻¹ ^ (n * 2))) := by ring
      _ = A := by rw [hcancelN, mul_one]
  rw [hpoly, HTGeometry.momentFunctional_smul] at hscale
  rw [hNzero] at hscale
  have hc : 2 * w / Real.log w ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) hw0)
      (ne_of_gt (Real.log_pos hw))
  have hp : w ^ (2 * ((i : ℕ) + n)) ≠ 0 := pow_ne_zero _ hw0
  apply (mul_eq_zero.mp ?_).resolve_left hp
  apply (mul_eq_zero.mp ?_).resolve_left hc
  simpa [mul_assoc] using hscale.symm

/-- The first subleading coefficient has coordinate weight minus two. -/
theorem sourceCoordinateAdmission_coeff_prev
    {w : ℝ} (hw : w ≠ 0) {n : ℕ} (hn : 0 < n) :
    (sourceCoordinateAdmission w n).coeff (n - 1) =
      (w ^ (2 : ℕ))⁻¹ * (dimensionlessAdmission w n).coeff (n - 1) := by
  simp only [sourceCoordinateAdmission, Polynomial.coeff_smul,
    Polynomial.comp_C_mul_X_coeff]
  have hsub : 2 * n = 2 * (n - 1) + 2 := by omega
  have hpow : (w ^ (2 : ℕ)) ^ (n - 1) = w ^ (2 * (n - 1)) := by
    rw [← pow_mul]
  rw [hpow, hsub, pow_add]
  have hz : w ^ (2 * (n - 1)) ≠ 0 := pow_ne_zero _ hw
  simp only [smul_eq_mul]
  field_simp [hw, hz]

/-- Recession and moving-connection gauges agree: every fixed canonical first coefficient
vanishes along the square-mass ray. -/
theorem tendsto_xiShiftedCanonicalAdmissionFirstCoeff_squareParam_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun w : ℝ => xiShiftedCanonicalAdmissionFirstCoeff (w ^ (2 : ℕ)) n)
      atTop (nhds 0) := by
  have hfactor : Tendsto (fun w : ℝ => (w ^ (2 : ℕ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega : 2 ≠ 0))
  have hcoeff := tendsto_dimensionlessAdmission_coeff
    (Nat.ne_of_gt hn) (n - 1)
  have hrhs : Tendsto
      (fun w : ℝ => (w ^ (2 : ℕ))⁻¹ * (dimensionlessAdmission w n).coeff (n - 1))
      atTop (nhds 0) := by
    simpa using hfactor.mul hcoeff
  apply hrhs.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually n,
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually n,
    eventually_gt_atTop (1 : ℝ)] with w hN hA hw
  have hNdet : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) n).det ≠ 0 := by
    exact ne_of_gt hN.det_pos
  have hAdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n).det ≠ 0 := by
    exact ne_of_gt hA.det_pos
  rw [xiShiftedCanonicalAdmissionFirstCoeff,
    ← sourceCoordinateAdmission_eq_actualAdmission hw hn hNdet hAdet,
    sourceCoordinateAdmission_coeff_prev (ne_of_gt (lt_trans zero_lt_one hw)) hn]

/-- The actual moving canonical first coefficient vanishes at infinite mass, without retaining
the square-root coordinate. -/
theorem tendsto_xiShiftedCanonicalAdmissionFirstCoeff_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun y : ℝ => xiShiftedCanonicalAdmissionFirstCoeff y n)
      atTop (nhds 0) := by
  have h := (tendsto_xiShiftedCanonicalAdmissionFirstCoeff_squareParam_zero hn).comp
    Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  simp only [Function.comp_apply]
  rw [Real.sq_sqrt hy]

set_option maxHeartbeats 2000000 in
/-- **Terminal trace law.** Every fixed positive degree has a complete terminal chamber on which
the canonical first coefficient is strictly negative and increases strictly to zero. -/
theorem exists_xiShiftedCanonicalAdmissionFirstCoeff_terminal_neg_increasing_to_zero
    {n : ℕ} (hn : 0 < n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y, A < y →
      xiShiftedCanonicalAdmissionFirstCoeff y n < 0 ∧
        0 < deriv (fun v => xiShiftedCanonicalAdmissionFirstCoeff v n) y := by
  obtain ⟨A, hA, hchamber⟩ := exists_xiShiftedCanonicalAdmissionTerminalChamber n
  let f : ℝ → ℝ := fun y => xiShiftedCanonicalAdmissionFirstCoeff y n
  have hcont : ContinuousOn f (Set.Ioi A) := by
    intro y hy
    have hy0 : 0 < y := lt_of_le_of_lt hA hy
    have hdet := xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef
      (hchamber y hy)
    exact (hasDerivAt_xiShiftedCanonicalAdmissionFirstCoeff hy0 hn hdet).continuousAt
      |>.continuousWithinAt
  have hmono : StrictMonoOn f (Set.Ioi A) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi A) hcont
    intro y hy
    rw [interior_Ioi] at hy
    exact deriv_xiShiftedCanonicalAdmissionFirstCoeff_pos
      (lt_of_le_of_lt hA hy) hn (hchamber y hy)
  have hlim : Tendsto f atTop (nhds 0) :=
    tendsto_xiShiftedCanonicalAdmissionFirstCoeff_zero hn
  refine ⟨A, hA, ?_⟩
  intro y hy
  have hderiv := deriv_xiShiftedCanonicalAdmissionFirstCoeff_pos
    (lt_of_le_of_lt hA hy) hn (hchamber y hy)
  refine ⟨?_, hderiv⟩
  change f y < 0
  by_contra hnot
  have hyNonneg : 0 ≤ f y := le_of_not_gt hnot
  let z : ℝ := y + 1
  have hyz : y < z := by dsimp only [z]; linarith
  have hzA : A < z := lt_trans hy hyz
  have hyzMono := hmono (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hzA) hyz
  have hzpos : 0 < f z := lt_of_le_of_lt hyNonneg hyzMono
  have hevent : ∀ᶠ t : ℝ in atTop, f t < f z :=
    hlim.eventually (isOpen_Iio.mem_nhds hzpos)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  let t : ℝ := max T (z + 1)
  have hTt : T ≤ t := le_max_left _ _
  have hzt : z < t := by
    exact lt_of_lt_of_le (lt_add_one z) (le_max_right _ _)
  have htA : A < t := lt_trans hzA hzt
  have hupper : f t < f z := hT t hTt
  have hlower : f z < f t :=
    hmono (Set.mem_Ioi.mpr hzA) (Set.mem_Ioi.mpr htA) hzt
  exact lt_asymm hupper hlower

end
end XiShiftedCanonicalAdmission
end RHTower
