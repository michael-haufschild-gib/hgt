import GaloisForLFunctions.RHTower.CCM.CCMActualHeadWallGramLightConeCovariantTransmutation
import GaloisForLFunctions.HTGeometry.PSDMatrixSpectralHankel

/-!
# Matched phase disk and Schur completion of the actual CCM cell

The mass-matched cosine and sine profiles are not unrelated scalar errors.  They are the entries
of an integrated positive-semidefinite `2 × 2` Gram density.  Its trace is exactly twice the
critical Mellin atom, so the oriented profile lies in the closed disk

`(C_n(xi) - w_n)^(2 : ℕ) + S_n(xi)^(2 : ℕ) <= w_n^(2 : ℕ)`.

Rotating this Gram matrix by the literal prime phase and taking its half-angle diagonal produces a
pointwise nonnegative completion of the intact prime-minus-polar cell.  The required reserve is
not an abstract majorant: on every actual head it is exactly

`4 w_n ||f||^(2 : ℕ) - w_n E_f(log n)`.

Thus the reflection-even covariant current from the preceding module has a coefficient-faithful
Schur diagonal.  This is an unconditional local completion; global completed-source transport of
its non-summable reserve remains the next obstruction.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

noncomputable section
namespace RHTower

def ccmActualHeadMatchedPhaseGramKernel (n : ℕ) (xi r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let A := Real.exp (Real.log n / 2)
  let theta := 2 * Real.pi * r * xi
  !![2 * A * Real.cosh (r / 2) * (1 - Real.cos theta),
      2 * A * Real.sinh (r / 2) * Real.sin theta;
     2 * A * Real.sinh (r / 2) * Real.sin theta,
      2 * A * Real.cosh (r / 2) * (1 + Real.cos theta)]

theorem ccmActualHeadMatchedPhaseGramKernel_posSemidef (n : ℕ) (xi r : ℝ) :
    (ccmActualHeadMatchedPhaseGramKernel n xi r).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian.ext_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ccmActualHeadMatchedPhaseGramKernel]
  · intro x
    let A := Real.exp (Real.log n / 2)
    let c := Real.cos (2 * Real.pi * r * xi)
    let s := Real.sin (2 * Real.pi * r * xi)
    let ch := Real.cosh (r / 2)
    let sh := Real.sinh (r / 2)
    let a := 2 * A * ch * (1 - c)
    let b := 2 * A * sh * s
    let d := 2 * A * ch * (1 + c)
    have hA : 0 < A := Real.exp_pos _
    have hc : -1 ≤ c := Real.neg_one_le_cos _
    have hc' : c ≤ 1 := Real.cos_le_one _
    have hch : 0 < ch := Real.cosh_pos _
    have ha : 0 ≤ a := by
      dsimp only [a]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA.le) hch.le)
        (sub_nonneg.mpr hc')
    have hd : 0 ≤ d := by
      dsimp only [d]
      have hsum : 0 ≤ 1 + c := by linarith
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA.le) hch.le)
        hsum
    have hdet : 0 ≤ a * d - b ^ (2 : ℕ) := by
      dsimp only [a, b, d, A, c, s, ch, sh]
      have htrig := Real.cos_sq_add_sin_sq (2 * Real.pi * r * xi)
      have hhyp := Real.cosh_sq_sub_sinh_sq (r / 2)
      calc
        _ = (2 * Real.exp (Real.log n / 2)) ^ (2 : ℕ) *
              (Real.cosh (r / 2) ^ (2 : ℕ) *
                  (1 - Real.cos (2 * Real.pi * r * xi) ^ (2 : ℕ)) -
                Real.sinh (r / 2) ^ (2 : ℕ) *
                  Real.sin (2 * Real.pi * r * xi) ^ (2 : ℕ)) := by ring
        _ = (2 * Real.exp (Real.log n / 2)) ^ (2 : ℕ) *
              Real.sin (2 * Real.pi * r * xi) ^ (2 : ℕ) *
                (Real.cosh (r / 2) ^ (2 : ℕ) - Real.sinh (r / 2) ^ (2 : ℕ)) := by
              have hsc : 1 - Real.cos (2 * Real.pi * r * xi) ^ (2 : ℕ) =
                  Real.sin (2 * Real.pi * r * xi) ^ (2 : ℕ) := by nlinarith
              rw [hsc]
              ring
        _ = (2 * Real.exp (Real.log n / 2) *
              Real.sin (2 * Real.pi * r * xi)) ^ (2 : ℕ) := by rw [hhyp]; ring
        _ ≥ 0 := sq_nonneg _
    have hq : 0 ≤ a * x 0 ^ (2 : ℕ) + 2 * b * x 0 * x 1 + d * x 1 ^ (2 : ℕ) := by
      rcases ha.eq_or_lt with ha0 | ha0
      · have hb0 : b = 0 := by
          rw [← sq_eq_zero_iff]
          nlinarith
        rw [ha0, hb0]
        nlinarith [mul_nonneg hd (sq_nonneg (x 1))]
      · have hscaled : 0 ≤ a *
            (a * x 0 ^ (2 : ℕ) + 2 * b * x 0 * x 1 + d * x 1 ^ (2 : ℕ)) := by
          nlinarith [sq_nonneg (a * x 0 + b * x 1),
            mul_nonneg hdet (sq_nonneg (x 1))]
        exact (mul_nonneg_iff_of_pos_left ha0).mp hscaled
    simp [ccmActualHeadMatchedPhaseGramKernel, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    dsimp only [a, b, d, A, c, s, ch, sh] at hq
    nlinarith

def ccmActualHeadMatchedComplementaryCosinePhaseProfile (n : ℕ) (xi : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
    2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
      (1 + Real.cos (2 * Real.pi * r * xi))

def ccmActualHeadMatchedPhaseGramMatrix (n : ℕ) (xi : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ccmActualHeadMatchedCosinePhaseProfile n xi,
      ccmActualHeadMatchedSinePhaseProfile n xi;
     ccmActualHeadMatchedSinePhaseProfile n xi,
      ccmActualHeadMatchedComplementaryCosinePhaseProfile n xi]

theorem integral_ccmActualHeadMatchedPhaseGramAnchor (n : ℕ) :
    (∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
      2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2)) =
        criticalMellinAtomWeight n := by
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  let C : ℝ := 2 * Real.exp (Real.log n / 2)
  let P : ℝ → ℝ := fun r => C * (2 * Real.sinh (r / 2))
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) rho,
      HasDerivAt P (2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2)) r := by
    intro r hr
    have hbase0 := (((Real.hasDerivAt_sinh (r / 2)).comp r
      ((hasDerivAt_id r).div_const 2)).const_mul 2)
    have hbase : HasDerivAt (fun x : ℝ => 2 * Real.sinh (x / 2))
        (Real.cosh (r / 2)) r := hbase0.congr_deriv (by ring)
    change HasDerivAt (fun x : ℝ => C * (2 * Real.sinh (x / 2))) _ r
    apply (hbase.const_mul C).congr_deriv
    dsimp only [C]
  have hint : IntervalIntegrable
      (fun r : ℝ => 2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2))
      volume 0 rho :=
    (by fun_prop : Continuous fun r : ℝ =>
      2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [P, C]
  simp only [zero_div, Real.sinh_zero, mul_zero, sub_zero]
  unfold rho ccmActualHeadMatchedPrimePolarRadius
  rw [show (2 * Real.arsinh
      (criticalMellinAtomWeight n / (4 * Real.exp (Real.log n / 2)))) / 2 =
      Real.arsinh
        (criticalMellinAtomWeight n / (4 * Real.exp (Real.log n / 2))) by ring,
    Real.sinh_arsinh]
  field_simp [Real.exp_ne_zero]
  ring

theorem ccmActualHeadMatchedPhaseProfiles_add_complement_eq_two_weight (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedCosinePhaseProfile n xi +
      ccmActualHeadMatchedComplementaryCosinePhaseProfile n xi = 2 * criticalMellinAtomWeight n := by
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  have hC : IntervalIntegrable (fun r : ℝ =>
      Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        (2 - 2 * Real.cos (2 * Real.pi * r * xi))) volume 0 rho :=
    (by fun_prop : Continuous fun r : ℝ =>
      Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        (2 - 2 * Real.cos (2 * Real.pi * r * xi))).intervalIntegrable _ _
  have hD : IntervalIntegrable (fun r : ℝ =>
      2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        (1 + Real.cos (2 * Real.pi * r * xi))) volume 0 rho :=
    (by fun_prop : Continuous fun r : ℝ =>
      2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        (1 + Real.cos (2 * Real.pi * r * xi))).intervalIntegrable _ _
  unfold ccmActualHeadMatchedCosinePhaseProfile ccmActualHeadMatchedComplementaryCosinePhaseProfile
  change (∫ r in (0 : ℝ)..rho, _) + (∫ r in (0 : ℝ)..rho, _) = _
  rw [← intervalIntegral.integral_add hC hD]
  calc
    (∫ r in (0 : ℝ)..rho,
      Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
          (2 - 2 * Real.cos (2 * Real.pi * r * xi)) +
        2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
          (1 + Real.cos (2 * Real.pi * r * xi))) =
        ∫ r in (0 : ℝ)..rho,
          2 * (2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2)) := by
            apply intervalIntegral.integral_congr
            intro r hr
            ring
    _ = 2 * (∫ r in (0 : ℝ)..rho,
          2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2)) := by
            rw [intervalIntegral.integral_const_mul]
    _ = 2 * criticalMellinAtomWeight n := by rw [integral_ccmActualHeadMatchedPhaseGramAnchor]

theorem ccmActualHeadMatchedPhaseGramMatrix_eq_integral (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseGramMatrix n xi =
      HTGeometry.integralMatrixKernel
        (volume.restrict (Ioc (0 : ℝ) (ccmActualHeadMatchedPrimePolarRadius n)))
        (ccmActualHeadMatchedPhaseGramKernel n xi) := by
  have hrho := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [ccmActualHeadMatchedPhaseGramMatrix, HTGeometry.integralMatrixKernel]
    unfold ccmActualHeadMatchedCosinePhaseProfile
    rw [intervalIntegral.integral_of_le hrho]
    apply integral_congr_ae
    filter_upwards with r
    simp [ccmActualHeadMatchedPhaseGramKernel]
    ring
  · simp only [ccmActualHeadMatchedPhaseGramMatrix, HTGeometry.integralMatrixKernel]
    unfold ccmActualHeadMatchedSinePhaseProfile
    rw [intervalIntegral.integral_of_le hrho]
    rfl
  · simp only [ccmActualHeadMatchedPhaseGramMatrix, HTGeometry.integralMatrixKernel]
    unfold ccmActualHeadMatchedSinePhaseProfile
    rw [intervalIntegral.integral_of_le hrho]
    rfl
  · simp only [ccmActualHeadMatchedPhaseGramMatrix, HTGeometry.integralMatrixKernel]
    unfold ccmActualHeadMatchedComplementaryCosinePhaseProfile
    rw [intervalIntegral.integral_of_le hrho]
    rfl

theorem ccmActualHeadMatchedPhaseGramMatrix_posSemidef (n : ℕ) (xi : ℝ) :
    (ccmActualHeadMatchedPhaseGramMatrix n xi).PosSemidef := by
  rw [ccmActualHeadMatchedPhaseGramMatrix_eq_integral]
  apply HTGeometry.integralMatrixKernel_posSemidef
  · intro i j
    apply Continuous.integrableOn_Ioc
    fin_cases i <;> fin_cases j <;> simp [ccmActualHeadMatchedPhaseGramKernel] <;> fun_prop
  · exact fun r => ccmActualHeadMatchedPhaseGramKernel_posSemidef n xi r

/-- Schur determinant inequality coupling the odd sine current to both even phase slacks. -/
theorem ccmActualHeadMatchedSinePhaseProfile_sq_le_cosine_mul_complement
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedSinePhaseProfile n xi ^ (2 : ℕ) ≤
      ccmActualHeadMatchedCosinePhaseProfile n xi *
        ccmActualHeadMatchedComplementaryCosinePhaseProfile n xi := by
  have hdet := (ccmActualHeadMatchedPhaseGramMatrix_posSemidef n xi).det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp [ccmActualHeadMatchedPhaseGramMatrix] at hdet
  nlinarith

/-- Exact closed-disk support of the two-channel matched phase profile. -/
theorem ccmActualHeadMatchedPhaseProfile_mem_weightDisk (n : ℕ) (xi : ℝ) :
    (ccmActualHeadMatchedCosinePhaseProfile n xi -
        criticalMellinAtomWeight n) ^ (2 : ℕ) +
      ccmActualHeadMatchedSinePhaseProfile n xi ^ (2 : ℕ) ≤
        criticalMellinAtomWeight n ^ (2 : ℕ) := by
  have hdet :=
    ccmActualHeadMatchedSinePhaseProfile_sq_le_cosine_mul_complement n xi
  have hsum := ccmActualHeadMatchedPhaseProfiles_add_complement_eq_two_weight n xi
  have hcomplement : ccmActualHeadMatchedComplementaryCosinePhaseProfile n xi =
      2 * criticalMellinAtomWeight n -
        ccmActualHeadMatchedCosinePhaseProfile n xi := by linarith
  rw [hcomplement] at hdet
  nlinarith

def ccmActualHeadMatchedPhaseSchurCompletionProfile (n : ℕ) (xi : ℝ) : ℝ :=
  criticalMellinAtomWeight n *
      (1 + Real.cos (2 * Real.pi * Real.log n * xi)) -
    (Real.cos (2 * Real.pi * Real.log n * xi) *
        ccmActualHeadMatchedCosinePhaseProfile n xi +
      Real.sin (2 * Real.pi * Real.log n * xi) *
        ccmActualHeadMatchedSinePhaseProfile n xi)

theorem ccmActualHeadMatchedPhaseSchurCompletionProfile_nonneg (n : ℕ) (xi : ℝ) :
    0 ≤ ccmActualHeadMatchedPhaseSchurCompletionProfile n xi := by
  let theta := 2 * Real.pi * Real.log n * xi
  let v : Fin 2 → ℝ :=
    ![Real.sin (theta / 2), -Real.cos (theta / 2)]
  have hq := (ccmActualHeadMatchedPhaseGramMatrix_posSemidef n xi).dotProduct_mulVec_nonneg v
  simp [ccmActualHeadMatchedPhaseGramMatrix, v, dotProduct, Matrix.mulVec, Fin.sum_univ_two] at hq
  have hsum := ccmActualHeadMatchedPhaseProfiles_add_complement_eq_two_weight n xi
  have hcomplement : ccmActualHeadMatchedComplementaryCosinePhaseProfile n xi =
      2 * criticalMellinAtomWeight n -
        ccmActualHeadMatchedCosinePhaseProfile n xi := by linarith
  rw [hcomplement] at hq
  have htrig := Real.sin_sq_add_cos_sq (theta / 2)
  have hsin := Real.sin_two_mul (theta / 2)
  have hcos := Real.cos_two_mul (theta / 2)
  have htheta : 2 * (theta / 2) = theta := by ring
  rw [htheta] at hsin hcos
  unfold ccmActualHeadMatchedPhaseSchurCompletionProfile
  change 0 ≤ criticalMellinAtomWeight n * (1 + Real.cos theta) -
    (Real.cos theta * ccmActualHeadMatchedCosinePhaseProfile n xi +
      Real.sin theta * ccmActualHeadMatchedSinePhaseProfile n xi)
  have heq :
      criticalMellinAtomWeight n * (1 + Real.cos theta) -
          (Real.cos theta * ccmActualHeadMatchedCosinePhaseProfile n xi +
            Real.sin theta * ccmActualHeadMatchedSinePhaseProfile n xi) =
        Real.sin (theta / 2) *
            (ccmActualHeadMatchedCosinePhaseProfile n xi * Real.sin (theta / 2) -
              ccmActualHeadMatchedSinePhaseProfile n xi * Real.cos (theta / 2)) -
          Real.cos (theta / 2) *
            (ccmActualHeadMatchedSinePhaseProfile n xi * Real.sin (theta / 2) -
              (2 * criticalMellinAtomWeight n -
                ccmActualHeadMatchedCosinePhaseProfile n xi) * Real.cos (theta / 2)) := by
    rw [hsin, hcos]
    linear_combination -ccmActualHeadMatchedCosinePhaseProfile n xi * htrig
  rw [heq]
  exact sub_nonneg.mpr hq

theorem integrable_ccmActualHeadMatchedPhaseReserveProfile_mul_density
    (n : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      criticalMellinAtomWeight n *
          (1 + Real.cos (2 * Real.pi * Real.log n * xi)) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by
  let D : ℝ → ℝ := fun xi => ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)
  let B : ℝ → ℝ := fun xi =>
    criticalMellinAtomWeight n *
      (1 + Real.cos (2 * Real.pi * Real.log n * xi))
  have hD : Integrable D := integrable_norm_sq (fourierUnitary f)
  have hB : StronglyMeasurable B := (by fun_prop : Continuous B).stronglyMeasurable
  have hbound : ∀ xi, ‖B xi‖ ≤ 2 * criticalMellinAtomWeight n := by
    intro xi
    have hw := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
    have hc0 : 0 ≤ 1 + Real.cos (2 * Real.pi * Real.log n * xi) := by
      nlinarith [Real.neg_one_le_cos (2 * Real.pi * Real.log n * xi)]
    have hc2 : 1 + Real.cos (2 * Real.pi * Real.log n * xi) ≤ 2 := by
      nlinarith [Real.cos_le_one (2 * Real.pi * Real.log n * xi)]
    dsimp only [B]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw hc0)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc2 hw
  have hDB : Integrable (fun xi => D xi * B xi) :=
    Integrable.mul_bdd (c := 2 * criticalMellinAtomWeight n) hD
      hB.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  exact hDB.congr (ae_of_all volume fun xi => by dsimp only [D, B]; ring)

def ccmActualHeadMatchedPhaseSchurReserveProducer (n : ℕ) (f : SoninL2) : ℝ :=
  2 * ∫ xi : ℝ,
    criticalMellinAtomWeight n *
        (1 + Real.cos (2 * Real.pi * Real.log n * xi)) *
      ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)

def ccmActualHeadMatchedPhaseSchurCompletionEnergy (n : ℕ) (f : SoninL2) : ℝ :=
  2 * ∫ xi : ℝ,
    ccmActualHeadMatchedPhaseSchurCompletionProfile n xi *
      ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)

theorem ccmActualHeadMatchedPhaseSchurCompletionEnergy_nonneg (n : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadMatchedPhaseSchurCompletionEnergy n f := by
  unfold ccmActualHeadMatchedPhaseSchurCompletionEnergy
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro xi
  exact mul_nonneg (ccmActualHeadMatchedPhaseSchurCompletionProfile_nonneg n xi) (sq_nonneg _)

theorem ccmActualHeadMatchedPhaseSchurReserveProducer_eq_chordComplement
    (n : ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPhaseSchurReserveProducer n f =
      4 * criticalMellinAtomWeight n * ‖f‖ ^ (2 : ℕ) -
        criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f := by
  let D : ℝ → ℝ := fun xi => ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)
  let Q : ℝ → ℝ := fun xi =>
    (2 - 2 * Real.cos (2 * Real.pi * Real.log n * xi)) * D xi
  have hD : Integrable D := integrable_norm_sq (fourierUnitary f)
  have hQ : Integrable Q := by
    have hcoeff : StronglyMeasurable (fun xi : ℝ =>
        2 - 2 * Real.cos (2 * Real.pi * Real.log n * xi)) :=
      (by fun_prop : Continuous fun xi : ℝ =>
        2 - 2 * Real.cos (2 * Real.pi * Real.log n * xi)).stronglyMeasurable
    have hbound : ∀ᵐ xi : ℝ, ‖2 - 2 * Real.cos
        (2 * Real.pi * Real.log n * xi)‖ ≤ 4 := by
      filter_upwards with xi
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · nlinarith [Real.cos_le_one (2 * Real.pi * Real.log n * xi),
          Real.neg_one_le_cos (2 * Real.pi * Real.log n * xi)]
      · nlinarith [Real.cos_le_one (2 * Real.pi * Real.log n * xi)]
    have h := Integrable.mul_bdd (c := 4) hD hcoeff.aestronglyMeasurable hbound
    exact h.congr (ae_of_all volume fun xi => by dsimp only [D, Q]; ring)
  have hnorm : ‖f‖ ^ (2 : ℕ) = ∫ xi : ℝ, D xi := by
    rw [← fourierUnitary.norm_map]
    exact norm_sq_eq_integral (fourierUnitary f)
  have hdef : ccmActualHeadTranslationDefect (Real.log n) f =
      ∫ xi : ℝ, Q xi := by
    have h := ccmActualHeadTranslationDefect_fourierUnitary_symm
      (Real.log n) (fourierUnitary f)
    rw [fourierUnitary.symm_apply_apply] at h
    simpa only [Q, D] using h
  rw [hnorm, hdef]
  unfold ccmActualHeadMatchedPhaseSchurReserveProducer
  calc
    2 * ∫ xi : ℝ,
        criticalMellinAtomWeight n *
            (1 + Real.cos (2 * Real.pi * Real.log n * xi)) * D xi =
      ∫ xi : ℝ,
        2 * (criticalMellinAtomWeight n *
            (1 + Real.cos (2 * Real.pi * Real.log n * xi)) * D xi) := by
          rw [integral_const_mul]
    _ = ∫ xi : ℝ,
        (4 * criticalMellinAtomWeight n) * D xi -
          criticalMellinAtomWeight n * Q xi := by
      apply integral_congr_ae
      filter_upwards with xi
      dsimp only [Q]
      ring
    _ = (∫ xi : ℝ, (4 * criticalMellinAtomWeight n) * D xi) -
        ∫ xi : ℝ, criticalMellinAtomWeight n * Q xi := by
      rw [integral_sub (hD.const_mul _) (hQ.const_mul _)]
    _ = 4 * criticalMellinAtomWeight n * (∫ xi : ℝ, D xi) -
        criticalMellinAtomWeight n * (∫ xi : ℝ, Q xi) := by
      rw [integral_const_mul, integral_const_mul]

theorem ccmActualHeadPrimePolarCell_add_phaseSchurReserve_eq_completion (n : ℕ) (f : SoninL2) :
    criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f +
      ccmActualHeadMatchedPhaseSchurReserveProducer n f = ccmActualHeadMatchedPhaseSchurCompletionEnergy n f := by
  rw [ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_orientedPhase]
  unfold ccmActualHeadMatchedPhaseSchurReserveProducer ccmActualHeadMatchedPhaseSchurCompletionEnergy ccmActualHeadMatchedPhaseSchurCompletionProfile
  simp_rw [ccmActualHeadMatchedOrientedPhaseSymbol_re]
  have hreserve := integrable_ccmActualHeadMatchedPhaseReserveProfile_mul_density n f
  have horiented :=
    integrable_ccmActualHeadMatchedOrientedPhaseSymbol_re_mul_density n f
  have horiented' : Integrable (fun xi : ℝ =>
      (Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi +
        Real.sin (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedSinePhaseProfile n xi) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by
    simpa only [ccmActualHeadMatchedOrientedPhaseSymbol_re] using horiented
  calc
    (-2 * ∫ xi : ℝ,
          (Real.cos (2 * Real.pi * Real.log n * xi) *
              ccmActualHeadMatchedCosinePhaseProfile n xi +
            Real.sin (2 * Real.pi * Real.log n * xi) *
              ccmActualHeadMatchedSinePhaseProfile n xi) *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) +
        2 * ∫ xi : ℝ,
          criticalMellinAtomWeight n *
              (1 + Real.cos (2 * Real.pi * Real.log n * xi)) *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) =
      2 * ((∫ xi : ℝ,
          criticalMellinAtomWeight n *
              (1 + Real.cos (2 * Real.pi * Real.log n * xi)) *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) -
        ∫ xi : ℝ,
          (Real.cos (2 * Real.pi * Real.log n * xi) *
              ccmActualHeadMatchedCosinePhaseProfile n xi +
            Real.sin (2 * Real.pi * Real.log n * xi) *
              ccmActualHeadMatchedSinePhaseProfile n xi) *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by ring
    _ = 2 * ∫ xi : ℝ,
        (criticalMellinAtomWeight n *
              (1 + Real.cos (2 * Real.pi * Real.log n * xi)) *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) -
          (Real.cos (2 * Real.pi * Real.log n * xi) *
              ccmActualHeadMatchedCosinePhaseProfile n xi +
            Real.sin (2 * Real.pi * Real.log n * xi) *
              ccmActualHeadMatchedSinePhaseProfile n xi) *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by
      rw [integral_sub hreserve horiented']
    _ = 2 * ∫ xi : ℝ,
        (criticalMellinAtomWeight n *
              (1 + Real.cos (2 * Real.pi * Real.log n * xi)) -
          (Real.cos (2 * Real.pi * Real.log n * xi) *
              ccmActualHeadMatchedCosinePhaseProfile n xi +
            Real.sin (2 * Real.pi * Real.log n * xi) *
              ccmActualHeadMatchedSinePhaseProfile n xi)) *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with xi
      ring

theorem ccmActualHeadPrimePolarCell_add_phaseSchurReserve_nonneg (n : ℕ) (f : SoninL2) :
    0 ≤ criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f +
      ccmActualHeadMatchedPhaseSchurReserveProducer n f := by
  rw [ccmActualHeadPrimePolarCell_add_phaseSchurReserve_eq_completion]
  exact ccmActualHeadMatchedPhaseSchurCompletionEnergy_nonneg n f

end RHTower
