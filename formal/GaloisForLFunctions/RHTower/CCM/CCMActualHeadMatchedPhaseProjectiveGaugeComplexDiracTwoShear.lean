import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseProjectiveGaugeNodalCenterCurvature

/-!
# Complex Dirac two-shear resolution of matched-source nodal crossings

The real nodal determinant sees only the real projection of the actual matched
oriented phase symbol.  This module retains its full complex orientation.

For every prime-power atom the complex symbol is nonzero away from the spectral
center.  A Hermitian Dirac block has the symbol as its exact nodal coordinate,
and two fixed Hermitian shears recover its real and imaginary components.  Their
joint crossing energy is therefore strictly positive off center and has center
as its unique zero.  The imaginary shear crosses that center transversely.

Finite prime-power packets retain this conclusion label by label.  No scalar
positivity or Riemann-hypothesis conclusion is asserted here: the remaining
problem is to transport this nowhere-zero oriented plane into the global scalar
receiver without destructive projection.
-/


open Complex MeasureTheory Set Filter Topology Matrix
open scoped BigOperators ComplexConjugate

noncomputable section
namespace RHTower

theorem ccmActualHeadMatchedCosinePhaseProfile_pos_of_weight_pos_of_ne_zero
    {n : ℕ} {xi : ℝ} (hn : 0 < criticalMellinAtomWeight n) (hxi : xi ≠ 0) :
    0 < ccmActualHeadMatchedCosinePhaseProfile n xi := by
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  have hrho : 0 < rho := ccmActualHeadMatchedPrimePolarRadius_pos_of_weight_pos hn
  have hxabs : 0 < |xi| := abs_pos.mpr hxi
  let r0 : ℝ := min (rho / 2) (1 / (4 * |xi|))
  have hr0 : 0 < r0 := by
    exact lt_min (half_pos hrho) (one_div_pos.mpr (mul_pos (by norm_num) hxabs))
  have hr0rho : r0 ≤ rho := by
    exact (min_le_left _ _).trans (half_le_self hrho.le)
  have hr0cap : r0 ≤ 1 / (4 * |xi|) := min_le_right _ _
  let theta : ℝ := 2 * Real.pi * r0 * xi
  have htheta_ne : theta ≠ 0 := by
    dsimp only [theta]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hr0.ne') hxi
  have habs_theta : |theta| ≤ Real.pi / 2 := by
    have hfac : 0 ≤ 2 * Real.pi * |xi| := by positivity
    calc
      |theta| = 2 * Real.pi * r0 * |xi| := by
        dsimp only [theta]
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos Real.pi_pos, abs_of_pos hr0]
      _ = (2 * Real.pi * |xi|) * r0 := by ring
      _ ≤ (2 * Real.pi * |xi|) * (1 / (4 * |xi|)) :=
        mul_le_mul_of_nonneg_left hr0cap hfac
      _ = Real.pi / 2 := by
        field_simp
        ring
  have htheta_lower : -(2 * Real.pi) < theta := by
    have hneg := neg_abs_le theta
    nlinarith [Real.pi_pos]
  have htheta_upper : theta < 2 * Real.pi := by
    have hle := le_abs_self theta
    nlinarith [Real.pi_pos]
  have hcosne : Real.cos theta ≠ 1 := by
    intro hcos
    have hzero :=
      (Real.cos_eq_one_iff_of_lt_of_lt htheta_lower htheta_upper).mp hcos
    exact htheta_ne hzero
  have hcoslt : Real.cos theta < 1 :=
    lt_of_le_of_ne (Real.cos_le_one theta) hcosne
  unfold ccmActualHeadMatchedCosinePhaseProfile
  apply intervalIntegral.integral_pos (a := (0 : ℝ)) (b := rho) hrho
  · fun_prop
  · intro r hr
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)
      (by nlinarith [Real.cos_le_one (2 * Real.pi * r * xi)])
  · refine ⟨r0, Set.mem_Icc.2 ⟨hr0.le, hr0rho⟩, ?_⟩
    dsimp only [theta] at hcoslt
    exact mul_pos
      (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
      (by nlinarith)

theorem ccmActualHeadMatchedOrientedPhaseProfile_ne_zero_of_weight_pos_of_ne_zero
    {n : ℕ} {xi : ℝ} (hn : 0 < criticalMellinAtomWeight n) (hxi : xi ≠ 0) :
    ccmActualHeadMatchedOrientedPhaseProfile n xi ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  have hpos := ccmActualHeadMatchedCosinePhaseProfile_pos_of_weight_pos_of_ne_zero hn hxi
  simp [ccmActualHeadMatchedOrientedPhaseProfile] at hre
  exact hpos.ne' hre

theorem ccmActualHeadMatchedOrientedPhaseSymbol_ne_zero_of_weight_pos_of_ne_zero
    {n : ℕ} {xi : ℝ} (hn : 0 < criticalMellinAtomWeight n) (hxi : xi ≠ 0) :
    ccmActualHeadMatchedOrientedPhaseSymbol n xi ≠ 0 := by
  unfold ccmActualHeadMatchedOrientedPhaseSymbol
  exact mul_ne_zero (Complex.exp_ne_zero _) <|
    ccmActualHeadMatchedOrientedPhaseProfile_ne_zero_of_weight_pos_of_ne_zero hn hxi

theorem ccmActualHeadMatchedOrientedPhaseSymbol_primePower_ne_zero_iff
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedOrientedPhaseSymbol
      (xiGammaEulerValuationNat (p, e)) xi ≠ 0 ↔ xi ≠ 0 := by
  constructor
  · intro hsymbol hxi
    subst xi
    exact hsymbol (ccmActualHeadMatchedOrientedPhaseSymbol_zero _)
  · intro hxi
    apply ccmActualHeadMatchedOrientedPhaseSymbol_ne_zero_of_weight_pos_of_ne_zero
      (xi := xi) _ hxi
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)

/-- Hermitian supersymmetric Dirac block carrying the full complex matched source coordinate. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac
    (xi : ℝ) (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let z := ccmActualHeadMatchedOrientedPhaseSymbol n xi
  !![0, 0, -star z; 0, 0, 1; -z, 1, 0]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac_isHermitian
    (xi : ℝ) (n : ℕ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac xi n).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac]

/-- Canonically normalized complex nodal vector. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalUnitVector
    (xi : ℝ) (n : ℕ) : Fin 3 → ℂ :=
  ![1, ccmActualHeadMatchedOrientedPhaseSymbol n xi, 0]

/-- Gauge-dressed complex nodal vector. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector
    (xi : ℝ) (n : ℕ) : Fin 3 → ℂ :=
  (ccmActualHeadMatchedPhaseProjectiveGauge n : ℂ) •
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalUnitVector xi n

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac_mulVec_unitNodal
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac xi n *ᵥ
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalUnitVector xi n = 0 := by
  ext i
  fin_cases i <;>
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalUnitVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac_mulVec_nodal
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac xi n *ᵥ
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector xi n = 0 := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector,
    Matrix.mulVec_smul,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac_mulVec_unitNodal]
  simp

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac_mulVec_eq_zero_iff
    (xi : ℝ) (n : ℕ) (v : Fin 3 → ℂ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac xi n *ᵥ v = 0 ↔
      v = v 0 • ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalUnitVector xi n := by
  constructor
  · intro hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    have h2 := congrFun hv 2
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
    have hv1 : v 1 = v 0 * ccmActualHeadMatchedOrientedPhaseSymbol n xi := by
      linear_combination h2
    ext i
    fin_cases i
    · simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalUnitVector]
    · simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalUnitVector, hv1]
    · simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalUnitVector, h1]
  · intro hv
    rw [hv, Matrix.mulVec_smul,
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac_mulVec_unitNodal]
    simp

/-- Real-coordinate Hermitian shear on the complex nodal line. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 0]

/-- Imaginary-coordinate Hermitian shear on the complex nodal line. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -I, 0; I, 0, 0; 0, 0, 0]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear_isHermitian :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear_isHermitian :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear]

def ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealCrossingForm
    (xi : ℝ) (n : ℕ) : ℝ :=
  (star (ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector xi n) ⬝ᵥ
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear *ᵥ
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector xi n)).re

def ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm
    (xi : ℝ) (n : ℕ) : ℝ :=
  (star (ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector xi n) ⬝ᵥ
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear *ᵥ
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector xi n)).re

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealCrossingForm_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealCrossingForm xi n =
      2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealCrossingForm,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalUnitVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.mul_re]
  ring

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm xi n =
      2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).im := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalUnitVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.mul_re]
  ring

/-- Two-parameter Hermitian shear plane through the complex Dirac wall. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceCrossingFamily
    (xi : ℝ) (n : ℕ) (t u : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac xi n +
    (t : ℂ) • ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear +
    (u : ℂ) • ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceCrossingFamily_isHermitian
    (xi : ℝ) (n : ℕ) (t u : ℝ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceCrossingFamily xi n t u).IsHermitian := by
  apply Matrix.IsHermitian.add
  · apply Matrix.IsHermitian.add
    · exact ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac_isHermitian xi n
    · apply Matrix.IsHermitian.smul
      · exact ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear_isHermitian
      · rw [isSelfAdjoint_iff]
        simp
  · apply Matrix.IsHermitian.smul
    · exact ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear_isHermitian
    · rw [isSelfAdjoint_iff]
      simp

theorem det_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceCrossingFamily
    (xi : ℝ) (n : ℕ) (t u : ℝ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceCrossingFamily xi n t u).det =
      (-(2 * (t * (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re +
        u * (ccmActualHeadMatchedOrientedPhaseSymbol n xi).im)) : ℝ) := by
  apply Complex.ext
  · simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceCrossingFamily,
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac,
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear,
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear,
      Matrix.det_fin_three, Complex.mul_re, Complex.mul_im]
    ring
  · simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceCrossingFamily,
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac,
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear,
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear,
      Matrix.det_fin_three, Complex.mul_re, Complex.mul_im]
    ring

/-- Squared norm of the two fixed shear crossing coordinates. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy
    (xi : ℝ) (n : ℕ) : ℝ :=
  ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealCrossingForm xi n ^ (2 : ℕ) +
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm xi n ^ (2 : ℕ)

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy xi n =
      4 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (4 : ℕ) *
        Complex.normSq (ccmActualHeadMatchedOrientedPhaseSymbol n xi) := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealCrossingForm_eq,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm_eq,
    Complex.normSq_apply]
  ring

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy_primePower_pos_iff
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) :
    0 < ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy xi
      (xiGammaEulerValuationNat (p, e)) ↔ xi ≠ 0 := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy_eq]
  have hw :
      0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  have hgauge :=
    ccmActualHeadMatchedPhaseProjectiveGauge_ne_zero_of_criticalMellinAtomWeight_ne_zero
      (xiGammaEulerValuationNat (p, e)) hw.ne'
  have hfactor :
      0 < 4 * ccmActualHeadMatchedPhaseProjectiveGauge
        (xiGammaEulerValuationNat (p, e)) ^ (4 : ℕ) := by positivity
  rw [mul_pos_iff_of_pos_left hfactor]
  rw [Complex.normSq_pos]
  exact ccmActualHeadMatchedOrientedPhaseSymbol_primePower_ne_zero_iff p e xi

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy_primePower_eq_zero_iff
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy xi
      (xiGammaEulerValuationNat (p, e)) = 0 ↔ xi = 0 := by
  constructor
  · intro henergy
    by_contra hxi
    have hpos :=
      (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy_primePower_pos_iff
        p e xi).mpr hxi
    linarith
  · rintro rfl
    rw [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy_eq]
    simp

@[simp]
theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy_zero
    (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy 0 n = 0 := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy_eq]
  simp

theorem hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbol_im_zero
    (n : ℕ) :
    HasDerivAt (fun xi : ℝ => (ccmActualHeadMatchedOrientedPhaseSymbol n xi).im)
      (-ccmActualHeadMatchedOrientedFirstMoment n) 0 := by
  let L := 2 * Real.pi * Real.log n
  have hlin : HasDerivAt (fun x : ℝ => L * x) L 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul L
  have hC := hasDerivAt_ccmActualHeadMatchedCosinePhaseProfile n 0
  have hP := hasDerivAt_ccmActualHeadMatchedSinePhaseProfile n 0
  have h := (hlin.sin.mul hC).sub (hlin.cos.mul hP)
  rw [show (fun xi : ℝ => (ccmActualHeadMatchedOrientedPhaseSymbol n xi).im) =
      fun xi : ℝ => Real.sin (L * xi) * ccmActualHeadMatchedCosinePhaseProfile n xi -
        Real.cos (L * xi) * ccmActualHeadMatchedSinePhaseProfile n xi by
    funext xi
    simpa only [L] using ccmActualHeadMatchedOrientedPhaseSymbol_im n xi]
  have hpointwise :
      ((fun x : ℝ => Real.sin (L * x)) * ccmActualHeadMatchedCosinePhaseProfile n -
        (fun x : ℝ => Real.cos (L * x)) * ccmActualHeadMatchedSinePhaseProfile n) =
      fun x : ℝ => Real.sin (L * x) * ccmActualHeadMatchedCosinePhaseProfile n x -
        Real.cos (L * x) * ccmActualHeadMatchedSinePhaseProfile n x := by
    funext x
    rfl
  rw [hpointwise] at h
  apply h.congr_deriv
  simp [ccmActualHeadMatchedCosinePhaseProfile_zero,
    ccmActualHeadMatchedCosinePhaseFirstJet_zero,
    ccmActualHeadMatchedSinePhaseProfile_zero,
    ccmActualHeadMatchedSinePhaseFirstJet_zero]

theorem hasDerivAt_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm_zero
    (n : ℕ) :
    HasDerivAt
      (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm · n)
      (-2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
        ccmActualHeadMatchedOrientedFirstMoment n) 0 := by
  rw [show (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm · n) =
      fun xi : ℝ => 2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).im by
    funext xi
    exact ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm_eq xi n]
  simpa using
    (hasDerivAt_ccmActualHeadMatchedOrientedPhaseSymbol_im_zero n).const_mul
      (2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ))

theorem deriv_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm_zero_primePower_neg
    (p : Nat.Primes) (e : ℕ) :
    deriv
      (fun xi : ℝ =>
        ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm xi
          (xiGammaEulerValuationNat (p, e))) 0 < 0 := by
  rw [(hasDerivAt_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagCrossingForm_zero
    (xiGammaEulerValuationNat (p, e))).deriv]
  have hw :
      0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  have hgauge :=
    ccmActualHeadMatchedPhaseProjectiveGauge_ne_zero_of_criticalMellinAtomWeight_ne_zero
      (xiGammaEulerValuationNat (p, e)) hw.ne'
  have hsq :
      0 < ccmActualHeadMatchedPhaseProjectiveGauge
        (xiGammaEulerValuationNat (p, e)) ^ (2 : ℕ) := sq_pos_of_ne_zero hgauge
  have hm := ccmActualHeadMatchedOrientedFirstMoment_primePower_pos p e
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hsq) hm

/-- Label-preserving joint crossing energy of a finite prime-power packet. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerJointCrossingEnergy
    (S : Finset (Nat.Primes × ℕ)) (xi : ℝ) : ℝ :=
  ∑ pe ∈ S,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy xi
      (xiGammaEulerValuationNat pe)

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerJointCrossingEnergy_pos_iff
    {S : Finset (Nat.Primes × ℕ)} (hS : S.Nonempty) (xi : ℝ) :
    0 < ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerJointCrossingEnergy
      S xi ↔ xi ≠ 0 := by
  constructor
  · intro hpos hxi
    subst xi
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerJointCrossingEnergy]
      at hpos
  · intro hxi
    obtain ⟨pe, hpe⟩ := hS
    unfold ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerJointCrossingEnergy
    have hlt :
        (∑ _pe ∈ S, (0 : ℝ)) <
          ∑ pe ∈ S,
            ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy xi
              (xiGammaEulerValuationNat pe) := by
      apply Finset.sum_lt_sum
      · intro x hx
        exact (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy_primePower_pos_iff
          x.1 x.2 xi).mpr hxi |>.le
      · exact ⟨pe, hpe,
          (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceJointCrossingEnergy_primePower_pos_iff
            pe.1 pe.2 xi).mpr hxi⟩
    simpa using hlt

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerJointCrossingEnergy_eq_zero_iff
    {S : Finset (Nat.Primes × ℕ)} (hS : S.Nonempty) (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerJointCrossingEnergy
      S xi = 0 ↔ xi = 0 := by
  constructor
  · intro henergy
    by_contra hxi
    have hpos :=
      (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerJointCrossingEnergy_pos_iff
        hS xi).mpr hxi
    linarith
  · rintro rfl
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerJointCrossingEnergy]

end RHTower

