import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeComplexDiracTwoShear

/-!
# Self-polarized complex Dirac shear

A fixed real projection of the matched complex phase symbol can cross zero even
when the symbol does not.  The source instead selects its own division-free
Hermitian shear direction, using its real and imaginary coordinates as the two
shear coefficients.

The resulting nodal form is a positive gauge factor times `normSq Z`, and the
adaptive Dirac determinant is exactly `-2 t normSq Z`.  Thus every actual
prime-power atom has one global determinant chamber: for positive shear time
the spectral center is the unique zero and strict global maximum, while the
determinant is negative at every off-center frequency.  Nonempty finite labeled
packets inherit the same law.

This constructs a source-native scalarization of the two-shear plane.  It does
not identify that adaptive determinant with the global Weil/Xi receiver.
-/


open Complex MeasureTheory Set Filter Topology Matrix
open scoped BigOperators ComplexConjugate

noncomputable section
namespace RHTower

/-- Division-free shear selected by the full complex matched source coordinate. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedShear
    (xi : ℝ) (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((ccmActualHeadMatchedOrientedPhaseSymbol n xi).re : ℂ) •
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear +
    ((ccmActualHeadMatchedOrientedPhaseSymbol n xi).im : ℂ) •
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedShear_isHermitian
    (xi : ℝ) (n : ℕ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedShear xi n).IsHermitian := by
  apply Matrix.IsHermitian.add
  · apply Matrix.IsHermitian.smul
    · exact ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear_isHermitian
    · rw [isSelfAdjoint_iff]
      simp
  · apply Matrix.IsHermitian.smul
    · exact ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear_isHermitian
    · rw [isSelfAdjoint_iff]
      simp

/-- Nodal expectation of the source-selected shear. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm
    (xi : ℝ) (n : ℕ) : ℝ :=
  (star (ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector xi n) ⬝ᵥ
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedShear xi n *ᵥ
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector xi n)).re

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm_eq
    (xi : ℝ) (n : ℕ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm xi n =
      2 * ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
        Complex.normSq (ccmActualHeadMatchedOrientedPhaseSymbol n xi) := by
  simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedShear,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalVector,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexNodalUnitVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.mul_re,
    Complex.normSq_apply]
  ring

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm_primePower_pos_iff
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) :
    0 < ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm xi
      (xiGammaEulerValuationNat (p, e)) ↔ xi ≠ 0 := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm_eq]
  have hw :
      0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  have hgauge :=
    ccmActualHeadMatchedPhaseProjectiveGauge_ne_zero_of_criticalMellinAtomWeight_ne_zero
      (xiGammaEulerValuationNat (p, e)) hw.ne'
  have hfactor :
      0 < 2 * ccmActualHeadMatchedPhaseProjectiveGauge
        (xiGammaEulerValuationNat (p, e)) ^ (2 : ℕ) := by positivity
  rw [mul_pos_iff_of_pos_left hfactor]
  rw [Complex.normSq_pos]
  exact ccmActualHeadMatchedOrientedPhaseSymbol_primePower_ne_zero_iff p e xi

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm_primePower_eq_zero_iff
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm xi
      (xiGammaEulerValuationNat (p, e)) = 0 ↔ xi = 0 := by
  constructor
  · intro hform
    by_contra hxi
    have hpos :=
      (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm_primePower_pos_iff
        p e xi).mpr hxi
    linarith
  · rintro rfl
    rw [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm_eq]
    simp

/-- Dirac wall sheared in the source-selected complex direction. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily
    (xi : ℝ) (n : ℕ) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac xi n +
    (t : ℂ) •
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedShear xi n

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_isHermitian
    (xi : ℝ) (n : ℕ) (t : ℝ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily
      xi n t).IsHermitian := by
  apply Matrix.IsHermitian.add
  · exact ccmActualHeadMatchedPhaseProjectiveGaugeComplexDirac_isHermitian xi n
  · apply Matrix.IsHermitian.smul
    · exact
        ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedShear_isHermitian xi n
    · rw [isSelfAdjoint_iff]
      simp

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_eq_twoShear
    (xi : ℝ) (n : ℕ) (t : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily xi n t =
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceCrossingFamily xi n
        (t * (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re)
        (t * (ccmActualHeadMatchedOrientedPhaseSymbol n xi).im) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily,
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedShear,
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceCrossingFamily,
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceRealShear,
      ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceImagShear] <;>
    ring_nf
  have hz :=
    (Complex.re_add_im (ccmActualHeadMatchedOrientedPhaseSymbol n xi)).symm
  linear_combination (t : ℂ) * hz

theorem det_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily
    (xi : ℝ) (n : ℕ) (t : ℝ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily
      xi n t).det =
      ((-2 * t * Complex.normSq
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi) : ℝ) : ℂ) := by
  rw [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_eq_twoShear,
    det_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceCrossingFamily,
    Complex.normSq_apply]
  push_cast
  ring

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedDeterminantKreinReciprocity
    (xi : ℝ) (n : ℕ) (t : ℝ) :
    ccmActualHeadMatchedPhaseProjectiveGauge n ^ (2 : ℕ) *
        (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily
          xi n t).det.re =
      -t * ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm xi n := by
  rw [det_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily,
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm_eq]
  simp
  ring

theorem det_re_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_primePower_neg_iff
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) {t : ℝ} (ht : 0 < t) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily xi
      (xiGammaEulerValuationNat (p, e)) t).det.re < 0 ↔ xi ≠ 0 := by
  rw [det_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily]
  simp only [ofReal_re]
  constructor
  · intro hdet
    have hnorm :
        0 < Complex.normSq
          (ccmActualHeadMatchedOrientedPhaseSymbol
            (xiGammaEulerValuationNat (p, e)) xi) := by
      nlinarith [Complex.normSq_nonneg
        (ccmActualHeadMatchedOrientedPhaseSymbol
          (xiGammaEulerValuationNat (p, e)) xi)]
    exact (ccmActualHeadMatchedOrientedPhaseSymbol_primePower_ne_zero_iff p e xi).mp
      (Complex.normSq_pos.mp hnorm)
  · intro hxi
    have hnorm :
        0 < Complex.normSq
          (ccmActualHeadMatchedOrientedPhaseSymbol
            (xiGammaEulerValuationNat (p, e)) xi) :=
      Complex.normSq_pos.mpr
        ((ccmActualHeadMatchedOrientedPhaseSymbol_primePower_ne_zero_iff p e xi).mpr hxi)
    nlinarith

theorem det_re_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_primePower_eq_zero_iff
    (p : Nat.Primes) (e : ℕ) (xi t : ℝ) (ht : t ≠ 0) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily xi
      (xiGammaEulerValuationNat (p, e)) t).det.re = 0 ↔ xi = 0 := by
  rw [det_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily]
  simp only [ofReal_re]
  have hziff :
      ccmActualHeadMatchedOrientedPhaseSymbol
        (xiGammaEulerValuationNat (p, e)) xi = 0 ↔ xi = 0 := by
    simpa only [not_ne_iff] using
      not_congr (ccmActualHeadMatchedOrientedPhaseSymbol_primePower_ne_zero_iff p e xi)
  simp [ht, hziff]

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_primePower_global_max_zero
    (p : Nat.Primes) (e : ℕ) {t : ℝ} (ht : 0 < t) (xi : ℝ) :
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily xi
      (xiGammaEulerValuationNat (p, e)) t).det.re ≤
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily 0
      (xiGammaEulerValuationNat (p, e)) t).det.re := by
  rw [det_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily,
    det_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily]
  simp only [ofReal_re, ccmActualHeadMatchedOrientedPhaseSymbol_zero,
    Complex.normSq_zero, mul_zero]
  nlinarith [Complex.normSq_nonneg
    (ccmActualHeadMatchedOrientedPhaseSymbol
      (xiGammaEulerValuationNat (p, e)) xi)]

/-- Label-preserving finite sum of self-polarized determinant responses. -/
def ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse
    (S : Finset (Nat.Primes × ℕ)) (xi t : ℝ) : ℝ :=
  ∑ pe ∈ S,
    (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily xi
      (xiGammaEulerValuationNat pe) t).det.re

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse_neg_iff
    {S : Finset (Nat.Primes × ℕ)} (hS : S.Nonempty) (xi : ℝ) {t : ℝ} (ht : 0 < t) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse
      S xi t < 0 ↔ xi ≠ 0 := by
  constructor
  · intro hneg hxi
    subst xi
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse,
      det_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily]
      at hneg
  · intro hxi
    obtain ⟨pe, hpe⟩ := hS
    unfold ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse
    have hlt :
        (∑ pe ∈ S,
          (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily xi
            (xiGammaEulerValuationNat pe) t).det.re) <
          ∑ _pe ∈ S, (0 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro x hx
        exact
          (det_re_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_primePower_neg_iff
            x.1 x.2 xi ht).mpr hxi |>.le
      · exact ⟨pe, hpe,
          (det_re_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_primePower_neg_iff
            pe.1 pe.2 xi ht).mpr hxi⟩
    simpa using hlt

theorem ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse_eq_zero_iff
    {S : Finset (Nat.Primes × ℕ)} (hS : S.Nonempty) (xi : ℝ) {t : ℝ} (ht : 0 < t) :
    ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse
      S xi t = 0 ↔ xi = 0 := by
  constructor
  · intro hresponse
    by_contra hxi
    have hneg :=
      (ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse_neg_iff
        hS xi ht).mpr hxi
    linarith
  · rintro rfl
    simp [ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse,
      det_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily]

end RHTower

