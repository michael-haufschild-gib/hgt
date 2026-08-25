import GaloisForLFunctions.RHTower.MobiusThetaInternalJetSourceLocalSpanning
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology

/-!
# Multiplicity-rank cofinal anomaly at an Xi divisor

The cofinal paracyclic anomaly is usually read on the first surviving Xi jet. Here it is read on
the complete internally promoted local source basis. The resulting matrix is the local Xi moment
matrix multiplied by the single transverse monodromy defect. Hence an off-line zero carries a
full-rank anomaly through every multiplicity direction, while a critical-line zero carries none.
-/

open Complex

noncomputable section
namespace RHTower

/-- Cofinal relative-homology readouts on the complete local Xi source-jet basis. -/
def thetaInternalJetCofinalAnomalyMatrix
    (n m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    Matrix (Fin (xiSupportMultiplicity rho))
      (Fin (xiSupportMultiplicity rho)) ℂ :=
  fun i j =>
    tateClockCofinalRelativeH1Equiv m
      (ccmMobiusThetaCofinalSourceHomologyLanding n
        (xiSupportMultiplicity rho - i.val + j.val) m (rho : ℂ)
        (xiSpectralPointSupport rho)
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p))

/-- Every multiplicity coordinate sees the same transverse monodromy defect. -/
theorem thetaInternalJetCofinalAnomalyMatrix_apply
    (n m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes)
    (i j : Fin (xiSupportMultiplicity rho)) :
    thetaInternalJetCofinalAnomalyMatrix n m rho p i j =
      ((deningerHalfDensityMateGain n (rho : ℂ) : ℂ) - 1) *
        thetaInternalJetLocalMomentMatrix rho i j := by
  rw [thetaInternalJetCofinalAnomalyMatrix,
    ccmMobiusThetaCofinalSourceHomologyLanding_readout,
    ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one,
    mul_one, thetaInternalJetLocalMomentMatrix_apply]

/-- Matrix form: longitudinal Xi multiplicity and transverse monodromy separate exactly. -/
theorem thetaInternalJetCofinalAnomalyMatrix_eq_smul
    (n m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaInternalJetCofinalAnomalyMatrix n m rho p =
      ((deningerHalfDensityMateGain n (rho : ℂ) : ℂ) - 1) •
        thetaInternalJetLocalMomentMatrix rho := by
  ext i j
  rw [thetaInternalJetCofinalAnomalyMatrix_apply]
  rfl

/-- Exact anomaly determinant: transverse defect to the analytic multiplicity times the complete
nonzero longitudinal Xi determinant. -/
theorem det_thetaInternalJetCofinalAnomalyMatrix
    (n m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    (thetaInternalJetCofinalAnomalyMatrix n m rho p).det =
      ((deningerHalfDensityMateGain n (rho : ℂ) : ℂ) - 1) ^
          xiSupportMultiplicity rho *
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)) ^ xiSupportMultiplicity rho := by
  rw [thetaInternalJetCofinalAnomalyMatrix_eq_smul, Matrix.det_smul,
    Fintype.card_fin, det_thetaInternalJetLocalMomentMatrix]

/-- The multiplicity anomaly determinant is nonzero exactly off the critical line. -/
theorem det_thetaInternalJetCofinalAnomalyMatrix_ne_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    (thetaInternalJetCofinalAnomalyMatrix n m rho p).det ≠ 0 ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  rw [det_thetaInternalJetCofinalAnomalyMatrix]
  constructor
  · intro hdet hline
    have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 :=
      (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).2 hline
    have hrne : xiSupportMultiplicity rho ≠ 0 :=
      Nat.ne_of_gt (xiSupportMultiplicity_pos rho)
    apply hdet
    rw [hgain]
    simp [hrne]
  · intro hoff
    have hgain : deningerHalfDensityMateGain n (rho : ℂ) ≠ 1 := by
      intro h
      exact hoff ((deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).1 h)
    apply mul_ne_zero
    · apply pow_ne_zero
      exact sub_ne_zero.mpr (by exact_mod_cast hgain)
    · exact pow_ne_zero _ (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)

/-- Off line, cofinal anomalies are independent in all local multiplicity directions. -/
theorem thetaInternalJetCofinalAnomalyMatrix_linearIndependent_of_re_ne_half
    {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    LinearIndependent ℂ (fun i => thetaInternalJetCofinalAnomalyMatrix n m rho p i) :=
  Matrix.linearIndependent_rows_of_det_ne_zero
    ((det_thetaInternalJetCofinalAnomalyMatrix_ne_zero_iff hn m rho p).2 hoff)

/-- On the critical line, every multiplicity-direction anomaly vanishes simultaneously. -/
theorem thetaInternalJetCofinalAnomalyMatrix_eq_zero_of_re_eq_half
    {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes)
    (hline : (rho : ℂ).re = 1 / 2) :
    thetaInternalJetCofinalAnomalyMatrix n m rho p = 0 := by
  rw [thetaInternalJetCofinalAnomalyMatrix_eq_smul]
  have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 :=
    (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).2 hline
  rw [hgain]
  norm_num

/-- Full-rank versus zero-rank dichotomy for the complete multiplicity anomaly packet. -/
theorem thetaInternalJetCofinalAnomalyMatrix_linearIndependent_iff
    {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    LinearIndependent ℂ (fun i => thetaInternalJetCofinalAnomalyMatrix n m rho p i) ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro hIndependent hline
    have hzero := thetaInternalJetCofinalAnomalyMatrix_eq_zero_of_re_eq_half
      hn m rho p hline
    let i : Fin (xiSupportMultiplicity rho) :=
      ⟨0, xiSupportMultiplicity_pos rho⟩
    have hrow : thetaInternalJetCofinalAnomalyMatrix n m rho p i = 0 := by
      rw [hzero]
      rfl
    exact (hIndependent.ne_zero i) hrow
  · exact thetaInternalJetCofinalAnomalyMatrix_linearIndependent_of_re_ne_half
      hn m rho p

/-- Divide out the nonsingular longitudinal Xi source frame. The remaining endomorphism measures
only transverse cyclic-to-paracyclic incompatibility. -/
def thetaInternalJetNormalizedCofinalAnomalyMatrix
    (n m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    Matrix (Fin (xiSupportMultiplicity rho))
      (Fin (xiSupportMultiplicity rho)) ℂ :=
  thetaInternalJetCofinalAnomalyMatrix n m rho p *
    (thetaInternalJetLocalMomentMatrix rho)⁻¹

/-- **Central-anomaly law.** After the complete multiplicity-bearing source frame is removed, the
cofinal anomaly is the same scalar on every Xi jet direction. Multiplicity cannot rotate, absorb,
or partially cancel horizontal displacement. -/
theorem thetaInternalJetNormalizedCofinalAnomalyMatrix_eq_smul_one
    (n m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaInternalJetNormalizedCofinalAnomalyMatrix n m rho p =
      ((deningerHalfDensityMateGain n (rho : ℂ) : ℂ) - 1) • 1 := by
  rw [thetaInternalJetNormalizedCofinalAnomalyMatrix,
    thetaInternalJetCofinalAnomalyMatrix_eq_smul, Matrix.smul_mul]
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
    (det_thetaInternalJetLocalMomentMatrix_ne_zero rho))]

end RHTower
