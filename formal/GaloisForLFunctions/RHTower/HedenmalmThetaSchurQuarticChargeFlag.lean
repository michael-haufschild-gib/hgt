import GaloisForLFunctions.RHTower.HedenmalmThetaHermiteTraceFlag
import GaloisForLFunctions.HTGeometry.FinitePacketSchwarzDoubledPositiveQuarticRealification

/-!
# Theta-source Schur quartic charge flag

Every Schur packet of an actual finite signed theta-source matrix receives the positive quartic
charge from finite-packet Schwarz-doubled realification. For any choice of Schur triangularization,
charge zero is exactly arithmetic Hermite positivity, ordinary real divisor, and modewise Green
neutrality at that stage.

Requiring zero charge at every stage and for every Schur packet is therefore exactly the existing
Hermite, Green, and all-stage real-divisor flags, hence implies RH. This closes finite spectral
transport for the positive GTA reporter. It does not prove the remaining arithmetic source-side
vanishing of the global charge flag.
-/

open Complex Filter Metric Polynomial
open scoped BigOperators Matrix

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmHilbertSchmidt

noncomputable section

/-- One unitary Schur triangularization of an actual signed theta-source stage. -/
structure ThetaSourceStageSchurPacket (k : ℕ) where
  U : Matrix (Fin (Fintype.card ↥(thetaSourceSignedCutoff k)))
    (Fin (Fintype.card ↥(thetaSourceSignedCutoff k))) ℂ
  T : Matrix (Fin (Fintype.card ↥(thetaSourceSignedCutoff k)))
    (Fin (Fintype.card ↥(thetaSourceSignedCutoff k))) ℂ
  unitary_left : Uᴴ * U = 1
  unitary_right : U * Uᴴ = 1
  triangular : T.BlockTriangular id
  conjugates_stage : Uᴴ * thetaSourceSignedStageFinMatrix k * U = T

/-- Every actual finite stage has a Schur packet. -/
theorem nonempty_thetaSourceStageSchurPacket (k : ℕ) :
    Nonempty (ThetaSourceStageSchurPacket k) := by
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ :=
    GaloisForLFunctions.HTGeometry.exists_schur_triangulation
      (Fintype.card ↥(thetaSourceSignedCutoff k))
      (thetaSourceSignedStageFinMatrix k)
  exact ⟨⟨U, T, hU1, hU2, hT, hMT⟩⟩

/-- Positive quartic charge of the diagonal spectral packet of one Schur stage. -/
def thetaSourceStageSchurPositiveQuarticCharge
    {k : ℕ} (S : ThetaSourceStageSchurPacket k) : ℝ :=
  finitePacketPositiveQuarticCharge (fun i => S.T i i)

theorem thetaSourceStageSchurPositiveQuarticCharge_nonneg
    {k : ℕ} (S : ThetaSourceStageSchurPacket k) :
    0 ≤ thetaSourceStageSchurPositiveQuarticCharge S :=
  finitePacketPositiveQuarticCharge_nonneg (fun i => S.T i i)

/-- At any fixed Schur packet, zero quartic charge is exactly root-free arithmetic Hermite
positivity of the actual stage. -/
theorem thetaSourceStageSchurPositiveQuarticCharge_eq_zero_iff_hermiteStage
    {k : ℕ} (S : ThetaSourceStageSchurPacket k) :
    thetaSourceStageSchurPositiveQuarticCharge S = 0 ↔
      ThetaSourceArithmeticHermiteStageProperty k := by
  constructor
  · intro hcharge
    have hdiag : ∀ i, (S.T i i).im = 0 :=
      (finitePacketPositiveQuarticCharge_eq_zero_iff
        (fun i => S.T i i)).mp hcharge
    intro p
    change 0 ≤ (finiteMatrixUnweightedTraceHankel
      (thetaSourceSignedStageFinMatrix k) p).re
    rw [finiteMatrixUnweightedTraceHankel_eq_schur S.unitary_left
      S.unitary_right S.triangular S.conjugates_stage]
    have hsum : (∑ i, evalRealPolynomial p (S.T i i) ^ 2).re =
        ∑ i, (evalRealPolynomial p (S.T i i) ^ 2).re := by simp
    rw [hsum]
    apply Finset.sum_nonneg
    intro i hi
    let x : ℝ := (S.T i i).re
    have htx : S.T i i = (x : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa [x] using hdiag i
    rw [htx, evalRealPolynomial_ofReal, pow_two, Complex.mul_re]
    simpa only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
      mul_self_nonneg (Polynomial.eval x p)
  · intro hhermite
    apply (finitePacketPositiveQuarticCharge_eq_zero_iff
      (fun i => S.T i i)).mpr
    apply finiteMatrix_unweightedTraceHankel_nonneg_implies_schur_real
      S.unitary_left S.unitary_right S.triangular S.conjugates_stage
    intro p
    exact hhermite p

/-- Zero Schur-packet charge is exactly the ordinary real-divisor property at that actual stage. -/
theorem thetaSourceStageSchurPositiveQuarticCharge_eq_zero_iff_realDivisor
    {k : ℕ} (S : ThetaSourceStageSchurPacket k) :
    thetaSourceStageSchurPositiveQuarticCharge S = 0 ↔
      ThetaSourceSignedStageRealDivisor k := by
  constructor
  · intro h
    exact thetaSourceArithmeticHermiteStage_realDivisor k
      ((thetaSourceStageSchurPositiveQuarticCharge_eq_zero_iff_hermiteStage S).mp h)
  · intro h
    exact (thetaSourceStageSchurPositiveQuarticCharge_eq_zero_iff_hermiteStage S).mpr
      (thetaSourceArithmeticHermiteStage_of_realDivisor k h)

/-- Zero Schur-packet charge is exactly modewise Green neutrality at that actual stage. -/
theorem thetaSourceStageSchurPositiveQuarticCharge_eq_zero_iff_greenStage
    {k : ℕ} (S : ThetaSourceStageSchurPacket k) :
    thetaSourceStageSchurPositiveQuarticCharge S = 0 ↔
      ThetaSourceArithmeticGreenStageProperty k := by
  rw [thetaSourceStageSchurPositiveQuarticCharge_eq_zero_iff_hermiteStage,
    thetaSourceArithmeticHermiteStage_iff_greenStage]

/-- Scalar quartic GTA flag on every actual stage and every Schur realization. -/
def ThetaSourceSchurQuarticChargeFlag : Prop :=
  ∀ (k : ℕ) (S : ThetaSourceStageSchurPacket k),
    thetaSourceStageSchurPositiveQuarticCharge S = 0

/-- Global quartic charge vanishing is exactly the root-free Hermite flag. -/
theorem thetaSourceSchurQuarticChargeFlag_iff_hermiteFlag :
    ThetaSourceSchurQuarticChargeFlag ↔ ThetaSourceArithmeticHermiteFlag := by
  constructor
  · intro h k
    let S : ThetaSourceStageSchurPacket k :=
      Classical.choice (nonempty_thetaSourceStageSchurPacket k)
    exact (thetaSourceStageSchurPositiveQuarticCharge_eq_zero_iff_hermiteStage S).mp
      (h k S)
  · intro h k S
    exact (thetaSourceStageSchurPositiveQuarticCharge_eq_zero_iff_hermiteStage S).mpr
      (h k)

/-- Global quartic charge vanishing is exactly the source Green flag. -/
theorem thetaSourceSchurQuarticChargeFlag_iff_greenFlag :
    ThetaSourceSchurQuarticChargeFlag ↔ ThetaSourceArithmeticGreenFlag := by
  rw [thetaSourceSchurQuarticChargeFlag_iff_hermiteFlag,
    thetaSourceArithmeticHermiteFlag_iff_greenFlag]

/-- Global quartic charge vanishing is exactly real divisor at every actual finite stage. -/
theorem thetaSourceSchurQuarticChargeFlag_iff_allStagesRealDivisor :
    ThetaSourceSchurQuarticChargeFlag ↔ ThetaSourceSignedAllStagesRealDivisor := by
  rw [thetaSourceSchurQuarticChargeFlag_iff_greenFlag,
    thetaSourceArithmeticGreenFlag_iff_allStagesRealDivisor]

/-- The all-stage scalar quartic source law closes RH. -/
theorem riemannHypothesis_of_thetaSourceSchurQuarticChargeFlag
    (h : ThetaSourceSchurQuarticChargeFlag) : RiemannHypothesis :=
  riemannHypothesis_of_thetaSourceArithmeticHermiteFlag
    (thetaSourceSchurQuarticChargeFlag_iff_hermiteFlag.mp h)

end

end RHTower.HedenmalmThetaSource
