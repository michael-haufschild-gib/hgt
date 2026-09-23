import GaloisForLFunctions.HTGeometry.GradedRegularizedTraceDeterminantRigidity
import GaloisForLFunctions.RHTower.HedenmalmThetaKreinTracePolarization

/-!
# Order-two regularized graded theta-source divisor lock

This is the sharp Hilbert--Carleman version of the graded theta-source obstruction.  A proposed
graded/Krein lift is allowed to discard the first trace completely.  It need preserve only the
signed source traces in degrees `2, 3, ...`, exactly the coordinates seen by `det₂`.

Those coordinates already force the regularized superdeterminant to equal the existing signed
theta-source determinant.  Hence real finite-stage even divisors and compact-open convergence to
`XiC` imply RH.  Metric adjointness and coercive escape do not affect the argument.  The positive
design consequence is exact: any genuine zero-moving polarization must introduce a nonzero signed
trace anomaly in some degree at least two.
-/

open Complex Filter Matrix Topology
open scoped Matrix

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HilbertSchmidt

noncomputable section

/-- Proposed pole-free graded/Krein source polarization at Hilbert--Carleman order two.  First
trace is deliberately absent; all divisor-bearing signed traces begin at the quadratic trace. -/
structure ThetaSourceOrderTwoRealGradedPolarization where
  oddRank : ℕ → ℕ
  odd : (k : ℕ) → Matrix (Fin (oddRank k)) (Fin (oddRank k)) ℂ
  even : (k : ℕ) →
    Matrix (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k))
      (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k)) ℂ
  signedTraceFromTwo : ∀ k n : ℕ,
    ((even k) ^ (n + 2)).trace - ((odd k) ^ (n + 2)).trace =
      ((thetaSourceKreinFiniteMatrix k) ^ (n + 2)).trace
  realDivisor : ∀ k : ℕ, ∀ z : ℂ,
    ((1 : Matrix (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k))
        (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k)) ℂ) -
      z • even k).det = 0 → z.im = 0
  oddRegularizedDet_ne_zero : ∀ k : ℕ, ∀ z : ℂ,
    finiteDet2 (-(odd k)) z ≠ 0
  polarization : (k : ℕ) →
    Matrix (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k))
      (↥(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k)) ℂ
  metricAdjoint : ∀ k : ℕ,
    polarization k * even k = (even k)ᴴ * polarization k
  coerciveEscape : ∀ k : ℕ,
    (polarization k)ᴴ * polarization k =
      ((((k : ℝ) + 1) ^ (2 : ℕ) : ℝ) : ℂ) • 1

/-- Regularized graded superdeterminant, centrally normalized in the Xi coordinate. -/
def thetaSourceOrderTwoGradedSuperdetCandidate
    (L : ThetaSourceOrderTwoRealGradedPolarization)
    (k : ℕ) (z : ℂ) : ℂ :=
  XiC 0 * finiteDet2 (-(L.even k)) z / finiteDet2 (-(L.odd k)) z

/-- Trace-zero source correction identifies its finite Hilbert--Carleman determinant with the
honest signed ordinary determinant. -/
theorem finiteDet2_neg_thetaSourceKreinFiniteMatrix_eq_signedOrdinaryDet
    (k : ℕ) (z : ℂ) :
    finiteDet2 (-(thetaSourceKreinFiniteMatrix k)) z =
      thetaSourceSignedOrdinaryDet k z := by
  have htrace : (thetaSourceKreinFiniteMatrix k).trace = 0 := by
    rw [thetaSourceKreinFiniteMatrix,
      trace_blockMatrix_eq_hsTraceDiag (thetaSourceSignedKernel_support k),
      hsTraceDiag_thetaSourceSignedKernel]
  rw [finiteDet2, thetaSourceSignedOrdinaryDet]
  have hnegTrace : (-(thetaSourceKreinFiniteMatrix k)).trace = 0 := by
    simp [htrace]
  rw [hnegTrace]
  simp [thetaSourceKreinFiniteMatrix, sub_eq_add_neg]

/-- Signed traces from degree two force exact cross-multiplied `det₂` factorization. -/
theorem thetaSourceOrderTwoRealGradedPolarization_det2_factor
    (L : ThetaSourceOrderTwoRealGradedPolarization) (k : ℕ) (z : ℂ) :
    finiteDet2 (-(L.even k)) z =
      thetaSourceSignedOrdinaryDet k z * finiteDet2 (-(L.odd k)) z := by
  rw [← finiteDet2_neg_thetaSourceKreinFiniteMatrix_eq_signedOrdinaryDet k z]
  exact graded_signedTrace_add_two_forces_finiteDet2_factor
    (thetaSourceKreinFiniteMatrix k) (L.odd k) (L.even k)
      (L.signedTraceFromTwo k) z

/-- The pole-free regularized superdeterminant is exactly the existing chiral theta-source
candidate; first-trace freedom supplies no divisor freedom. -/
theorem thetaSourceOrderTwoGradedSuperdetCandidate_eq_chiral
    (L : ThetaSourceOrderTwoRealGradedPolarization) :
    thetaSourceOrderTwoGradedSuperdetCandidate L =
      thetaSourceKreinChiralXiCandidate := by
  funext k z
  rw [thetaSourceOrderTwoGradedSuperdetCandidate,
    thetaSourceOrderTwoRealGradedPolarization_det2_factor]
  simpa [thetaSourceKreinChiralXiCandidate, mul_assoc] using
    mul_div_cancel_right₀ (XiC 0 * thetaSourceSignedOrdinaryDet k z)
      (L.oddRegularizedDet_ne_zero k z)

/-- Consequently every proposed order-two graded superdeterminant has the already-proved
compact-open limit `XiC`. -/
theorem thetaSourceOrderTwoGradedSuperdetCandidate_tendstoLocallyUniformly_XiC
    (L : ThetaSourceOrderTwoRealGradedPolarization) :
    TendstoLocallyUniformly (thetaSourceOrderTwoGradedSuperdetCandidate L)
      XiC atTop := by
  rw [thetaSourceOrderTwoGradedSuperdetCandidate_eq_chiral]
  exact thetaSourceKreinChiralXiCandidate_tendstoLocallyUniformly_XiC

/-- Real finite-stage even divisors plus signed trace fidelity from degree two already prove RH.
Neither first trace, metric adjointness, nor coercive escape is used. -/
theorem riemannHypothesis_of_thetaSourceOrderTwoRealGradedPolarization
    (L : ThetaSourceOrderTwoRealGradedPolarization) : RiemannHypothesis := by
  apply riemannHypothesis_of_thetaSourceKreinChiralXiCandidate_realDivisor
  intro k z hz
  have hsource : thetaSourceSignedOrdinaryDet k z = 0 := by
    unfold thetaSourceKreinChiralXiCandidate at hz
    exact (mul_eq_zero.mp hz).resolve_left XiC_zero_ne
  apply source_realDivisor_of_graded_signedTrace_add_two_realDivisor
    (thetaSourceKreinFiniteMatrix k) (L.odd k) (L.even k)
      (L.signedTraceFromTwo k) (L.realDivisor k)
  simpa [thetaSourceSignedOrdinaryDet, thetaSourceKreinFiniteMatrix] using hsource

/-- Closed order-two lock: either RH holds or no pole-free, real-divisor, coercively escaping
graded theta-source polarization can preserve every signed trace from the quadratic one onward. -/
theorem riemannHypothesis_or_no_thetaSourceOrderTwoRealGradedPolarization :
    RiemannHypothesis ∨ IsEmpty ThetaSourceOrderTwoRealGradedPolarization := by
  by_cases h : Nonempty ThetaSourceOrderTwoRealGradedPolarization
  · left
    exact riemannHypothesis_of_thetaSourceOrderTwoRealGradedPolarization h.some
  · right
    exact ⟨fun L => h ⟨L⟩⟩

end

end RHTower.HedenmalmThetaSource
