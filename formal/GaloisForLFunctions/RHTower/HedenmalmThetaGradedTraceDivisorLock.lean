import GaloisForLFunctions.HTGeometry.GradedTraceDeterminantRigidity
import GaloisForLFunctions.RHTower.HedenmalmThetaKreinTracePolarization

/-!
# Theta-source graded trace divisor lock

This module packages the requested finite-stage graded/Krein source polarization at full strength:

* exact signed traces in every degree;
* pole-free ordinary superdeterminants;
* real even finite-stage divisors;
* Krein metric-adjointness and exact coercive escape.

The universal graded trace determinant rigidity theorem then identifies its superdeterminant with
the existing chiral theta-source determinant.  Compact-open convergence to `XiC` follows
unconditionally from the source construction.  The same identity shows the decisive obstruction:
real even divisors force every original source divisor to be real, which closes RH by zero transfer.

The closed endpoint says: RH holds, or no object satisfying all requested fields exists.  Thus a
graded or Krein enlargement cannot manufacture real finite stages while preserving coefficient-
faithful signed traces; doing so is already an RH proof.
-/

open Complex Matrix
open scoped Matrix

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Full finite-stage specification for a pole-free, real-divisor, coercively escaping graded
theta-source lift. -/
structure ThetaSourceRealGradedTraceLift where
  oddRank : ℕ → ℕ
  odd : (k : ℕ) → Matrix (Fin (oddRank k)) (Fin (oddRank k)) ℂ
  even : (k : ℕ) →
    Matrix (↑(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k))
      (↑(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k)) ℂ
  signedTrace : ∀ k m : ℕ,
    ((even k) ^ m).trace - ((odd k) ^ m).trace =
      ((thetaSourceKreinFiniteMatrix k) ^ m).trace
  realDivisor : ∀ k : ℕ, ∀ z : ℂ,
    ((1 : Matrix (↑(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k))
        (↑(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k)) ℂ) -
      z • even k).det = 0 → z.im = 0
  oddDet_ne_zero : ∀ k : ℕ, ∀ z : ℂ,
    ((1 : Matrix (Fin (oddRank k)) (Fin (oddRank k)) ℂ) - z • odd k).det ≠ 0
  polarization : (k : ℕ) →
    Matrix (↑(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k))
      (↑(thetaSourceSignedCutoff k) ⊕ Fin (oddRank k)) ℂ
  metricAdjoint : ∀ k : ℕ,
    polarization k * even k = (even k)ᴴ * polarization k
  coerciveEscape : ∀ k : ℕ,
    (polarization k)ᴴ * polarization k =
      ((((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) • 1

/-- Ordinary numerator determinant of a graded theta-source lift. -/
def thetaSourceGradedEvenDet (L : ThetaSourceRealGradedTraceLift)
    (k : ℕ) (z : ℂ) : ℂ :=
  ((1 : Matrix (↑(thetaSourceSignedCutoff k) ⊕ Fin (L.oddRank k))
      (↑(thetaSourceSignedCutoff k) ⊕ Fin (L.oddRank k)) ℂ) - z • L.even k).det

/-- Ordinary denominator determinant of a graded theta-source lift. -/
def thetaSourceGradedOddDet (L : ThetaSourceRealGradedTraceLift)
    (k : ℕ) (z : ℂ) : ℂ :=
  ((1 : Matrix (Fin (L.oddRank k)) (Fin (L.oddRank k)) ℂ) - z • L.odd k).det

/-- Centrally normalized finite ordinary superdeterminant. -/
def thetaSourceGradedSuperdetCandidate (L : ThetaSourceRealGradedTraceLift)
    (k : ℕ) (z : ℂ) : ℂ :=
  XiC 0 * thetaSourceGradedEvenDet L k z / thetaSourceGradedOddDet L k z

/-- Exact all-degree signed traces force numerator factorization by the source determinant. -/
theorem thetaSourceRealGradedTraceLift_det_factor
    (L : ThetaSourceRealGradedTraceLift) (k : ℕ) (z : ℂ) :
    thetaSourceGradedEvenDet L k z =
      thetaSourceSignedOrdinaryDet k z * thetaSourceGradedOddDet L k z := by
  unfold thetaSourceGradedEvenDet thetaSourceGradedOddDet
  exact graded_signedTrace_preservation_forces_det_factor
    (thetaSourceKreinFiniteMatrix k) (L.odd k) (L.even k) (L.signedTrace k) z

/-- Pole-free graded superdeterminant is exactly the existing chiral source determinant. -/
theorem thetaSourceGradedSuperdetCandidate_eq_chiral
    (L : ThetaSourceRealGradedTraceLift) :
    thetaSourceGradedSuperdetCandidate L = thetaSourceKreinChiralXiCandidate := by
  funext k z
  rw [thetaSourceGradedSuperdetCandidate,
    thetaSourceRealGradedTraceLift_det_factor]
  simpa [thetaSourceGradedOddDet, thetaSourceKreinChiralXiCandidate, mul_assoc] using
    mul_div_cancel_right₀ (XiC 0 * thetaSourceSignedOrdinaryDet k z)
      (L.oddDet_ne_zero k z)

/-- Every such ordinary superdeterminant converges compact-open to `XiC`. -/
theorem thetaSourceGradedSuperdetCandidate_tendstoLocallyUniformly_XiC
    (L : ThetaSourceRealGradedTraceLift) :
    TendstoLocallyUniformly (thetaSourceGradedSuperdetCandidate L) XiC Filter.atTop := by
  rw [thetaSourceGradedSuperdetCandidate_eq_chiral]
  exact thetaSourceKreinChiralXiCandidate_tendstoLocallyUniformly_XiC

/-- A full real-divisor graded theta-source lift proves RH.  Coercive escape and Krein
self-adjointness cannot weaken the exact signed-trace divisor lock. -/
theorem riemannHypothesis_of_thetaSourceRealGradedTraceLift
    (L : ThetaSourceRealGradedTraceLift) : RiemannHypothesis := by
  apply riemannHypothesis_of_thetaSourceKreinChiralXiCandidate_realDivisor
  intro k z hz
  have hsource : thetaSourceSignedOrdinaryDet k z = 0 := by
    unfold thetaSourceKreinChiralXiCandidate at hz
    exact (mul_eq_zero.mp hz).resolve_left XiC_zero_ne
  apply source_realDivisor_of_graded_signedTrace_realDivisor
    (thetaSourceKreinFiniteMatrix k) (L.odd k) (L.even k)
    (L.signedTrace k) (L.realDivisor k)
  exact hsource

/-- **Closed graded-divisor lock.** Either RH holds, or no exact, pole-free, real-divisor,
coercively escaping graded theta-source lift exists. -/
theorem riemannHypothesis_or_no_thetaSourceRealGradedTraceLift :
    RiemannHypothesis ∨ IsEmpty ThetaSourceRealGradedTraceLift := by
  by_cases h : Nonempty ThetaSourceRealGradedTraceLift
  · left
    exact riemannHypothesis_of_thetaSourceRealGradedTraceLift h.some
  · right
    exact ⟨fun L => h ⟨L⟩⟩

end

end RHTower.HedenmalmThetaSource
