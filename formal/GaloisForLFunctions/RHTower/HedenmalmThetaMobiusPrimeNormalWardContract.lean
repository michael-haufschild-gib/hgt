import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPrimeNormalProfileBridge
import GaloisForLFunctions.RHTower.HedenmalmThetaKakutaniHarmonicCoercivity

/-!
# Physical Möbius prime-normal Ward contract

The singular Möbius prime-normal profile is already coefficient-exactly welded to Route P's
positive polarization.  This file identifies the precise finite-packet source estimate which
remains: uniform boundedness of its weighted squares.  Pointwise this contract is equivalent to
positivity of the corresponding Route P squared node; on every Xi copy it is equivalent to RH.

No convergence hypothesis is hidden in the definition: the source contract quantifies only over
finite prime packets.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Weighted finite-packet energy of the literal singular Möbius prime-normal reflection profile. -/
def thetaMobiusPrimeNormalProfilePacketEnergy
    (q : XiZeroCopy) (s : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ s, thetaMobiusPrimeNormalProfilePositiveGauge p q *
    thetaMobiusPrimeNormalReflectionProfile p q ^ (2 : ℕ)

/-- The physical source packet energy is exactly the already isolated theta/Kakutani packet
energy, coefficient by coefficient. -/
theorem thetaMobiusPrimeNormalProfilePacketEnergy_eq_thetaPolarization
    (q : XiZeroCopy) (s : Finset Nat.Primes) :
    thetaMobiusPrimeNormalProfilePacketEnergy q s =
      ∑ p ∈ s, thetaKakutaniFluxPositiveUnit p q *
        thetaXiRankTwoBoundaryFlux q ^ (2 : ℕ) := by
  apply Finset.sum_congr rfl
  intro p _hp
  rw [← primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq,
    primeValuationHellingerGap_eq_mobiusPrimeNormalProfile_sq]

/-- Finite-packet Ward admission on one multiplicity-resolved Xi divisor copy. -/
def ThetaMobiusPrimeNormalWardBoundAt (q : XiZeroCopy) : Prop :=
  ∃ C : ℝ, ∀ s : Finset Nat.Primes,
    thetaMobiusPrimeNormalProfilePacketEnergy q s ≤ C

/-- The finite-packet physical source contract at one copy is exactly positivity of its Route P
squared spectral node. -/
theorem thetaMobiusPrimeNormalWardBoundAt_iff_reciprocalEigenvalue_sq_positiveReal
    (q : XiZeroCopy) :
    ThetaMobiusPrimeNormalWardBoundAt q ↔
      ∃ r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ (2 : ℕ) = (r : ℂ) := by
  rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_uniform_finset_polarization_bound]
  simp only [ThetaMobiusPrimeNormalWardBoundAt]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun s => by
      rw [← thetaMobiusPrimeNormalProfilePacketEnergy_eq_thetaPolarization]
      exact hC s⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun s => by
      rw [thetaMobiusPrimeNormalProfilePacketEnergy_eq_thetaPolarization]
      exact hC s⟩

/-- Global finite-packet Ward contract for the literal singular Möbius source graph. -/
def ThetaMobiusPrimeNormalWardBound : Prop :=
  ∀ q : XiZeroCopy, ThetaMobiusPrimeNormalWardBoundAt q

/-- **Exact physical Route P producer contract.**  Uniform finite-packet control of the literal
Möbius prime-normal profile on every divisor copy is equivalent to RH. -/
theorem thetaMobiusPrimeNormalWardBound_iff_riemannHypothesis :
    ThetaMobiusPrimeNormalWardBound ↔ RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  constructor
  · intro hward q
    rw [← thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero]
    exact (thetaMobiusPrimeNormalWardBoundAt_iff_reciprocalEigenvalue_sq_positiveReal q).1
      (hward q)
  · intro hneutral q
    apply (thetaMobiusPrimeNormalWardBoundAt_iff_reciprocalEigenvalue_sq_positiveReal q).2
    rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero]
    exact hneutral q

end

end RHTower.HedenmalmThetaSource
