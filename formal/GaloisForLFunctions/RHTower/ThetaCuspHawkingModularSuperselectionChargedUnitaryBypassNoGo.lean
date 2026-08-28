import GaloisForLFunctions.RHTower.ThetaCuspHawkingChargedDoubleKMSSectorSwapNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingModularSuperselectionEndpoint

/-!
# Modular-superselection charged-unitary bypass no-go

The strongest modular-superselection objection to the explicit charged double-KMS escape is
representation-relative. At positive Hawking charge, the corpus proves that no finite-Rees-
moderate scalar operator family sews the reflected prime-valuation profiles. This module proves
that the same resonance nevertheless admits exact bounded charge conjugation in the actual HC86
doubled thermofield Hilbert space.

Coordinate transposition on `lp (fun _ : ℕ × ℕ => ℂ) 2` is a linear isometric equivalence. It maps
the visible charged double-KMS half-density exactly to the partner half-density for every resonance
and prime. At positive charge this equality coexists with the full Xi source-modular
superselection certificate, failure of occupation-preserving alignment, and the scalar finite-
Rees no-sewing law.

Thus modular superselection alone cannot supply the missing no-charge-sector producer. A viable
HB route must derive a source-faithful representation-selection or phase/Ward law that rules out
the doubled conjugate-sector completion.

`[NEW] [REPRESENTATION FRACTURE] [EXACT UNITARY] [SUPERSELECTION NO-GO]`
-/

open Complex Filter Asymptotics GaloisForLFunctions

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-- Coordinate transposition on the charged thermofield occupation space. -/
def thetaCuspHawkingChargedDoubleKMSSwapUnitary :
    lp (fun _ : ℕ × ℕ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℕ × ℕ => ℂ) 2 :=
  GaloisForLFunctions.HTGeometry.lpReindexEquiv (Equiv.prodComm ℕ ℕ)

/-- The charged swap maps the actual visible half-density exactly to its partner. -/
theorem thetaCuspHawkingChargedDoubleKMSSwapUnitary_visible_eq_partner
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) :
    thetaCuspHawkingChargedDoubleKMSSwapUnitary
        (thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p) =
      thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p := by
  apply lp.ext
  funext x
  rcases x with ⟨k, l⟩
  simp only [thetaCuspHawkingChargedDoubleKMSSwapUnitary,
    GaloisForLFunctions.HTGeometry.lpReindexEquiv_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply]
  rw [thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity,
    thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity,
    GaloisForLFunctions.HTGeometry.lpTensorProductVector_apply,
    GaloisForLFunctions.HTGeometry.lpTensorProductVector_apply]
  exact mul_comm _ _

/-- Exact doubled-sector unitary conjugation coexists with scalar finite-Rees no-sewing. -/
theorem thetaCuspHawking_positiveCharge_scalarNoSewing_and_chargedUnitarySwap
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hpos : 0 < thetaCuspHawkingBackreactionHorizonCharge r)
    (p : Nat.Primes) (K : ℕ) (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hR : ReesOperatorGradeAtMost atTop primeWoldBoundaryVolumeBelow K R) :
    (fun N =>
      R N
        (primeValuationSquaredHellingerBelow
          (thetaCuspHawkingBackreactionHorizonCharge r) N)) ≠
        primeValuationSquaredHellingerBelow
          (-thetaCuspHawkingBackreactionHorizonCharge r) ∧
      thetaCuspHawkingChargedDoubleKMSSwapUnitary
          (thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p) =
        thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p := by
  exact ⟨no_finiteReesOperator_sews_positive_thetaCuspHawkingHorizon r hpos K R hR,
    thetaCuspHawkingChargedDoubleKMSSwapUnitary_visible_eq_partner r p⟩

/-- Closed representation-fracture statement: every positive-charge resonance has the full scalar
superselection certificate while every prime admits exact doubled-sector unitary conjugation and
fails occupation-preserving alignment. -/
def ThetaCuspHawkingModularSuperselectionChargedUnitaryBypass : Prop :=
  ∀ r : ThetaCuspHawkingBackreactionResonantMode,
    0 < thetaCuspHawkingBackreactionHorizonCharge r →
      ∃ q : XiRightZeroCopy,
        xiSpectralPoint q.1 = -r.1 ∧
        xiRightSourceModularCharge q =
          thetaCuspHawkingBackreactionHorizonCharge r ∧
        thetaCuspHawkingBackreactionPortDissipation r =
          2 * thetaSource.mass * xiRightSourceModularCharge q *
            thetaCuspHawkingBackreactionPhysicalEnergy r ∧
        XiRightSourceModularTypeSuperselectionCertificate q ∧
        ∀ p : Nat.Primes,
          thetaCuspHawkingChargedDoubleKMSSwapUnitary
              (thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p) =
            thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p ∧
          ¬ ThetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned r p ∧
          ∀ (K : ℕ) (R : ℕ → (ℝ →L[ℝ] ℝ)),
            ReesOperatorGradeAtMost atTop primeWoldBoundaryVolumeBelow K R →
              (fun N =>
                R N
                  (primeValuationSquaredHellingerBelow
                    (thetaCuspHawkingBackreactionHorizonCharge r) N)) ≠
                primeValuationSquaredHellingerBelow
                  (-thetaCuspHawkingBackreactionHorizonCharge r)

/-- **[REPRESENTATION FRACTURE NO-GO]** Scalar modular superselection does not exclude the
explicit charged thermofield completion: its no-sewing law and exact doubled-space unitary charge
swap hold simultaneously at every positive source charge. -/
theorem thetaCuspHawkingModularSuperselectionChargedUnitaryBypass :
    ThetaCuspHawkingModularSuperselectionChargedUnitaryBypass := by
  intro r hpos
  obtain ⟨q, hspectral, hcharge, hport, hcert⟩ :=
    thetaCuspHawkingBackreaction_modularSuperselection_certificate r hpos
  refine ⟨q, hspectral, hcharge, hport, hcert, ?_⟩
  intro p
  refine ⟨thetaCuspHawkingChargedDoubleKMSSwapUnitary_visible_eq_partner r p, ?_, ?_⟩
  · exact
      (thetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned_iff_horizonCharge_zero
        r p).not.mpr hpos.ne'
  · intro K R hR
    exact no_finiteReesOperator_sews_positive_thetaCuspHawkingHorizon r hpos K R hR

end RHTower
