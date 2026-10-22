import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHartleHawkingDoubleKMSEndpoint
import GaloisForLFunctions.HTGeometry.WoldThermofieldStandardForm

/-!
# Charged double-KMS sector-swap no-go

The existing occupation-aligned Hartle--Hawking diagnostic is equivalent to RH but explicitly
leaves open whether real theta-mirror dynamics forces that alignment. This module constructs the
strongest charged-sector escape using actual normalized `lp` thermofield vectors.

Visible and reflected geometric KMS half-densities are tensorized in opposite charge orders. Both
vectors have norm one. Their squared Schmidt coefficients agree unconditionally after swapping the
two charge occupations, even when the arithmetic ratios differ. Agreement without the charge swap
holds exactly when the two ratios agree, hence exactly at neutral horizon charge; universally it is
RH.

Therefore abstract double-KMS purity and wedge reflection do not supply the missing alignment.
Any viable HB producer must exclude independent charge-conjugate sectors or couple them through a
source-faithful phase/Ward law.

`[NEW] [CHARGED TFD] [SECTOR SWAP] [PURITY NO-GO] [NO-SWAP IFF RH]`
-/

open Complex
open GaloisForLFunctions

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem norm_geometricOccupationHalfDensity_apply_sq
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (k : ℕ) :
    ‖geometricOccupationHalfDensity a ha0 ha1 k‖ ^ (2 : ℕ) =
      geometricOccupationProbability a k := by
  rw [geometricOccupationHalfDensity_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (geometricOccupationProbability_nonneg ha0 ha1 k)]

/-- Visible charged double-KMS half-density: positive then negative charge sector. -/
def thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) :
    lp (fun _ : ℕ × ℕ => ℂ) 2 :=
  lpTensorProductVector
    (geometricOccupationHalfDensity
      (thetaCuspHawkingPrimeVisibleKMSRatio r p)
      (thetaCuspHawkingPrimeVisibleKMSRatio_pos r p).le
      (thetaCuspHawkingPrimeVisibleKMSRatio_lt_one r p))
    (geometricOccupationHalfDensity
      (thetaCuspHawkingPrimePartnerKMSRatio r p)
      (thetaCuspHawkingPrimePartnerKMSRatio_pos r p).le
      (thetaCuspHawkingPrimePartnerKMSRatio_lt_one r p))

/-- Reflected charged double-KMS half-density with charge factors exchanged. -/
def thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) :
    lp (fun _ : ℕ × ℕ => ℂ) 2 :=
  lpTensorProductVector
    (geometricOccupationHalfDensity
      (thetaCuspHawkingPrimePartnerKMSRatio r p)
      (thetaCuspHawkingPrimePartnerKMSRatio_pos r p).le
      (thetaCuspHawkingPrimePartnerKMSRatio_lt_one r p))
    (geometricOccupationHalfDensity
      (thetaCuspHawkingPrimeVisibleKMSRatio r p)
      (thetaCuspHawkingPrimeVisibleKMSRatio_pos r p).le
      (thetaCuspHawkingPrimeVisibleKMSRatio_lt_one r p))

theorem norm_sq_thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) :
    ‖thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p‖ ^ (2 : ℕ) = 1 := by
  rw [thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity,
    norm_sq_lpTensorProductVector,
    norm_sq_geometricOccupationHalfDensity,
    norm_sq_geometricOccupationHalfDensity, mul_one]

theorem norm_sq_thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) :
    ‖thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p‖ ^ (2 : ℕ) = 1 := by
  rw [thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity,
    norm_sq_lpTensorProductVector,
    norm_sq_geometricOccupationHalfDensity,
    norm_sq_geometricOccupationHalfDensity, mul_one]

theorem norm_sq_thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity_apply
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) (k l : ℕ) :
    ‖thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p (k, l)‖ ^ (2 : ℕ) =
      thetaCuspHawkingPrimeGeometricKMSMass
          (thetaCuspHawkingPrimeVisibleKMSRatio r p) k *
        thetaCuspHawkingPrimeGeometricKMSMass
          (thetaCuspHawkingPrimePartnerKMSRatio r p) l := by
  rw [thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity,
    lpTensorProductVector_apply, norm_mul, mul_pow,
    norm_geometricOccupationHalfDensity_apply_sq,
    norm_geometricOccupationHalfDensity_apply_sq]
  rfl

theorem norm_sq_thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity_apply
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) (k l : ℕ) :
    ‖thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p (k, l)‖ ^ (2 : ℕ) =
      thetaCuspHawkingPrimeGeometricKMSMass
          (thetaCuspHawkingPrimePartnerKMSRatio r p) k *
        thetaCuspHawkingPrimeGeometricKMSMass
          (thetaCuspHawkingPrimeVisibleKMSRatio r p) l := by
  rw [thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity,
    lpTensorProductVector_apply, norm_mul, mul_pow,
    norm_geometricOccupationHalfDensity_apply_sq,
    norm_geometricOccupationHalfDensity_apply_sq]
  rfl

/-- Charged double-KMS Schmidt masses always agree after swapping the two charge occupations. -/
theorem thetaCuspHawkingPrimeChargedDoubleKMS_chargeSwap_isospectral
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) (k l : ℕ) :
    ‖thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p (k, l)‖ ^ (2 : ℕ) =
      ‖thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p (l, k)‖ ^ (2 : ℕ) := by
  rw [norm_sq_thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity_apply,
    norm_sq_thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity_apply]
  ring

/-- Occupation-preserving matching without charge swap. -/
def ThetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) : Prop :=
  ∀ k l : ℕ,
    ‖thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p (k, l)‖ ^ (2 : ℕ) =
      ‖thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p (k, l)‖ ^ (2 : ℕ)

theorem thetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned_iff_ratio_eq
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) :
    ThetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned r p ↔
      thetaCuspHawkingPrimeVisibleKMSRatio r p =
        thetaCuspHawkingPrimePartnerKMSRatio r p := by
  constructor
  · intro halign
    have h := halign 1 0
    rw [norm_sq_thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity_apply,
      norm_sq_thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity_apply,
      thetaCuspHawkingPrimeGeometricKMSMass,
      thetaCuspHawkingPrimeGeometricKMSMass,
      thetaCuspHawkingPrimeGeometricKMSMass,
      thetaCuspHawkingPrimeGeometricKMSMass] at h
    simp only [pow_one, pow_zero, mul_one] at h
    have hv : 0 < 1 - thetaCuspHawkingPrimeVisibleKMSRatio r p :=
      sub_pos.mpr (thetaCuspHawkingPrimeVisibleKMSRatio_lt_one r p)
    have hp : 0 < 1 - thetaCuspHawkingPrimePartnerKMSRatio r p :=
      sub_pos.mpr (thetaCuspHawkingPrimePartnerKMSRatio_lt_one r p)
    have hfactor :
        ((1 - thetaCuspHawkingPrimeVisibleKMSRatio r p) *
          (1 - thetaCuspHawkingPrimePartnerKMSRatio r p)) *
            thetaCuspHawkingPrimeVisibleKMSRatio r p =
        ((1 - thetaCuspHawkingPrimeVisibleKMSRatio r p) *
          (1 - thetaCuspHawkingPrimePartnerKMSRatio r p)) *
            thetaCuspHawkingPrimePartnerKMSRatio r p := by
      nlinarith
    exact mul_left_cancel₀ (mul_ne_zero hv.ne' hp.ne') hfactor
  · intro hratio k l
    rw [norm_sq_thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity_apply,
      norm_sq_thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity_apply,
      hratio]

theorem thetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned_iff_horizonCharge_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) :
    ThetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned r p ↔
      thetaCuspHawkingBackreactionHorizonCharge r = 0 :=
  (thetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned_iff_ratio_eq r p).trans
    (thetaCuspHawkingPrimeKMSRatio_eq_iff_horizonCharge_zero r p)

/-- Charge-swap Schmidt matching is unconditional over all theta resonances and prime channels. -/
def ThetaCuspHawkingChargedDoubleKMSChargeSwapCompletable : Prop :=
  ∀ (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) (k l : ℕ),
    ‖thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p (k, l)‖ ^ (2 : ℕ) =
      ‖thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p (l, k)‖ ^ (2 : ℕ)

theorem thetaCuspHawkingChargedDoubleKMSChargeSwapCompletable :
    ThetaCuspHawkingChargedDoubleKMSChargeSwapCompletable := by
  intro r p k l
  exact thetaCuspHawkingPrimeChargedDoubleKMS_chargeSwap_isospectral r p k l

/-- Universal no-swap charge-sector alignment. -/
def ThetaCuspHawkingChargedDoubleKMSOccupationAligned : Prop :=
  ∀ (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes),
    ThetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned r p

/-- Charge sectors recover the RH endpoint only when occupation labels may not be swapped. -/
theorem thetaCuspHawkingChargedDoubleKMSOccupationAligned_iff_riemannHypothesis :
    ThetaCuspHawkingChargedDoubleKMSOccupationAligned ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_thetaCuspHawkingBackreactionResonances_real]
  constructor
  · intro halign alpha hres
    let r : ThetaCuspHawkingBackreactionResonantMode := ⟨alpha, hres⟩
    have hzero :=
      (thetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned_iff_horizonCharge_zero
        r ⟨2, Nat.prime_two⟩).1 (halign r ⟨2, Nat.prime_two⟩)
    rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im] at hzero
    exact hzero
  · intro hreal r p
    apply
      (thetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned_iff_horizonCharge_zero r p).2
    rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im]
    exact hreal r.1 r.2

end RHTower
