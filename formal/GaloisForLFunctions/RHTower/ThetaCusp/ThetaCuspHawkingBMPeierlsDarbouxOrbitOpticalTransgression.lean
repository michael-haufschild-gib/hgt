import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFESchwarzFixedWeightWardDichotomy
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingDarbouxHorizonPhaseMixingOpticalLaw

/-!
# Peierls--Darboux FE--Schwarz orbit optical transgression

The HC16 global Peierls orbit trace and the absorbed-horizon Darboux phase mismatch are exact
normalizations of the same orthogonal-helicity mixing invariant. This module proves their
coefficient-exact division-free transgression and transports it through arbitrary radiation maps.

The negative real Peierls trace becomes a nonnegative radiation power, strictly positive for every
radiating tilted Xi copy and zero exactly on the critical wall. The canonical unit-amplitude
full-Einstein reporter is premise-free: universal optical darkness is equivalent to RH and exactly
the same endpoint as HC17 equal-positive-weight Ward stationarity. Thus passive optical transport
does not supply stationarity off wall; it exposes a positive Ward defect.

`[NEW] [OPTICAL TRANSGRESSION] [STRICT PASSIVITY NO-GO] [EXACT RH ENDPOINT] [LEAN-PROVED]`
-/

open Complex Real Set Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

theorem hbXiPeierlsFESchwarzOrbitDarbouxPhaseMismatch_optical_eq
    (n : ℕ) (q : XiZeroCopy) (horizonAmplitude omega : ℝ) :
    let a := (q.1 : ℂ).re
    let b := (q.1 : ℂ).im
    let c := d4BMXiHorizonDarbouxAlgebraicWeight q
    let d := d4BMXiHorizonDarbouxAlgebraicWeight (xiZeroCopyReflectEquiv q)
    let y := 12 * horizonAmplitude ^ (2 : ℕ) * omega
    b ^ (2 : ℕ) * (c ^ (2 : ℕ) + y ^ (2 : ℕ)) * (d ^ (2 : ℕ) + y ^ (2 : ℕ)) *
        d4BMXiAbsorbedHorizonDarbouxPhaseMismatch q horizonAmplitude omega *
          (8 * (n : ℝ) + 5) =
      -16 * y ^ (2 : ℕ) * a ^ (2 : ℕ) * (1 - a) ^ (2 : ℕ) *
        (hbXiPeierlsFESchwarzOrbitCubicTrace n q).re := by
  dsimp only
  have hopt := d4BMXiAbsorbedHorizonDarbouxPhaseMismatch_optical_eq
    q horizonAmplitude omega
  dsimp only at hopt
  rw [hbXiPeierlsFESchwarzOrbitCubicTrace_eq]
  norm_num
  nlinarith [hopt]

variable {H K : Type*}
  [AddCommMonoid H] [Module ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- Positive optical power canonically extracted from the negative Peierls orbit trace. -/
def hbXiPeierlsFESchwarzOrbitRadiationPower
    (radiation : H →ₗ[ℂ] K) (psi : H) (n : ℕ) (q : XiZeroCopy) : ℝ :=
  -(hbXiPeierlsFESchwarzOrbitCubicTrace n q).re * ‖radiation psi‖ ^ (2 : ℕ)

theorem hbXiPeierlsFESchwarzOrbitRadiationPower_eq_flux
    (radiation : H →ₗ[ℂ] K) (psi : H) (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsFESchwarzOrbitRadiationPower radiation psi n q =
      4 * (8 * (n : ℝ) + 5) *
        d4BMXiTransportedOrthogonalHelicityMixingFlux radiation psi q := by
  rw [hbXiPeierlsFESchwarzOrbitRadiationPower,
    hbXiPeierlsFESchwarzOrbitCubicTrace_eq,
    d4BMXiTransportedOrthogonalHelicityMixingFlux]
  norm_num
  ring

theorem hbXiPeierlsFESchwarzOrbitRadiationPower_nonneg
    (radiation : H →ₗ[ℂ] K) (psi : H) (n : ℕ) (q : XiZeroCopy) :
    0 ≤ hbXiPeierlsFESchwarzOrbitRadiationPower radiation psi n q := by
  rw [hbXiPeierlsFESchwarzOrbitRadiationPower_eq_flux,
    d4BMXiTransportedOrthogonalHelicityMixingFlux]
  exact mul_nonneg (by positivity)
    (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))

theorem hbXiPeierlsFESchwarzOrbitRadiationPower_eq_zero_iff_line
    (radiation : H →ₗ[ℂ] K) (psi : H) (n : ℕ) (q : XiZeroCopy)
    (hradiates : radiation psi ≠ 0) :
    hbXiPeierlsFESchwarzOrbitRadiationPower radiation psi n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsFESchwarzOrbitRadiationPower_eq_flux]
  have hscale : (4 * (8 * (n : ℝ) + 5) : ℝ) ≠ 0 := by positivity
  rw [mul_eq_zero]
  simp only [hscale, false_or]
  unfold d4BMXiTransportedOrthogonalHelicityMixingFlux
  rw [normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient]
  exact d4ThetaTeukolskyOrthogonalHelicityMixingEnergy_eq_zero_iff
    (radiation psi) hradiates q

theorem hbXiPeierlsFESchwarzOrbitRadiationPower_pos_of_tilt
    (radiation : H →ₗ[ℂ] K) (psi : H) (n : ℕ) (q : XiZeroCopy)
    (hradiates : radiation psi ≠ 0) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < hbXiPeierlsFESchwarzOrbitRadiationPower radiation psi n q := by
  rw [hbXiPeierlsFESchwarzOrbitRadiationPower_eq_flux,
    d4BMXiTransportedOrthogonalHelicityMixingFlux]
  have hmix : d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q ≠ 0 :=
    (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).not.mpr htilt
  have hnormmix : 0 < Complex.normSq
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) :=
    Complex.normSq_pos.mpr hmix
  have hnormrad : 0 < ‖radiation psi‖ := norm_pos_iff.mpr hradiates
  positivity

theorem hbXiPeierlsFESchwarzOrbitDarbouxRadiation_optical_eq
    (radiation : H →ₗ[ℂ] K) (psi : H) (n : ℕ) (q : XiZeroCopy)
    (horizonAmplitude omega : ℝ) :
    let a := (q.1 : ℂ).re
    let b := (q.1 : ℂ).im
    let c := d4BMXiHorizonDarbouxAlgebraicWeight q
    let d := d4BMXiHorizonDarbouxAlgebraicWeight (xiZeroCopyReflectEquiv q)
    let y := 12 * horizonAmplitude ^ (2 : ℕ) * omega
    b ^ (2 : ℕ) * (c ^ (2 : ℕ) + y ^ (2 : ℕ)) * (d ^ (2 : ℕ) + y ^ (2 : ℕ)) *
        d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy
          radiation psi q horizonAmplitude omega * (8 * (n : ℝ) + 5) =
      16 * y ^ (2 : ℕ) * a ^ (2 : ℕ) * (1 - a) ^ (2 : ℕ) *
        hbXiPeierlsFESchwarzOrbitRadiationPower radiation psi n q := by
  dsimp only
  have hopt :=
    d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy_optical_eq
      radiation psi q horizonAmplitude omega
  dsimp only at hopt
  rw [hopt, hbXiPeierlsFESchwarzOrbitRadiationPower_eq_flux]
  ring

/-- Full-Einstein specialization of the orbit radiation power. -/
def hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower
    (n : ℕ) (q : XiZeroCopy) (horizonAmplitude : ℝ)
    (orthogonalMixing : ℂ) : ℝ :=
  hbXiPeierlsFESchwarzOrbitRadiationPower
    (d4BMGaugeFixedSecondHarmonicRadiationMap q)
    (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient (horizonAmplitude : ℂ)
      (xiSpectralPoint q), orthogonalMixing)
    n q

theorem hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower_eq_zero_iff_line
    (n : ℕ) (q : XiZeroCopy) {horizonAmplitude : ℝ}
    (orthogonalMixing : ℂ) (hamp : horizonAmplitude ≠ 0) :
    hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower
        n q horizonAmplitude orthogonalMixing = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  unfold hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower
  apply hbXiPeierlsFESchwarzOrbitRadiationPower_eq_zero_iff_line
  have ha : (horizonAmplitude : ℂ) ≠ 0 := by exact_mod_cast hamp
  exact d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation_ne_zero
    ha q orthogonalMixing

theorem forall_hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower_eq_zero_iff_rh
    (n : ℕ) {horizonAmplitude : ℝ} (orthogonalMixing : ℂ)
    (hamp : horizonAmplitude ≠ 0) :
    (∀ q : XiZeroCopy,
      hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower
        n q horizonAmplitude orthogonalMixing = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis
      n).mp
    intro q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mpr
    exact (hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower_eq_zero_iff_line
      n q orthogonalMixing hamp).mp (h q)
  · intro hRH q
    apply (hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower_eq_zero_iff_line
      n q orthogonalMixing hamp).mpr
    exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH) (q.1 : ℂ)
      (xi_eq_zero_of_mem_divisor_support q.1)

/-- Unit absorbed amplitude and zero auxiliary mixing give a premise-free physical reporter. -/
def hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower n q 1 0

theorem hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_line
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  exact hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower_eq_zero_iff_line
    n q 0 (by norm_num)

theorem forall_hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0) ↔
      RiemannHypothesis := by
  exact forall_hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower_eq_zero_iff_rh
    n 0 (by norm_num)

/-- HC17 positive Ward stationarity and canonical optical darkness are the same RH endpoint. -/
theorem hbXiPeierlsFESchwarzCanonicalOpticalWard_iff_positiveWard
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0) ↔
      HBXiPeierlsFESchwarzFixedWeightWardIdentity n 1 1 :=
  (forall_hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_rh n).trans
    (hbXiPeierlsFESchwarzPositiveWeightWardIdentity_iff_rh
      n 1 1 (by norm_num)).symm

end

end RHTower

