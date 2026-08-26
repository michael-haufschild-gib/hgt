import GaloisForLFunctions.RHTower.ThetaCuspHawkingDarbouxHorizonCayleyReflectionRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullEinsteinGaugeFixedRadiationGram

/-!
# Darboux horizon phase mismatch as orthogonal-helicity optical flux

Let `c` and `d` be reflected Birmingham--Mokhtari horizon algebraic weights and let
`y = 12 |A_H|² omega` be real absorbed-horizon drive.  Exact Cayley subtraction gives

`|S(c,y)-S(d,y)|² = 4 y²(d-c)² / ((c²+y²)(d²+y²))`.

For a Xi divisor `rho=a+ib`, the reflected weight defect is
`d-c=4a(1-a)(1-2a)`, while the de-aliased Teukolsky orthogonal-helicity coefficient has energy
`b²(1-2a)²`.  Their combination produces a division-free optical identity.  Transport through
the exact gauge-fixed BM horizon-plus-boundary radiation map preserves it and makes the phase
mismatch energy equal to zero exactly on the critical line for every nonzero absorbed source and
real frequency, independently of the opposite-helicity source amplitude.

This identifies the exact optical price of coherent horizon phase mismatch.  It does not assert
that the total nonlinear `++-` Schur section equals the horizon channel.

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real Set Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

theorem d4DarbouxCayleyDenominator_ne_zero
    {c y : ℝ} (hc : c ≠ 0) :
    (c : ℂ) - Complex.I * (y : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  exact hc hre

theorem d4DarbouxCayleyPhase_sub_eq
    {c d y : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    d4DarbouxCayleyPhase c y - d4DarbouxCayleyPhase d y =
      (2 * Complex.I * (y : ℂ) * ((d - c : ℝ) : ℂ)) /
        (((c : ℂ) - Complex.I * (y : ℂ)) *
          ((d : ℂ) - Complex.I * (y : ℂ))) := by
  have hcden := d4DarbouxCayleyDenominator_ne_zero (y := y) hc
  have hdden := d4DarbouxCayleyDenominator_ne_zero (y := y) hd
  unfold d4DarbouxCayleyPhase
  field_simp [hcden, hdden]
  push_cast
  ring

def d4DarbouxCayleyPhaseMismatch (c d y : ℝ) : ℝ :=
  Complex.normSq (d4DarbouxCayleyPhase c y - d4DarbouxCayleyPhase d y)

theorem d4DarbouxCayleyPhaseMismatch_eq
    {c d y : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    d4DarbouxCayleyPhaseMismatch c d y =
      4 * y ^ 2 * (d - c) ^ 2 /
        ((c ^ 2 + y ^ 2) * (d ^ 2 + y ^ 2)) := by
  rw [d4DarbouxCayleyPhaseMismatch,
    d4DarbouxCayleyPhase_sub_eq hc hd,
    Complex.normSq_div]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I]
  norm_num [Complex.normSq_apply]
  ring

theorem d4DarbouxCayleyPhaseMismatch_scaled_eq
    {c d y : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) :
    (c ^ 2 + y ^ 2) * (d ^ 2 + y ^ 2) *
        d4DarbouxCayleyPhaseMismatch c d y =
      4 * y ^ 2 * (d - c) ^ 2 := by
  rw [d4DarbouxCayleyPhaseMismatch_eq hc hd]
  have hcpos : 0 < c ^ 2 + y ^ 2 := by
    have : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    nlinarith [sq_nonneg y]
  have hdpos : 0 < d ^ 2 + y ^ 2 := by
    have : 0 < d ^ 2 := sq_pos_of_ne_zero hd
    nlinarith [sq_nonneg y]
  field_simp [ne_of_gt hcpos, ne_of_gt hdpos]

theorem normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_tilt
    (q : XiZeroCopy) :
    Complex.normSq (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) =
      (q.1 : ℂ).im ^ 2 * (1 - 2 * (q.1 : ℂ).re) ^ 2 := by
  rw [normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient,
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq]
  simp [xiSpectralPoint, pow_two, Complex.mul_im]
  ring

def d4BMXiAbsorbedHorizonDarbouxPhaseMismatch
    (q : XiZeroCopy) (horizonAmplitude omega : ℝ) : ℝ :=
  Complex.normSq
    (d4BMXiAbsorbedHorizonDarbouxSMatrix q horizonAmplitude omega -
      d4BMXiAbsorbedHorizonDarbouxSMatrix (xiZeroCopyReflectEquiv q)
        horizonAmplitude omega)

/-- Division-free local optical law relating horizon phase mismatch to angular helicity energy. -/
theorem d4BMXiAbsorbedHorizonDarbouxPhaseMismatch_optical_eq
    (q : XiZeroCopy) (horizonAmplitude omega : ℝ) :
    let a := (q.1 : ℂ).re
    let b := (q.1 : ℂ).im
    let c := d4BMXiHorizonDarbouxAlgebraicWeight q
    let d := d4BMXiHorizonDarbouxAlgebraicWeight (xiZeroCopyReflectEquiv q)
    let y := 12 * horizonAmplitude ^ 2 * omega
    b ^ 2 * (c ^ 2 + y ^ 2) * (d ^ 2 + y ^ 2) *
        d4BMXiAbsorbedHorizonDarbouxPhaseMismatch q horizonAmplitude omega =
      64 * y ^ 2 * a ^ 2 * (1 - a) ^ 2 *
        Complex.normSq (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) := by
  dsimp only
  let a : ℝ := (q.1 : ℂ).re
  let b : ℝ := (q.1 : ℂ).im
  let c : ℝ := d4BMXiHorizonDarbouxAlgebraicWeight q
  let d : ℝ := d4BMXiHorizonDarbouxAlgebraicWeight (xiZeroCopyReflectEquiv q)
  let y : ℝ := 12 * horizonAmplitude ^ 2 * omega
  have hc : c ≠ 0 := ne_of_lt (d4BMXiHorizonDarbouxAlgebraicWeight_neg q)
  have hd : d ≠ 0 := ne_of_lt
    (d4BMXiHorizonDarbouxAlgebraicWeight_neg (xiZeroCopyReflectEquiv q))
  have hphase := d4DarbouxCayleyPhaseMismatch_scaled_eq (y := y) hc hd
  have hdc : d - c = 4 * a * (1 - a) * (1 - 2 * a) := by
    dsimp [a, c, d]
    linarith [d4BMXiHorizonDarbouxAlgebraicWeight_sub_reflect_eq q]
  have hmix := normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_tilt q
  change Complex.normSq (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) =
      b ^ 2 * (1 - 2 * a) ^ 2 at hmix
  change b ^ 2 * (c ^ 2 + y ^ 2) * (d ^ 2 + y ^ 2) *
        d4BMXiAbsorbedHorizonDarbouxPhaseMismatch q horizonAmplitude omega =
      64 * y ^ 2 * a ^ 2 * (1 - a) ^ 2 *
        Complex.normSq (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q)
  have hmismatch :
      d4BMXiAbsorbedHorizonDarbouxPhaseMismatch q horizonAmplitude omega =
        d4DarbouxCayleyPhaseMismatch c d y := by
    unfold d4BMXiAbsorbedHorizonDarbouxPhaseMismatch
      d4DarbouxCayleyPhaseMismatch
    rw [d4BMXiAbsorbedHorizonDarbouxSMatrix_eq_phase,
      d4BMXiAbsorbedHorizonDarbouxSMatrix_eq_phase]
  rw [hmismatch, hmix]
  rw [hdc] at hphase
  nlinarith [hphase]

variable {H K : Type*}
  [AddCommMonoid H] [Module ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

def d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy
    (radiation : H →ₗ[ℂ] K) (psi : H) (q : XiZeroCopy)
    (horizonAmplitude omega : ℝ) : ℝ :=
  d4BMXiAbsorbedHorizonDarbouxPhaseMismatch q horizonAmplitude omega *
    ‖radiation psi‖ ^ 2

def d4BMXiTransportedOrthogonalHelicityMixingFlux
    (radiation : H →ₗ[ℂ] K) (psi : H) (q : XiZeroCopy) : ℝ :=
  Complex.normSq (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) *
    ‖radiation psi‖ ^ 2

/-- Radiation transport turns local phase mismatch into exact orthogonal-helicity flux. -/
theorem d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy_optical_eq
    (radiation : H →ₗ[ℂ] K) (psi : H) (q : XiZeroCopy)
    (horizonAmplitude omega : ℝ) :
    let a := (q.1 : ℂ).re
    let b := (q.1 : ℂ).im
    let c := d4BMXiHorizonDarbouxAlgebraicWeight q
    let d := d4BMXiHorizonDarbouxAlgebraicWeight (xiZeroCopyReflectEquiv q)
    let y := 12 * horizonAmplitude ^ 2 * omega
    b ^ 2 * (c ^ 2 + y ^ 2) * (d ^ 2 + y ^ 2) *
        d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy
          radiation psi q horizonAmplitude omega =
      64 * y ^ 2 * a ^ 2 * (1 - a) ^ 2 *
        d4BMXiTransportedOrthogonalHelicityMixingFlux radiation psi q := by
  dsimp only
  rw [d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy,
    d4BMXiTransportedOrthogonalHelicityMixingFlux]
  have h := d4BMXiAbsorbedHorizonDarbouxPhaseMismatch_optical_eq
    q horizonAmplitude omega
  dsimp only at h
  nlinarith [h, sq_nonneg ‖radiation psi‖]

theorem d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy_nonneg
    (radiation : H →ₗ[ℂ] K) (psi : H) (q : XiZeroCopy)
    (horizonAmplitude omega : ℝ) :
    0 ≤ d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy
      radiation psi q horizonAmplitude omega := by
  unfold d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy
    d4BMXiAbsorbedHorizonDarbouxPhaseMismatch
  exact mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)

theorem d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy_eq_zero_iff_flux
    (radiation : H →ₗ[ℂ] K) (psi : H) (q : XiZeroCopy)
    {horizonAmplitude omega : ℝ}
    (hamp : horizonAmplitude ≠ 0) (homega : omega ≠ 0) :
    d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy
        radiation psi q horizonAmplitude omega = 0 ↔
      d4BMXiTransportedOrthogonalHelicityMixingFlux radiation psi q = 0 := by
  let a : ℝ := (q.1 : ℂ).re
  let b : ℝ := (q.1 : ℂ).im
  let c : ℝ := d4BMXiHorizonDarbouxAlgebraicWeight q
  let d : ℝ := d4BMXiHorizonDarbouxAlgebraicWeight (xiZeroCopyReflectEquiv q)
  let y : ℝ := 12 * horizonAmplitude ^ 2 * omega
  have ha := xi_divisor_support_re_mem_open_unit q.1
  have hb : b ≠ 0 := by simpa [b] using xi_divisor_support_im_ne_zero q.1
  have hc : c ≠ 0 := ne_of_lt (d4BMXiHorizonDarbouxAlgebraicWeight_neg q)
  have hd : d ≠ 0 := ne_of_lt
    (d4BMXiHorizonDarbouxAlgebraicWeight_neg (xiZeroCopyReflectEquiv q))
  have hy : y ≠ 0 := by
    dsimp [y]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hamp)) homega
  have hleft : 0 < b ^ 2 * (c ^ 2 + y ^ 2) * (d ^ 2 + y ^ 2) := by
    positivity
  have hright : 0 < 64 * y ^ 2 * a ^ 2 * (1 - a) ^ 2 := by
    have ha0 : 0 < a := by simpa [a] using ha.1
    have ha1 : a < 1 := by simpa [a] using ha.2
    positivity
  have hlaw :=
    d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy_optical_eq
      radiation psi q horizonAmplitude omega
  dsimp only at hlaw
  change
    b ^ 2 * (c ^ 2 + y ^ 2) * (d ^ 2 + y ^ 2) *
        d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy
          radiation psi q horizonAmplitude omega =
      64 * y ^ 2 * a ^ 2 * (1 - a) ^ 2 *
        d4BMXiTransportedOrthogonalHelicityMixingFlux radiation psi q at hlaw
  constructor
  · intro hzero
    have hprod :
        (64 * y ^ 2 * a ^ 2 * (1 - a) ^ 2) *
          d4BMXiTransportedOrthogonalHelicityMixingFlux radiation psi q = 0 := by
      rw [← hlaw, hzero]
      ring
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hright)
  · intro hzero
    have hprod :
        (b ^ 2 * (c ^ 2 + y ^ 2) * (d ^ 2 + y ^ 2)) *
          d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy
            radiation psi q horizonAmplitude omega = 0 := by
      rw [hlaw, hzero]
      ring
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hleft)

theorem d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy_eq_zero_iff_line
    (radiation : H →ₗ[ℂ] K) (psi : H) (q : XiZeroCopy)
    {horizonAmplitude omega : ℝ}
    (hamp : horizonAmplitude ≠ 0) (homega : omega ≠ 0)
    (hradiates : radiation psi ≠ 0) :
    d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy
        radiation psi q horizonAmplitude omega = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy_eq_zero_iff_flux
      radiation psi q hamp homega,
    show d4BMXiTransportedOrthogonalHelicityMixingFlux radiation psi q = 0 ↔
        (q.1 : ℂ).re = 1 / 2 by
      unfold d4BMXiTransportedOrthogonalHelicityMixingFlux
      rw [normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient]
      exact d4ThetaTeukolskyOrthogonalHelicityMixingEnergy_eq_zero_iff
        (radiation psi) hradiates q]

/-- Full-Einstein BM radiation map obeys the phase-to-mixing optical law for every source. -/
theorem d4BMXiFullEinsteinAbsorbedHorizonPhaseMixingOpticalLaw
    (q : XiZeroCopy) (horizonAmplitude omega : ℝ) (orthogonalMixing : ℂ) :
    let a := (q.1 : ℂ).re
    let b := (q.1 : ℂ).im
    let c := d4BMXiHorizonDarbouxAlgebraicWeight q
    let d := d4BMXiHorizonDarbouxAlgebraicWeight (xiZeroCopyReflectEquiv q)
    let y := 12 * horizonAmplitude ^ 2 * omega
    let source : ℂ × ℂ :=
      (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient (horizonAmplitude : ℂ)
        (xiSpectralPoint q), orthogonalMixing)
    b ^ 2 * (c ^ 2 + y ^ 2) * (d ^ 2 + y ^ 2) *
        d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy
          (d4BMGaugeFixedSecondHarmonicRadiationMap q) source q
          horizonAmplitude omega =
      64 * y ^ 2 * a ^ 2 * (1 - a) ^ 2 *
        d4BMXiTransportedOrthogonalHelicityMixingFlux
          (d4BMGaugeFixedSecondHarmonicRadiationMap q) source q := by
  dsimp only
  exact d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy_optical_eq
    (d4BMGaugeFixedSecondHarmonicRadiationMap q)
    (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient (horizonAmplitude : ℂ)
      (xiSpectralPoint q), orthogonalMixing)
    q horizonAmplitude omega

theorem d4BMXiFullEinsteinAbsorbedHorizonPhaseMismatchEnergy_eq_zero_iff
    (q : XiZeroCopy) {horizonAmplitude omega : ℝ} (orthogonalMixing : ℂ)
    (hamp : horizonAmplitude ≠ 0) (homega : omega ≠ 0) :
    d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy
        (d4BMGaugeFixedSecondHarmonicRadiationMap q)
        (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient (horizonAmplitude : ℂ)
          (xiSpectralPoint q), orthogonalMixing)
        q horizonAmplitude omega = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have ha : (horizonAmplitude : ℂ) ≠ 0 := by exact_mod_cast hamp
  have hradiates := d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation_ne_zero
    ha q orthogonalMixing
  exact d4BMXiAbsorbedHorizonDarbouxPhaseMismatchRadiationEnergy_eq_zero_iff_line
    (d4BMGaugeFixedSecondHarmonicRadiationMap q)
    (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient (horizonAmplitude : ℂ)
      (xiSpectralPoint q), orthogonalMixing)
    q hamp homega hradiates

end

end RHTower
