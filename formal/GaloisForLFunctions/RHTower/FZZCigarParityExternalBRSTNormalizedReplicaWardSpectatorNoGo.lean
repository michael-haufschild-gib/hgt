import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBalancedGammaWardDelayRigidity

/-!
# FZZ normalized replica-Ward external-Gamma spectator no-go

Halder--Jafferis' replica-area insertion differentiates the winding source, whereas the external
Gamma normalizations are replica-independent factors.  This module proves that every normalized
replica Ward profile cancels such a factor exactly.  It then exhibits a full one-parameter family
of entire, nonzero, centered, Schwarz-compatible, reflection-reciprocal normalizations which are
unit-modulus on the physical line but add a cubic phase and a quadratic delay shift.

Consequently the canonical and a fitted admissible frame have the same complete normalized
replica-Ward profile and opposite vacuum-delay saturation truth values at a nonzero momentum.  No
predicate of that profile can supply the FZZ external-Gamma delay endpoint uniformly over the
normalization orbit.  The positive survivor is a mixed replica--momentum correlator or an
independently fixed asymptotic phase frame.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Entire cubic phase normalization centered at the critical line. -/
def fzzHJReciprocalCubicExternalGammaNormalization (c : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(c : ℂ) * (s - (1 / 2 : ℂ)) ^ 3)

/-- Exact normalization class preserved by the no-go witness. -/
def FZZHJAdmissibleExternalGammaNormalization (H : ℂ → ℂ) : Prop :=
  (∀ s, H s ≠ 0) ∧
    (∀ s, star (H s) = H (star s)) ∧
    (∀ s, H (1 - s) * H s = 1) ∧
    H (1 / 2 : ℂ) = 1 ∧
    ∀ P : ℝ, ‖H ((1 / 2 : ℂ) + (P : ℂ) * I)‖ = 1

theorem fzzHJReciprocalCubicExternalGammaNormalization_ne_zero
    (c : ℝ) (s : ℂ) :
    fzzHJReciprocalCubicExternalGammaNormalization c s ≠ 0 :=
  Complex.exp_ne_zero _

theorem fzzHJReciprocalCubicExternalGammaNormalization_schwarz
    (c : ℝ) (s : ℂ) :
    star (fzzHJReciprocalCubicExternalGammaNormalization c s) =
      fzzHJReciprocalCubicExternalGammaNormalization c (star s) := by
  change (starRingEnd ℂ)
      (Complex.exp (-(c : ℂ) * (s - (1 / 2 : ℂ)) ^ 3)) = _
  rw [← Complex.exp_conj]
  apply congrArg Complex.exp
  have hc : star (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
  simp only [map_mul, map_neg, map_pow, map_sub, div_eq_mul_inv, map_one,
    map_inv₀, map_ofNat, starRingEnd_apply, hc]

theorem fzzHJReciprocalCubicExternalGammaNormalization_reflection
    (c : ℝ) (s : ℂ) :
    fzzHJReciprocalCubicExternalGammaNormalization c (1 - s) *
        fzzHJReciprocalCubicExternalGammaNormalization c s = 1 := by
  unfold fzzHJReciprocalCubicExternalGammaNormalization
  rw [← Complex.exp_add]
  conv_rhs => rw [← Complex.exp_zero]
  apply congrArg Complex.exp
  ring

@[simp] theorem fzzHJReciprocalCubicExternalGammaNormalization_center
    (c : ℝ) :
    fzzHJReciprocalCubicExternalGammaNormalization c (1 / 2 : ℂ) = 1 := by
  simp [fzzHJReciprocalCubicExternalGammaNormalization]

theorem fzzHJReciprocalCubicExternalGammaNormalization_criticalLine
    (c P : ℝ) :
    fzzHJReciprocalCubicExternalGammaNormalization c
        ((1 / 2 : ℂ) + (P : ℂ) * I) =
      Complex.exp (I * ((c * P ^ 3 : ℝ) : ℂ)) := by
  unfold fzzHJReciprocalCubicExternalGammaNormalization
  apply congrArg Complex.exp
  push_cast
  ring_nf
  have hI : I ^ 3 = -(I : ℂ) := by
    calc
      I ^ 3 = I ^ 2 * I := by ring
      _ = -I := by rw [Complex.I_sq]; ring
  rw [hI]
  ring

theorem norm_fzzHJReciprocalCubicExternalGammaNormalization_criticalLine
    (c P : ℝ) :
    ‖fzzHJReciprocalCubicExternalGammaNormalization c
        ((1 / 2 : ℂ) + (P : ℂ) * I)‖ = 1 := by
  rw [fzzHJReciprocalCubicExternalGammaNormalization_criticalLine,
    Complex.norm_exp]
  have hre : (I * ((c * P ^ 3 : ℝ) : ℂ)).re = 0 := by
    rw [mul_re]
    simp only [I_re, I_im, ofReal_re, ofReal_im]
    ring
  rw [hre]
  simp

theorem fzzHJReciprocalCubicExternalGammaNormalization_admissible
    (c : ℝ) :
    FZZHJAdmissibleExternalGammaNormalization
      (fzzHJReciprocalCubicExternalGammaNormalization c) := by
  exact ⟨fzzHJReciprocalCubicExternalGammaNormalization_ne_zero c,
    fzzHJReciprocalCubicExternalGammaNormalization_schwarz c,
    fzzHJReciprocalCubicExternalGammaNormalization_reflection c,
    fzzHJReciprocalCubicExternalGammaNormalization_center c,
    norm_fzzHJReciprocalCubicExternalGammaNormalization_criticalLine c⟩

/-- Correlator with a replica-independent external factor and a replica-dependent core. -/
def fzzHJFactorizedReplicaAmplitude
    (G : ℝ → ℂ) (C : ℝ → ℂ → ℂ) (δ : ℂ) (P : ℝ) : ℂ :=
  G P * C P δ

/-- Replica differentiation leaves the external factor as a spectator. -/
theorem hasDerivAt_fzzHJFactorizedReplicaAmplitude
    (G : ℝ → ℂ) (C : ℝ → ℂ → ℂ) (δ : ℂ) (P : ℝ) (D : ℂ)
    (hC : HasDerivAt (C P) D δ) :
    HasDerivAt (fun ε : ℂ => fzzHJFactorizedReplicaAmplitude G C ε P)
      (G P * D) δ := by
  simpa [fzzHJFactorizedReplicaAmplitude] using hC.const_mul (G P)

/-- Normalized replica-Ward profile supplied by factorized value and replica velocity. -/
def fzzHJFactorizedNormalizedReplicaWardProfile
    (G C D : ℝ → ℂ) (P : ℝ) : ℂ :=
  G P * D P / (G P * C P)

/-- Exact spectator cancellation: the full normalized Ward profile is the core profile. -/
theorem fzzHJFactorizedNormalizedReplicaWardProfile_eq_core
    (G C D : ℝ → ℂ) (hG : ∀ P, G P ≠ 0) (hC : ∀ P, C P ≠ 0) :
    fzzHJFactorizedNormalizedReplicaWardProfile G C D =
      fun P => D P / C P := by
  funext P
  unfold fzzHJFactorizedNormalizedReplicaWardProfile
  field_simp [hG P, hC P]

/-- External factor after an admissible cubic normalization change. -/
def fzzHJReciprocalCubicGaugedExternalFactor
    (c : ℝ) (G : ℝ → ℂ) (P : ℝ) : ℂ :=
  fzzHJReciprocalCubicExternalGammaNormalization c
      ((1 / 2 : ℂ) + (P : ℂ) * I) * G P

theorem fzzHJReciprocalCubicGaugedExternalFactor_ne_zero
    (c : ℝ) (G : ℝ → ℂ) (hG : ∀ P, G P ≠ 0) (P : ℝ) :
    fzzHJReciprocalCubicGaugedExternalFactor c G P ≠ 0 := by
  exact mul_ne_zero
    (fzzHJReciprocalCubicExternalGammaNormalization_ne_zero c _) (hG P)

theorem fzzHJFactorizedNormalizedReplicaWardProfile_cubicGauge
    (c : ℝ) (G C D : ℝ → ℂ)
    (hG : ∀ P, G P ≠ 0) (hC : ∀ P, C P ≠ 0) :
    fzzHJFactorizedNormalizedReplicaWardProfile
        (fzzHJReciprocalCubicGaugedExternalFactor c G) C D =
      fun P => D P / C P := by
  exact fzzHJFactorizedNormalizedReplicaWardProfile_eq_core _ C D
    (fzzHJReciprocalCubicGaugedExternalFactor_ne_zero c G hG) hC

/-- Balanced external-Gamma amplitude in the cubic normalization frame. -/
def fzzHJReciprocalCubicGaugedExternalGammaAmplitude
    (c P : ℝ) : ℂ :=
  fzzHJReciprocalCubicExternalGammaNormalization c
      ((1 / 2 : ℂ) + (P : ℂ) * I) *
    fzzHJBalancedExternalGammaAmplitude P

/-- Unwrapped balanced external-Gamma phase in the cubic normalization frame. -/
def fzzHJReciprocalCubicGaugedExternalGammaMomentumPhase
    (c P : ℝ) : ℝ :=
  fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * P) + c * P ^ 3

/-- The gauged complex amplitude is exactly the exponential of the gauged phase lift. -/
theorem fzzHJReciprocalCubicGaugedExternalGammaAmplitude_eq_exp_phase
    (c P : ℝ) :
    fzzHJReciprocalCubicGaugedExternalGammaAmplitude c P =
      Complex.exp (I *
        (fzzHJReciprocalCubicGaugedExternalGammaMomentumPhase c P : ℂ)) := by
  unfold fzzHJReciprocalCubicGaugedExternalGammaAmplitude
  rw [fzzHJReciprocalCubicExternalGammaNormalization_criticalLine,
    fzzHJBalancedExternalGammaAmplitude_eq_exp_phase, ← Complex.exp_add]
  apply congrArg Complex.exp
  unfold fzzHJReciprocalCubicGaugedExternalGammaMomentumPhase
  push_cast
  ring

/-- Local momentum delay in the cubic normalization frame. -/
def fzzHJReciprocalCubicGaugedExternalGammaWardDelay
    (c P : ℝ) : ℝ :=
  fzzHJBalancedExternalGammaWardDelay P + 3 * c * P ^ 2

theorem hasDerivAt_fzzHJReciprocalCubicGaugedExternalGammaMomentumPhase
    (c P : ℝ) :
    HasDerivAt
      (fzzHJReciprocalCubicGaugedExternalGammaMomentumPhase c)
      (fzzHJReciprocalCubicGaugedExternalGammaWardDelay c P) P := by
  have hcubic : HasDerivAt (fun Q : ℝ => c * Q ^ 3) (3 * c * P ^ 2) P := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_two,
      one_mul, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id P).pow 3).const_mul c
  exact (hasDerivAt_fzzHJBalancedExternalGammaMomentumPhase P).add hcubic

/-- Unique cubic coefficient which makes a prescribed nonzero momentum vacuum-delay saturated. -/
def fzzHJReciprocalCubicWardDelaySaturatingGauge (P : ℝ) : ℝ :=
  (fzzHJBalancedExternalGammaWardDelay 0 -
    fzzHJBalancedExternalGammaWardDelay P) / (3 * P ^ 2)

theorem fzzHJReciprocalCubicGaugedExternalGammaWardDelay_fit_saturates
    {P : ℝ} (hP : P ≠ 0) :
    fzzHJReciprocalCubicGaugedExternalGammaWardDelay
        (fzzHJReciprocalCubicWardDelaySaturatingGauge P) P =
      fzzHJReciprocalCubicGaugedExternalGammaWardDelay
        (fzzHJReciprocalCubicWardDelaySaturatingGauge P) 0 := by
  unfold fzzHJReciprocalCubicGaugedExternalGammaWardDelay
    fzzHJReciprocalCubicWardDelaySaturatingGauge
  have hsq : P ^ 2 ≠ 0 := pow_ne_zero 2 hP
  field_simp [hsq]
  ring

theorem fzzHJReciprocalCubicGaugedExternalGammaWardDelay_zeroGauge_not_saturates
    {P : ℝ} (hP : P ≠ 0) :
    fzzHJReciprocalCubicGaugedExternalGammaWardDelay 0 P ≠
      fzzHJReciprocalCubicGaugedExternalGammaWardDelay 0 0 := by
  simp only [fzzHJReciprocalCubicGaugedExternalGammaWardDelay, mul_zero,
    zero_mul, add_zero]
  exact (fzzHJBalancedExternalGammaWardDelay_zero_lt hP).ne'

/-- Proposed normalization-independent selector from the complete normalized replica-Ward profile. -/
structure FZZHJNormalizedReplicaWardExternalGammaSelector where
  externalFactor : ℝ → ℂ
  replicaCore : ℝ → ℂ
  replicaVelocity : ℝ → ℂ
  externalFactor_ne_zero : ∀ P, externalFactor P ≠ 0
  replicaCore_ne_zero : ∀ P, replicaCore P ≠ 0
  predicate : (ℝ → ℂ) → ℝ → Prop
  selects_saturation : ∀ c P,
    predicate
        (fzzHJFactorizedNormalizedReplicaWardProfile
          (fzzHJReciprocalCubicGaugedExternalFactor c externalFactor)
          replicaCore replicaVelocity) P ↔
      fzzHJReciprocalCubicGaugedExternalGammaWardDelay c P =
        fzzHJReciprocalCubicGaugedExternalGammaWardDelay c 0

/-- No complete normalized replica-Ward profile can select external-Gamma delay saturation over
the admissible cubic normalization orbit. -/
theorem no_fzzHJNormalizedReplicaWardExternalGammaSelector :
    ¬ Nonempty FZZHJNormalizedReplicaWardExternalGammaSelector := by
  rintro ⟨S⟩
  let c := fzzHJReciprocalCubicWardDelaySaturatingGauge 1
  have hprofile (a : ℝ) :
      fzzHJFactorizedNormalizedReplicaWardProfile
          (fzzHJReciprocalCubicGaugedExternalFactor a S.externalFactor)
          S.replicaCore S.replicaVelocity =
        fun P => S.replicaVelocity P / S.replicaCore P :=
    fzzHJFactorizedNormalizedReplicaWardProfile_cubicGauge
      a S.externalFactor S.replicaCore S.replicaVelocity
      S.externalFactor_ne_zero S.replicaCore_ne_zero
  have hzero :
      ¬ S.predicate
        (fzzHJFactorizedNormalizedReplicaWardProfile
          (fzzHJReciprocalCubicGaugedExternalFactor 0 S.externalFactor)
          S.replicaCore S.replicaVelocity) 1 := by
    intro h
    exact fzzHJReciprocalCubicGaugedExternalGammaWardDelay_zeroGauge_not_saturates
      (by norm_num : (1 : ℝ) ≠ 0) ((S.selects_saturation 0 1).mp h)
  have hfit :
      S.predicate
        (fzzHJFactorizedNormalizedReplicaWardProfile
          (fzzHJReciprocalCubicGaugedExternalFactor c S.externalFactor)
          S.replicaCore S.replicaVelocity) 1 :=
    (S.selects_saturation c 1).mpr
      (fzzHJReciprocalCubicGaugedExternalGammaWardDelay_fit_saturates
        (by norm_num : (1 : ℝ) ≠ 0))
  rw [hprofile c, ← hprofile 0] at hfit
  exact hzero hfit

/-- Closed FZZ-P route class: direct normalized replica Ward data cannot force the unframed
external-Gamma vacuum-delay endpoint. -/
def FZZHJNormalizedReplicaWardExternalGammaSpectatorRouteKilled : Prop :=
  (∀ c : ℝ, FZZHJAdmissibleExternalGammaNormalization
    (fzzHJReciprocalCubicExternalGammaNormalization c)) ∧
  ¬ Nonempty FZZHJNormalizedReplicaWardExternalGammaSelector

theorem fzzHJNormalizedReplicaWardExternalGammaSpectatorRouteKilled :
    FZZHJNormalizedReplicaWardExternalGammaSpectatorRouteKilled := by
  exact ⟨fzzHJReciprocalCubicExternalGammaNormalization_admissible,
    no_fzzHJNormalizedReplicaWardExternalGammaSelector⟩

end

end RHTower
