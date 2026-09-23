import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorCouplingWindingEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingKMSCayleyScatteringMixingEndpoint

/-!
# No-go for selecting unit Hawking coupling winding from generic dynamics

An explicit family of analytic delayed-onset Cayley blocks has arbitrary coupling order `m`, exact
two-port Hermitian conservation, exact Hawking KMS detailed balance, and strict mixing at every
nonzero real coupling.  At the same time its local complex-coupling phase winding is exactly `m`.

The quadratic member is therefore a closed countermodel to any claim that losslessness, KMS, and
nonperturbative nonzero-coupling mixing force unit winding.  The missing RH producer must use
theta-specific source structure or a genuinely stronger locality/minimality law.
-/

open Complex Real
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-- Cayley load with an arbitrary delayed coupling onset `m`. -/
def delayedHawkingCayleyLoad (m : ℕ) (lambda : ℝ) : ℝ :=
  lambda ^ (2 * m) / 4

def delayedHawkingCayleyRetention (m : ℕ) (lambda : ℝ) : ℝ :=
  (1 - delayedHawkingCayleyLoad m lambda) /
    (1 + delayedHawkingCayleyLoad m lambda)

def delayedHawkingCayleyTransition (m : ℕ) (lambda : ℝ) : ℂ :=
  ((lambda ^ m : ℝ) : ℂ) /
    ((1 + delayedHawkingCayleyLoad m lambda : ℝ) : ℂ)

theorem delayedHawkingCayleyLoad_nonneg (m : ℕ) (lambda : ℝ) :
    0 ≤ delayedHawkingCayleyLoad m lambda := by
  rw [delayedHawkingCayleyLoad]
  have hp : 0 ≤ (lambda ^ m) ^ (2 : ℕ) := sq_nonneg _
  rw [show lambda ^ (2 * m) = (lambda ^ m) ^ (2 : ℕ) by
    rw [pow_two, ← pow_add]
    congr 1
    omega]
  positivity

theorem delayedHawkingCayley_denominator_pos (m : ℕ) (lambda : ℝ) :
    0 < 1 + delayedHawkingCayleyLoad m lambda := by
  linarith [delayedHawkingCayleyLoad_nonneg m lambda]

/-- Exact two-port losslessness permits every positive onset order. -/
theorem delayedHawkingCayleyRetention_sq_add_transition_normSq
    (m : ℕ) (lambda : ℝ) :
    delayedHawkingCayleyRetention m lambda ^ (2 : ℕ) +
        Complex.normSq (delayedHawkingCayleyTransition m lambda) = 1 := by
  let j := delayedHawkingCayleyLoad m lambda
  have hj : lambda ^ (2 * m) = 4 * j := by
    dsimp [j]
    rw [delayedHawkingCayleyLoad]
    ring
  have hpow : (lambda ^ m) ^ (2 : ℕ) = lambda ^ (2 * m) := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  have hden : 1 + j ≠ 0 :=
    (delayedHawkingCayley_denominator_pos m lambda).ne'
  rw [delayedHawkingCayleyRetention, delayedHawkingCayleyTransition]
  change ((1 - j) / (1 + j)) ^ (2 : ℕ) +
      Complex.normSq (((lambda ^ m : ℝ) : ℂ) / (((1 + j : ℝ) : ℂ))) = 1
  rw [Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_ofReal]
  field_simp [hden]
  rw [hpow, hj]
  ring

def delayedHawkingCayleyExteriorOutput
    (m : ℕ) (lambda : ℝ) (x h : ℂ) : ℂ :=
  (delayedHawkingCayleyRetention m lambda : ℂ) * x -
    conj (delayedHawkingCayleyTransition m lambda) * h

def delayedHawkingCayleyHorizonOutput
    (m : ℕ) (lambda : ℝ) (x h : ℂ) : ℂ :=
  delayedHawkingCayleyTransition m lambda * x +
    (delayedHawkingCayleyRetention m lambda : ℂ) * h

/-- Exact unitary two-port conservation permits arbitrary delayed onset. -/
theorem delayedHawkingCayley_preserves_hermitian
    (m : ℕ) (lambda : ℝ) (x h : ℂ) :
    conj (delayedHawkingCayleyExteriorOutput m lambda x h) *
          delayedHawkingCayleyExteriorOutput m lambda x h +
        conj (delayedHawkingCayleyHorizonOutput m lambda x h) *
          delayedHawkingCayleyHorizonOutput m lambda x h =
      conj x * x + conj h * h := by
  let r : ℝ := delayedHawkingCayleyRetention m lambda
  let t : ℂ := delayedHawkingCayleyTransition m lambda
  have hunit := delayedHawkingCayleyRetention_sq_add_transition_normSq m lambda
  have hunitC := congrArg (fun y : ℝ => (y : ℂ)) hunit
  push_cast at hunitC
  have hnorm : (Complex.normSq t : ℂ) = conj t * t := by
    rw [Complex.normSq_eq_conj_mul_self]
  rw [hnorm] at hunitC
  change conj ((r : ℂ) * x - conj t * h) * ((r : ℂ) * x - conj t * h) +
      conj (t * x + (r : ℂ) * h) * (t * x + (r : ℂ) * h) =
        conj x * x + conj h * h
  simp only [map_sub, map_add, map_mul, conj_ofReal, conj_conj]
  linear_combination (conj x * x + conj h * h) * hunitC

theorem delayedHawkingCayleyTransition_ne_zero
    (m : ℕ) {lambda : ℝ} (hlambda : lambda ≠ 0) :
    delayedHawkingCayleyTransition m lambda ≠ 0 := by
  rw [delayedHawkingCayleyTransition, div_ne_zero_iff]
  constructor
  · exact_mod_cast pow_ne_zero m hlambda
  · exact_mod_cast (delayedHawkingCayley_denominator_pos m lambda).ne'

/-- Every nonzero coupling mixes even when the first `m-1` coupling channels are absent. -/
theorem delayedHawkingCayleyRetention_sq_lt_one
    (m : ℕ) {lambda : ℝ} (hlambda : lambda ≠ 0) :
    delayedHawkingCayleyRetention m lambda ^ (2 : ℕ) < 1 := by
  have hunit := delayedHawkingCayleyRetention_sq_add_transition_normSq m lambda
  have htransition : 0 < Complex.normSq (delayedHawkingCayleyTransition m lambda) :=
    Complex.normSq_pos.mpr
      (delayedHawkingCayleyTransition_ne_zero m hlambda)
  linarith

def delayedHawkingKMSCayleyUpProbability
    (m : ℕ) (lambda kappa omega : ℝ) : ℝ :=
  Complex.normSq (delayedHawkingCayleyTransition m lambda) *
    thetaCuspHawkingKMSExcitedPopulation kappa omega

def delayedHawkingKMSCayleyDownProbability
    (m : ℕ) (lambda kappa omega : ℝ) : ℝ :=
  Complex.normSq (delayedHawkingCayleyTransition m lambda) *
    (1 - thetaCuspHawkingKMSExcitedPopulation kappa omega)

/-- Exact Hawking KMS detailed balance also permits arbitrary delayed onset. -/
theorem delayedHawkingKMSCayleyUpProbability_eq_ratio_mul_down
    (m : ℕ) (lambda kappa omega : ℝ) :
    delayedHawkingKMSCayleyUpProbability m lambda kappa omega =
      thetaCuspHawkingKMSBoltzmannRatio kappa omega *
        delayedHawkingKMSCayleyDownProbability m lambda kappa omega := by
  let q := thetaCuspHawkingKMSBoltzmannRatio kappa omega
  have hq : 1 + q ≠ 0 := by
    linarith [thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega]
  rw [delayedHawkingKMSCayleyUpProbability,
    delayedHawkingKMSCayleyDownProbability,
    thetaCuspHawkingKMSExcitedPopulation]
  change _ * (q / (1 + q)) = q * (_ * (1 - q / (1 + q)))
  field_simp [hq]
  ring

/-- The delayed analytic numerator carries exactly onset-order winding. -/
theorem delayedHawkingCayleyCouplingWinding_eq_order
    (m : ℕ) (r : ℝ) (hr : 0 < r) :
    windingNumber
        (fun theta : ℝ =>
          (((r : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ m))
        0 (2 * Real.pi) = (m : ℤ) :=
  windingNumber_center_zero m r hr

/-- **[NO-GO]** Losslessness, exact Hawking KMS detailed balance, and mixing at every nonzero
coupling do not select unit coupling winding: the quadratic-onset block satisfies all three and
has local coupling winding `2`. -/
theorem lossless_KMS_every_nonzero_mix_not_force_unitCouplingWinding :
    (∀ lambda x h,
      conj (delayedHawkingCayleyExteriorOutput 2 lambda x h) *
            delayedHawkingCayleyExteriorOutput 2 lambda x h +
          conj (delayedHawkingCayleyHorizonOutput 2 lambda x h) *
            delayedHawkingCayleyHorizonOutput 2 lambda x h =
        conj x * x + conj h * h) ∧
    (∀ lambda : ℝ, lambda ≠ 0 →
      delayedHawkingCayleyRetention 2 lambda ^ (2 : ℕ) < 1) ∧
    (∀ lambda kappa omega,
      delayedHawkingKMSCayleyUpProbability 2 lambda kappa omega =
        thetaCuspHawkingKMSBoltzmannRatio kappa omega *
          delayedHawkingKMSCayleyDownProbability 2 lambda kappa omega) ∧
    (∀ r : ℝ, 0 < r →
      windingNumber
          (fun theta : ℝ =>
            (((r : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ (2 : ℕ)))
          0 (2 * Real.pi) = 2) := by
  refine ⟨delayedHawkingCayley_preserves_hermitian 2,
    fun lambda hlambda =>
      delayedHawkingCayleyRetention_sq_lt_one 2 hlambda,
    delayedHawkingKMSCayleyUpProbability_eq_ratio_mul_down 2,
    fun r hr => ?_⟩
  norm_num [delayedHawkingCayleyCouplingWinding_eq_order 2 r hr]

end RHTower
