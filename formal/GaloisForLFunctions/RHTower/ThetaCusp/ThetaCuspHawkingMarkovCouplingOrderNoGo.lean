import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingQuantumStratonovichBoundaryEndpoint

/-!
# Temporal Markovity does not select Hawking coupling order

Poissonizing the exact delayed-onset Hawking Cayley collision gives a genuine continuous-time
Markov relaxation semigroup.  Every nonzero quadratic coupling relaxes, while the transition
amplitude still has zero first coupling jet and winding two.

This closes a tempting but false route: composition in physical time cannot determine order in
the external coupling parameter.  The surviving RH-bearing producer must constrain the
parameter-to-generator map itself, for example by a theta-source-faithful first-jet
transversality or by the already isolated standard-clock nondegeneracy condition.
-/

open Complex Real Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-- Collision probability per unit Poisson time for the exact delayed Hawking Cayley block. -/
def delayedHawkingQuantumMarkovRate (m : ℕ) (lambda : ℝ) : ℝ :=
  Complex.normSq (delayedHawkingCayleyTransition m lambda)

theorem delayedHawkingQuantumMarkovRate_nonneg (m : ℕ) (lambda : ℝ) :
    0 ≤ delayedHawkingQuantumMarkovRate m lambda :=
  Complex.normSq_nonneg _

theorem delayedHawkingQuantumMarkovRate_pos
    (m : ℕ) {lambda : ℝ} (hlambda : lambda ≠ 0) :
    0 < delayedHawkingQuantumMarkovRate m lambda :=
  Complex.normSq_pos.mpr (delayedHawkingCayleyTransition_ne_zero m hlambda)

/-- Exact transverse deviation flow obtained by Poissonizing independent Cayley collisions. -/
def delayedHawkingQuantumMarkovDeviationFlow
    (m : ℕ) (lambda t c : ℝ) : ℝ :=
  Real.exp (-delayedHawkingQuantumMarkovRate m lambda * t) * c

theorem delayedHawkingQuantumMarkovDeviationFlow_zero
    (m : ℕ) (lambda c : ℝ) :
    delayedHawkingQuantumMarkovDeviationFlow m lambda 0 c = c := by
  simp [delayedHawkingQuantumMarkovDeviationFlow]

/-- **[PAPER-PROVED] [LEAN-PROVED]** Poissonized exact collisions form a time-homogeneous
one-parameter semigroup for every onset order. -/
theorem delayedHawkingQuantumMarkovDeviationFlow_add
    (m : ℕ) (lambda t s c : ℝ) :
    delayedHawkingQuantumMarkovDeviationFlow m lambda (t + s) c =
      delayedHawkingQuantumMarkovDeviationFlow m lambda t
        (delayedHawkingQuantumMarkovDeviationFlow m lambda s c) := by
  rw [delayedHawkingQuantumMarkovDeviationFlow,
    delayedHawkingQuantumMarkovDeviationFlow,
    delayedHawkingQuantumMarkovDeviationFlow]
  rw [show -delayedHawkingQuantumMarkovRate m lambda * (t + s) =
      -delayedHawkingQuantumMarkovRate m lambda * t +
        -delayedHawkingQuantumMarkovRate m lambda * s by ring,
    Real.exp_add]
  ring

/-- A delayed Hawking Markov sector mixes when every transverse deviation relaxes. -/
def DelayedHawkingQuantumMarkovSectorMixes
    (m : ℕ) (lambda : ℝ) : Prop :=
  ∀ c : ℝ,
    Tendsto
      (fun t : ℝ => delayedHawkingQuantumMarkovDeviationFlow m lambda t c)
      atTop (𝓝 0)

theorem delayedHawkingQuantumMarkovSectorMixes_of_ne_zero
    (m : ℕ) {lambda : ℝ} (hlambda : lambda ≠ 0) :
    DelayedHawkingQuantumMarkovSectorMixes m lambda := by
  intro c
  have hrate := delayedHawkingQuantumMarkovRate_pos m hlambda
  have hscale : Tendsto
      (fun t : ℝ => delayedHawkingQuantumMarkovRate m lambda * t)
      atTop atTop :=
    Filter.Tendsto.const_mul_atTop hrate tendsto_id
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  simpa [delayedHawkingQuantumMarkovDeviationFlow] using hexp.mul_const c

/-- Real transition coordinate whose complexification is the exact Cayley transition. -/
def delayedHawkingCayleyTransitionReal (m : ℕ) (lambda : ℝ) : ℝ :=
  lambda ^ m / (1 + delayedHawkingCayleyLoad m lambda)

theorem ofReal_delayedHawkingCayleyTransitionReal
    (m : ℕ) (lambda : ℝ) :
    (delayedHawkingCayleyTransitionReal m lambda : ℂ) =
      delayedHawkingCayleyTransition m lambda := by
  simp [delayedHawkingCayleyTransitionReal, delayedHawkingCayleyTransition]

/-- Quadratic Hawking transition has a vanishing first coupling jet. -/
theorem hasDerivAt_delayedHawkingCayleyTransitionReal_two_zero :
    HasDerivAt (delayedHawkingCayleyTransitionReal 2) 0 0 := by
  have hnum : HasDerivAt (fun lambda : ℝ => lambda ^ (2 : ℕ)) 0 0 := by
    exact (hasDerivAt_pow 2 (0 : ℝ)).congr_deriv (by norm_num)
  have hpow4 : HasDerivAt (fun lambda : ℝ => lambda ^ (4 : ℕ)) 0 0 := by
    exact (hasDerivAt_pow 4 (0 : ℝ)).congr_deriv (by norm_num)
  have hden : HasDerivAt (fun lambda : ℝ => 1 + lambda ^ (4 : ℕ) / 4) 0 0 := by
    exact ((hpow4.div_const 4).const_add 1).congr_deriv (by norm_num)
  change HasDerivAt (fun lambda : ℝ => lambda ^ (2 : ℕ) / (1 + lambda ^ (4 : ℕ) / 4)) 0 0
  simpa only [Pi.div_apply] using!
    (hnum.div hden (by norm_num)).congr_deriv (by norm_num)

/-- **[FALSIFIED]** Exact quantum-Stratonovich selection, two-port losslessness, Hawking KMS,
time-homogeneous Markov composition, and relaxation at every nonzero coupling do not force a
first-order coupling channel.  The quadratic block has all those properties, zero first jet, and
winding two. -/
theorem quantumStratonovich_KMS_Markov_relaxation_not_force_firstCouplingOrder :
    (∀ lambda x h,
      QuantumStratonovichTwoPortBoundary (((lambda ^ (2 : ℕ) : ℝ) : ℂ)) x h
        (delayedHawkingCayleyExteriorOutput 2 lambda x h)
        (delayedHawkingCayleyHorizonOutput 2 lambda x h)) ∧
    (∀ lambda x h,
      conj (delayedHawkingCayleyExteriorOutput 2 lambda x h) *
            delayedHawkingCayleyExteriorOutput 2 lambda x h +
          conj (delayedHawkingCayleyHorizonOutput 2 lambda x h) *
            delayedHawkingCayleyHorizonOutput 2 lambda x h =
        conj x * x + conj h * h) ∧
    (∀ lambda kappa omega,
      delayedHawkingKMSCayleyUpProbability 2 lambda kappa omega =
        thetaCuspHawkingKMSBoltzmannRatio kappa omega *
          delayedHawkingKMSCayleyDownProbability 2 lambda kappa omega) ∧
    (∀ lambda t s c,
      delayedHawkingQuantumMarkovDeviationFlow 2 lambda (t + s) c =
        delayedHawkingQuantumMarkovDeviationFlow 2 lambda t
          (delayedHawkingQuantumMarkovDeviationFlow 2 lambda s c)) ∧
    (∀ lambda : ℝ, lambda ≠ 0 →
      DelayedHawkingQuantumMarkovSectorMixes 2 lambda) ∧
    HasDerivAt (delayedHawkingCayleyTransitionReal 2) 0 0 ∧
    (∀ r : ℝ, 0 < r →
      windingNumber
          (fun theta : ℝ =>
            (((r : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ (2 : ℕ)))
          0 (2 * Real.pi) = 2) := by
  rcases quantumStratonovich_lossless_KMS_every_nonzero_mix_not_force_unitCouplingWinding with
    ⟨hboundary, hlossless, _hcollisionMixing, hKMS, hwinding⟩
  exact ⟨hboundary, hlossless, hKMS,
    delayedHawkingQuantumMarkovDeviationFlow_add 2,
    fun _lambda hlambda =>
      delayedHawkingQuantumMarkovSectorMixes_of_ne_zero 2 hlambda,
    hasDerivAt_delayedHawkingCayleyTransitionReal_two_zero,
    hwinding⟩

end RHTower
