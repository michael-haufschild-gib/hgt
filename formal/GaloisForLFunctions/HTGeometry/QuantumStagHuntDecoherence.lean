import GaloisForLFunctions.HTGeometry.QuantumStagHuntPotential
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinAmplitudeDamping

/-!
# Decoherence laws for the quantum Stag Hunt

Exact payoff, Ising-coupling, coexistence, and entanglement-negativity identities from
arXiv:2609.02957. The post-circuit amplitude-damping attenuation is connected directly
to the corpus's constructed Kraus semigroup survival mass.
-/

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Depolarized `QQ` payoff, with `s = sin(Γ)^2`. -/
def depolarizedStagHuntM (p s : ℝ) : ℝ :=
  4 - 5 * p / 2 + 3 * p ^ 2 / 4 - p * (1 - p) * s

/-- Depolarized `QD` payoff. -/
def depolarizedStagHuntN (p s : ℝ) : ℝ :=
  3 * p - 3 * p ^ 2 / 4 + 3 / 2 * (1 - p) * (2 - p) * s

/-- Depolarized `DQ` payoff. -/
def depolarizedStagHuntR (p s : ℝ) : ℝ :=
  3 - 3 * p ^ 2 / 4 - 3 / 2 * (1 - p) * (2 - p) * s

/-- Depolarized `DD` payoff. -/
def depolarizedStagHuntQ (p s : ℝ) : ℝ :=
  2 - p / 2 + 3 * p ^ 2 / 4 + p * (1 - p) * s

def phaseDampedStagHuntInteraction (_p : ℝ) : ℝ := 3 / 4
def phaseDampedStagHuntField (p s : ℝ) : ℝ := (-1 + (6 - 5 * p) * s) / 4
def depolarizedStagHuntInteraction (p : ℝ) : ℝ := 3 / 4 * (1 - p) ^ 2
def depolarizedStagHuntField (p s : ℝ) : ℝ :=
  (1 - p) * (-1 + (6 - 5 * p) * s) / 4

/-- Paper payoff table induces its stated depolarized interaction. -/
theorem depolarizedStagHunt_payoff_interaction (p s : ℝ) :
    binaryGameInteraction (depolarizedStagHuntM p s) (depolarizedStagHuntN p s)
      (depolarizedStagHuntR p s) (depolarizedStagHuntQ p s) =
        depolarizedStagHuntInteraction p := by
  simp [binaryGameInteraction, depolarizedStagHuntM, depolarizedStagHuntN,
    depolarizedStagHuntR, depolarizedStagHuntQ, depolarizedStagHuntInteraction]
  ring

/-- Paper payoff table induces its stated depolarized field. -/
theorem depolarizedStagHunt_payoff_field (p s : ℝ) :
    binaryGameField (depolarizedStagHuntM p s) (depolarizedStagHuntN p s)
      (depolarizedStagHuntR p s) (depolarizedStagHuntQ p s) =
        depolarizedStagHuntField p s := by
  simp [binaryGameField, depolarizedStagHuntM, depolarizedStagHuntN,
    depolarizedStagHuntR, depolarizedStagHuntQ, depolarizedStagHuntField]
  ring

/-- Complete depolarization collapses all four payoffs to `9/4`. -/
theorem depolarizedStagHunt_payoff_complete_noise (s : ℝ) :
    depolarizedStagHuntM 1 s = 9 / 4 ∧ depolarizedStagHuntN 1 s = 9 / 4 ∧
    depolarizedStagHuntR 1 s = 9 / 4 ∧ depolarizedStagHuntQ 1 s = 9 / 4 := by
  simp [depolarizedStagHuntM, depolarizedStagHuntN,
    depolarizedStagHuntR, depolarizedStagHuntQ]
  norm_num

/-- Depolarization multiplies the phase-damped field by its survival factor. -/
theorem depolarizedStagHuntField_eq_phase_attenuation (p s : ℝ) :
    depolarizedStagHuntField p s = (1 - p) * phaseDampedStagHuntField p s := by
  simp [depolarizedStagHuntField, phaseDampedStagHuntField]
  ring

def phaseDampedStagHuntNeutralPolynomial (p s : ℝ) : ℝ :=
  (6 - 5 * p) * s - 1

theorem phaseDampedStagHuntField_eq_neutralPolynomial (p s : ℝ) :
    phaseDampedStagHuntField p s = phaseDampedStagHuntNeutralPolynomial p s / 4 := by
  simp [phaseDampedStagHuntField, phaseDampedStagHuntNeutralPolynomial]
  ring

/-- Exact phase-damped coexistence equation `(6-5p)s=1`. -/
theorem phaseDampedStagHuntField_zero_iff (p s : ℝ) :
    phaseDampedStagHuntField p s = 0 ↔ phaseDampedStagHuntNeutralPolynomial p s = 0 := by
  rw [phaseDampedStagHuntField_eq_neutralPolynomial]
  norm_num

def stagHuntPostADAttenuation (p : ℝ) : ℝ := (1 - p) ^ 2
def postDampedStagHuntInteraction (p : ℝ) : ℝ := 3 / 4 * stagHuntPostADAttenuation p

/-- Under the corpus Kraus channel, game attenuation is squared survival mass. -/
theorem stagHuntPostADAttenuation_spinDecayMass
    (a : ℝ) (t : NNReal) :
    stagHuntPostADAttenuation (1 - SchafferExl.spinDecayMass a t) =
      SchafferExl.spinDecayMass a t ^ 2 := by
  simp [stagHuntPostADAttenuation]

/-- Paper interaction evaluated on the corpus channel's physical noise parameter. -/
theorem postDampedStagHuntInteraction_spinDecayMass
    (a : ℝ) (t : NNReal) :
    postDampedStagHuntInteraction (1 - SchafferExl.spinDecayMass a t) =
      3 / 4 * SchafferExl.spinDecayMass a t ^ 2 := by
  simp [postDampedStagHuntInteraction, stagHuntPostADAttenuation_spinDecayMass]

/-- Markovian time composition makes Stag Hunt attenuation multiplicative. -/
theorem stagHuntPostADAttenuation_spinDecayMass_add
    (a : ℝ) (s t : NNReal) :
    stagHuntPostADAttenuation (1 - SchafferExl.spinDecayMass a (s + t)) =
      stagHuntPostADAttenuation (1 - SchafferExl.spinDecayMass a s) *
        stagHuntPostADAttenuation (1 - SchafferExl.spinDecayMass a t) := by
  rw [stagHuntPostADAttenuation_spinDecayMass,
    SchafferExl.spinDecayMass_add,
    stagHuntPostADAttenuation_spinDecayMass,
    stagHuntPostADAttenuation_spinDecayMass]
  ring

/-- Resource-damped payoff table in `x = sin(Γ/2)^2` coordinates. -/
def resourceDampedStagHuntM (p x : ℝ) : ℝ := 4 + (3 * p ^ 2 - 5 * p) * x
def resourceDampedStagHuntN (p x : ℝ) : ℝ :=
  3 * x * (-p ^ 2 + 4 * p * x - 2 * p - 4 * x + 4)
def resourceDampedStagHuntR (p x : ℝ) : ℝ :=
  -3 * (p ^ 2 * x + 4 * p * x ^ 2 - 4 * p * x - 4 * x ^ 2 + 4 * x - 1)
def resourceDampedStagHuntQ (p x : ℝ) : ℝ := 2 + (3 * p ^ 2 - p) * x

def resourceDampedStagHuntInteraction (p x : ℝ) : ℝ :=
  3 / 4 * (1 - 4 * p * (1 - p) * x)
def resourceDampedStagHuntField (p x : ℝ) : ℝ :=
  (-1 + 24 * x - 24 * x ^ 2 - 22 * p * x + 24 * p * x ^ 2) / 4

theorem resourceDampedStagHunt_payoff_interaction (p x : ℝ) :
    binaryGameInteraction (resourceDampedStagHuntM p x) (resourceDampedStagHuntN p x)
      (resourceDampedStagHuntR p x) (resourceDampedStagHuntQ p x) =
        resourceDampedStagHuntInteraction p x := by
  simp [binaryGameInteraction, resourceDampedStagHuntM, resourceDampedStagHuntN,
    resourceDampedStagHuntR, resourceDampedStagHuntQ, resourceDampedStagHuntInteraction]
  ring

theorem resourceDampedStagHunt_payoff_field (p x : ℝ) :
    binaryGameField (resourceDampedStagHuntM p x) (resourceDampedStagHuntN p x)
      (resourceDampedStagHuntR p x) (resourceDampedStagHuntQ p x) =
        resourceDampedStagHuntField p x := by
  simp [binaryGameField, resourceDampedStagHuntM, resourceDampedStagHuntN,
    resourceDampedStagHuntR, resourceDampedStagHuntQ, resourceDampedStagHuntField]
  ring

/-- Post-circuit amplitude-damped payoff table. -/
def postDampedStagHuntM (p x : ℝ) : ℝ := 4 + (3 * p ^ 2 - 5 * p) * x
def postDampedStagHuntN (p x : ℝ) : ℝ :=
  2 * (6 * p * x ^ 2 - 7 * p * x + 2 * p - 6 * x ^ 2 + 6 * x)
def postDampedStagHuntR (p x : ℝ) : ℝ :=
  -12 * p * x ^ 2 + 10 * p * x + p + 12 * x ^ 2 - 12 * x + 3
def postDampedStagHuntQ (p x : ℝ) : ℝ :=
  -3 * p ^ 2 * x + 3 * p ^ 2 + p * x - p + 2
def postDampedStagHuntField (p x : ℝ) : ℝ :=
  (1 - p) * (-1 + 24 * x - 24 * x ^ 2 + 3 * p - 6 * p * x) / 4

theorem postDampedStagHunt_payoff_interaction (p x : ℝ) :
    binaryGameInteraction (postDampedStagHuntM p x) (postDampedStagHuntN p x)
      (postDampedStagHuntR p x) (postDampedStagHuntQ p x) =
        postDampedStagHuntInteraction p := by
  simp [binaryGameInteraction, postDampedStagHuntM, postDampedStagHuntN,
    postDampedStagHuntR, postDampedStagHuntQ, postDampedStagHuntInteraction,
    stagHuntPostADAttenuation]
  ring

theorem postDampedStagHunt_payoff_field (p x : ℝ) :
    binaryGameField (postDampedStagHuntM p x) (postDampedStagHuntN p x)
      (postDampedStagHuntR p x) (postDampedStagHuntQ p x) =
        postDampedStagHuntField p x := by
  simp [binaryGameField, postDampedStagHuntM, postDampedStagHuntN,
    postDampedStagHuntR, postDampedStagHuntQ, postDampedStagHuntField]
  ring

/-- At `p=1/3`, the physical post-damping coexistence branch ends at `Γ=0` (`x=0`). -/
theorem postDampedStagHuntField_branch_endpoint :
    postDampedStagHuntField (1 / 3) 0 = 0 := by
  norm_num [postDampedStagHuntField]

def postDampedStagHuntNeutralRoot (p : ℝ) : ℝ :=
  (3 * p + Real.sqrt (9 * p ^ 2 + 120)) / 12

/-- Closed radical solution of `5 - 6c^2 + 3pc = 0`. -/
theorem postDampedStagHuntNeutralRoot_equation (p : ℝ) :
    5 - 6 * postDampedStagHuntNeutralRoot p ^ 2 +
      3 * p * postDampedStagHuntNeutralRoot p = 0 := by
  have hrad : 0 ≤ 9 * p ^ 2 + 120 := by positivity
  have hsqrt := Real.sq_sqrt hrad
  unfold postDampedStagHuntNeutralRoot
  nlinarith

/-- Phase-damping negativity with `a = sin(Γ)`. -/
def phaseDampedNegativity (p a : ℝ) : ℝ := (1 - p) * a / 2

/-- Depolarizing negativity with `a = sin(Γ)`. -/
def depolarizedNegativity (p a : ℝ) : ℝ :=
  max 0 ((1 - p) ^ 2 * a / 2 - p * (2 - p) / 4)

/-- Amplitude-damping negativity with `a = sin(Γ)` and `c = cos(Γ)`. -/
def amplitudeDampedNegativity (p a c : ℝ) : ℝ :=
  (1 - p) * (a - p * (1 - c)) / 2

theorem depolarizedNegativity_nonnegative (p a : ℝ) :
    0 ≤ depolarizedNegativity p a := by
  simp [depolarizedNegativity]

theorem depolarizedNegativity_complete_noise (a : ℝ) :
    depolarizedNegativity 1 a = 0 := by
  simp [depolarizedNegativity]
  norm_num

theorem phaseDampedNegativity_complete_noise (a : ℝ) :
    phaseDampedNegativity 1 a = 0 := by
  simp [phaseDampedNegativity]

theorem amplitudeDampedNegativity_complete_noise (a c : ℝ) :
    amplitudeDampedNegativity 1 a c = 0 := by
  simp [amplitudeDampedNegativity]

end
end GaloisForLFunctions.HTGeometry
