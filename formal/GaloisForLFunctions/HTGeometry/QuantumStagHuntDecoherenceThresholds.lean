import GaloisForLFunctions.HTGeometry.QuantumStagHuntDecoherence

/-!
# Neutrality and entanglement thresholds in the decoherent quantum Stag Hunt

Closed radical coexistence solutions and exact entanglement-death conditions from
arXiv:2609.02957. Physical subunit noise is encoded as an input type, eliminating
denominator premises. Half-angle payoff coordinates are bridged back to cosine equations.
-/

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Physical noise parameters in `[0,1)`. -/
structure StagHuntSubunitNoise where
  val : ℝ
  nonnegative : 0 ≤ val
  lt_one : val < 1

instance : Coe StagHuntSubunitNoise ℝ := ⟨StagHuntSubunitNoise.val⟩

def phaseDampedNeutralSinSq (p : StagHuntSubunitNoise) : ℝ :=
  1 / (6 - 5 * (p : ℝ))

/-- Closed phase/depolarizing coexistence line `sin(Γ)^2 = 1/(6-5p)`. -/
theorem phaseDampedNeutralSinSq_field_zero (p : StagHuntSubunitNoise) :
    phaseDampedStagHuntField (p : ℝ) (phaseDampedNeutralSinSq p) = 0 := by
  have hd : 6 - 5 * (p : ℝ) ≠ 0 := by
    have : 0 < 6 - 5 * (p : ℝ) := by linarith [p.lt_one]
    exact this.ne'
  simp [phaseDampedStagHuntField, phaseDampedNeutralSinSq]
  field_simp
  ring

/-- Resource-amplitude-damping coexistence equation in `c = cos(Γ)`. -/
def resourceDampedNeutralEquation (p c : ℝ) : ℝ :=
  (1 - p) * (5 - 6 * c ^ 2) - p * c

def resourceDampedNeutralCos (p : StagHuntSubunitNoise) : ℝ :=
  (-(p : ℝ) + Real.sqrt ((p : ℝ) ^ 2 + 120 * (1 - (p : ℝ)) ^ 2)) /
    (12 * (1 - (p : ℝ)))

/-- Half-angle payoff field equals the paper's cosine-coordinate equation. -/
theorem resourceDampedStagHuntField_cosCoordinate (p c : ℝ) :
    resourceDampedStagHuntField p ((1 - c) / 2) =
      resourceDampedNeutralEquation p c / 4 := by
  simp [resourceDampedStagHuntField, resourceDampedNeutralEquation]
  ring

/-- Closed resource-damping radical solves its coexistence equation. -/
theorem resourceDampedNeutralCos_equation (p : StagHuntSubunitNoise) :
    resourceDampedNeutralEquation (p : ℝ) (resourceDampedNeutralCos p) = 0 := by
  have hb : 1 - (p : ℝ) ≠ 0 := by linarith [p.lt_one]
  have hrad : 0 ≤ (p : ℝ) ^ 2 + 120 * (1 - (p : ℝ)) ^ 2 := by positivity
  have hs := Real.sq_sqrt hrad
  unfold resourceDampedNeutralEquation resourceDampedNeutralCos
  field_simp
  ring_nf at hs ⊢
  nlinarith

theorem resourceDampedNeutralCos_field_zero (p : StagHuntSubunitNoise) :
    resourceDampedStagHuntField (p : ℝ) ((1 - resourceDampedNeutralCos p) / 2) = 0 := by
  rw [resourceDampedStagHuntField_cosCoordinate, resourceDampedNeutralCos_equation]
  norm_num

/-- Post-circuit amplitude-damping coexistence equation in `c = cos(Γ)`. -/
def postDampedNeutralEquation (p c : ℝ) : ℝ := 5 - 6 * c ^ 2 + 3 * p * c

theorem postDampedStagHuntField_cosCoordinate (p c : ℝ) :
    postDampedStagHuntField p ((1 - c) / 2) =
      (1 - p) * postDampedNeutralEquation p c / 4 := by
  unfold postDampedStagHuntField postDampedNeutralEquation
  ring

theorem postDampedNeutralRoot_equation (p : ℝ) :
    postDampedNeutralEquation p (postDampedStagHuntNeutralRoot p) = 0 := by
  exact postDampedStagHuntNeutralRoot_equation p

theorem postDampedNeutralRoot_field_zero (p : ℝ) :
    postDampedStagHuntField p ((1 - postDampedStagHuntNeutralRoot p) / 2) = 0 := by
  rw [postDampedStagHuntField_cosCoordinate, postDampedNeutralRoot_equation]
  ring

/-- Phase-damping entanglement vanishes only at complete noise or zero input sine. -/
theorem phaseDampedNegativity_zero_iff (p a : ℝ) :
    phaseDampedNegativity p a = 0 ↔ p = 1 ∨ a = 0 := by
  simp [phaseDampedNegativity, div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr h

/-- Amplitude-damping entanglement-death surface. -/
theorem amplitudeDampedNegativity_zero_iff (p a c : ℝ) :
    amplitudeDampedNegativity p a c = 0 ↔ p = 1 ∨ a = p * (1 - c) := by
  simp [amplitudeDampedNegativity, div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

/-- Depolarizing entanglement dies exactly when the unclipped expression is nonpositive. -/
theorem depolarizedNegativity_zero_iff (p a : ℝ) :
    depolarizedNegativity p a = 0 ↔
      (1 - p) ^ 2 * a / 2 - p * (2 - p) / 4 ≤ 0 := by
  simp [depolarizedNegativity]

end
end GaloisForLFunctions.HTGeometry
