import GaloisForLFunctions.RHTower.StaticChoiGaussianFirstReturnLaw

open Set

namespace RHTower

noncomputable section

/-- Two distinct padded words used to expose the arbitrary-target obstruction. -/
def adversarialIdentityWord : PaddedCircuitWord Bool 0 := fun _ => false

def adversarialOrbitWord : PaddedCircuitWord Bool 0 := fun _ => true

/-- An arbitrary target map may place one word at the initial Choi ray and another exactly on the
same orbit at positive time one. -/
def adversarialStaticChoiTarget (d : ℕ) (energy : Fin (d + 1) → ℝ) (τ : ℝ) :
    PaddedCircuitWord Bool 0 → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) :=
  fun w => if w 0 then
    staticSpectralChoiVector (d + 1) τ energy
  else
    staticSpectralChoiVector (d + 1) 0 energy

@[simp] theorem adversarialStaticChoiTarget_identity
    (d : ℕ) (energy : Fin (d + 1) → ℝ) (τ : ℝ) :
    adversarialStaticChoiTarget d energy τ adversarialIdentityWord =
      staticSpectralChoiVector (d + 1) 0 energy := by
  simp [adversarialStaticChoiTarget, adversarialIdentityWord]

@[simp] theorem adversarialStaticChoiTarget_orbit
    (d : ℕ) (energy : Fin (d + 1) → ℝ) (τ : ℝ) :
    adversarialStaticChoiTarget d energy τ adversarialOrbitWord =
      staticSpectralChoiVector (d + 1) τ energy := by
  simp [adversarialStaticChoiTarget, adversarialOrbitWord]

theorem norm_adversarialStaticChoiTarget
    (d : ℕ) (energy : Fin (d + 1) → ℝ) (τ : ℝ)
    (w : PaddedCircuitWord Bool 0) :
    ‖adversarialStaticChoiTarget d energy τ w‖ = 1 := by
  unfold adversarialStaticChoiTarget
  split <;> exact staticSpectralChoiVector_norm (by omega) _ energy

@[simp] theorem pureStateTraceDistance_adversarialStaticChoiTarget_orbit
    (d : ℕ) (energy : Fin (d + 1) → ℝ) (τ : ℝ) :
    pureStateTraceDistance
      (staticSpectralChoiVector (d + 1) τ energy)
      (adversarialStaticChoiTarget d energy τ adversarialOrbitWord) = 0 := by
  rw [adversarialStaticChoiTarget_orbit]
  unfold pureStateTraceDistance
  rw [inner_self_eq_norm_sq_to_K,
    staticSpectralChoiVector_norm (by omega : 0 < d + 1)]
  norm_num

/-- **Arbitrary-target first-return no-go.** No theorem can quantify over every normalized padded
target map, require only that one word is the initial Choi ray, and then exclude all positive-time
captures.  A two-word target dictionary can encode the orbit itself at time one.  Hence a genuine
circuit first-return law must use fixed gate semantics rather than an arbitrary normalized map. -/
theorem not_every_normalizedPaddedCircuitTarget_avoids_positiveTimeCapture
    (d : ℕ) (energy : Fin (d + 1) → ℝ) :
    ¬ ∀ (target : PaddedCircuitWord Bool 0 →
          EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1))),
        (∀ w, ‖target w‖ = 1) →
        ∀ identityWord : PaddedCircuitWord Bool 0,
          target identityWord = staticSpectralChoiVector (d + 1) 0 energy →
          ¬ ∃ t ∈ Icc (1 : ℝ) 1,
            ∃ w, pureStateTraceDistance
              (staticSpectralChoiVector (d + 1) t energy) (target w) ≤ 0 := by
  intro hall
  have havoid := hall (adversarialStaticChoiTarget d energy 1)
    (norm_adversarialStaticChoiTarget d energy 1)
    adversarialIdentityWord (adversarialStaticChoiTarget_identity d energy 1)
  apply havoid
  refine ⟨1, ⟨le_rfl, le_rfl⟩, adversarialOrbitWord, ?_⟩
  rw [pureStateTraceDistance_adversarialStaticChoiTarget_orbit]

end

end RHTower
