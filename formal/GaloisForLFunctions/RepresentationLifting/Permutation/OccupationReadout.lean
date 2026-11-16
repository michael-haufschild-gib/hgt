import GaloisForLFunctions.RepresentationLifting.Permutation.SharedAttention
import GaloisForLFunctions.HTGeometry.UniformSamplePermutationFiber
import GaloisForLFunctions.RHTower.PermutationInvariantQubitClockRealization

/-!
# Shared recursive readouts factor through occupation number

With two token values, one for occupied sites and one for empty sites, every shared
attention readout is a function of Hamming weight alone. Thus the architectural symmetry
of recursive pooling gives an exact reduction to the corpus's symmetric occupation ladder.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.SharedAttention
open HTGeometry RHTower.ParityForecast
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Encode an occupation set by shared occupied and vacant token values. -/
def occupationTokens (n : ℕ) (occupied vacant : V) (S : Finset (Fin n)) : Fin n → V :=
  fun i => if sampleIndicator S i then occupied else vacant

private theorem occupationTokens_transport (n : ℕ) (occupied vacant : V)
    (S T : Finset (Fin n)) (h : S.card = T.card) :
    occupationTokens n occupied vacant T ∘ sampleTransportPerm S T h =
      occupationTokens n occupied vacant S := by
  funext i
  have hi := congrFun (sampleIndicator_comp_sampleTransportPerm S T h) i
  simp only [Function.comp_apply] at hi
  simp only [occupationTokens, Function.comp_apply, hi]

private theorem occupation_readout_eq_of_card (n : ℕ)
    (score : V → V → ℝ) (value post : V → V) (poolScore : V → ℝ) (output : V → W)
    (depth : ℕ) (initial occupied vacant : V) (S T : Finset (Fin n))
    (h : S.card = T.card) :
    readout score value post poolScore output depth initial (occupationTokens n occupied vacant S) =
      readout score value post poolScore output depth initial (occupationTokens n occupied vacant T) := by
  rw [← occupationTokens_transport n occupied vacant S T h]
  exact readout_perm score value post poolScore output depth initial _ _

/-- At every depth and every parameter choice, the readout factors through the Hamming ladder. -/
theorem occupation_readout_factors (n : ℕ)
    (score : V → V → ℝ) (value post : V → V) (poolScore : V → ℝ) (output : V → W)
    (depth : ℕ) (initial occupied vacant : V) :
    ∃ F : Fin (n + 1) → W, ∀ S : Finset (Fin n),
      readout score value post poolScore output depth initial (occupationTokens n occupied vacant S) =
        F (occupationCardIndex n S) := by
  classical
  let result (S : Finset (Fin n)) :=
    readout score value post poolScore output depth initial (occupationTokens n occupied vacant S)
  let F (m : Fin (n + 1)) :=
    if h : ∃ S : Finset (Fin n), occupationCardIndex n S = m then result (Classical.choose h) else 0
  refine ⟨F, fun S => ?_⟩
  have h : ∃ T : Finset (Fin n), occupationCardIndex n T = occupationCardIndex n S := ⟨S, rfl⟩
  change result S = F (occupationCardIndex n S)
  dsimp only [F]
  rw [dif_pos h]
  apply occupation_readout_eq_of_card
  exact (congrArg Fin.val (Classical.choose_spec h)).symm

#print axioms occupation_readout_factors

end GaloisForLFunctions.RepresentationLifting.SharedAttention
