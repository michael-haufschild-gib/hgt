import GaloisForLFunctions.HTGeometry.ExponentialBlockSeedFaithful
import GaloisForLFunctions.HTGeometry.BoundaryWedgeSeedAssembly

/-!
# The one-variable block datum exists

Assembling the block seed with its annihilation and faithfulness properties gives the one-variable
datum `BlockSeed` for every finite block whose steps are integrally independent.  This is the
positive input the two-variable realization of the boundary wedge consumes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- **The exponential block seed.**  Steps vanishing off the block and integrally independent on it
give a one-variable block datum: the seed `∑_{v ∈ B} exp (exp (2πi z / step v))` is entire, is
annihilated by the full block product of difference operators, and has nonconstant carrier for every
polynomial with a monomial inside the block missing a block vertex. -/
def expBlockSeed {B : Finset α} {step : α → ℂ} (hoff : ∀ v ∉ B, step v = 0)
    (hindep : StepIndep B step) : BlockSeed B where
  step := step
  step_off := hoff
  seed := blockSeedFun B step
  seed_entire := differentiable_blockSeedFun B step
  seed_ann := seedAnnihilates_blockSeedFun_prod B step fun _ hv => stepIndep_ne_zero hindep hv
  seed_nonconstant := fun P hP => exists_ne_seedCarrierPoly_blockSeedFun hoff hindep P hP

@[simp] theorem expBlockSeed_step {B : Finset α} {step : α → ℂ} (hoff : ∀ v ∉ B, step v = 0)
    (hindep : StepIndep B step) : (expBlockSeed hoff hindep).step = step := rfl

end

end GaloisForLFunctions.HTGeometry
