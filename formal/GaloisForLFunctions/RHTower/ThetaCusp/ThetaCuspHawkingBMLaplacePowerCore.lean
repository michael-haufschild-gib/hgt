import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The positive-real radial complex power, independent of physical monodromy. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

/-- Original positive-radius complex-power branch. -/
def power (a : ℂ) (z : ℝ) : ℂ := (z : ℂ) ^ a

end
end RHTower.D4BMLaplaceRadial
