import GaloisForLFunctions.RHTower.SelbergClass.Basic

/-!
# Invariant root number of a concrete Selberg gamma presentation

`SelbergGammaData.rootNumber` is the raw phase in the completed functional
equation.  Kaczorowski--Perelli's asymmetric functional equation and multiple
twist residue formula instead use the invariant phase
`ω_F = ω ∏ λ_j ^ (-2 i Im μ_j)`.  This module names that source-faithful
quantity without altering the raw completed-functional-equation carrier.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Invariant root number `ω_F` from Kaczorowski--Perelli (2.1), formed from
the raw completed-functional-equation phase and the selected gamma data. -/
noncomputable def SelbergGammaData.invariantRootNumber (G : SelbergGammaData) : ℂ :=
  G.rootNumber * ∏ j, (G.lambda j : ℂ) ^ (-(2 : ℂ) * I * ((G.mu j).im : ℂ))

end

end RHTower
