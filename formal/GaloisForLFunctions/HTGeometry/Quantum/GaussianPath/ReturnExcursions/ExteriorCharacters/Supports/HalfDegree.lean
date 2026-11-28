import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Supports.HammingPrice

/-! # The small-support correction at half exterior degree -/

open Filter
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
noncomputable section
/-- For large dimensions divisible by four, all pairs differing on at most
a quarter of the levels cost less than half the squared character floor. -/
theorem quarter_price :
    ∀ᶠ n : ℕ in atTop, 2^n*(3/2:ℝ)^(4*n) ≤
      (1/2:ℝ)*((4*n).choose (2*n):ℝ)*(199/200)^(4*n) :=
  quarter_price_of_base (by norm_num)

#print axioms quarter_price
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
