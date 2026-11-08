# Multiplicity consumes a hyperbolic annihilator budget

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Obstacles:** B13, B112.
- **Statement:** For a normalized positive two-prime Dirichlet polynomial `P`, let `H=H_P(σ)`. If `ρ=σ+δ+iγ`, `δ>0`, `γ≠0`, is a zero of order at least `n`, conjecture
  `1+H ≥ ((sqrt(δ²+γ²)+δ)/(sqrt(δ²+γ²)-δ))^n`.
  More generally, every finite zero divisor to the right of `σ` should satisfy the corresponding product of half-plane Blaschke costs, evaluated at each real point `x>σ`.
- **Mechanism:** Positivity gives `P(x)≥1` on the real axis and `|P(s)|≤1+H` on `Re s≥σ`. Real coefficients supply the conjugate zero with the same multiplicity. Remove both Blaschke factors without increasing the bound. Optimize the real evaluation point at `x-σ=sqrt(δ²+γ²)`.
- **New consequence sought:** At fixed height and fixed positive left displacement, bounded mass permits only bounded multiplicity. Compare with arbitrary multiplicity near unit mass measured on the zero's own line.
- **Corpus leads:** `HTGeometry/DiskMultiplierBlaschkeDivision` proves norm-preserving removal of one disk zero; `MultiscaleMollifiedZetaField/TheDerivativeReadsTheBlaschkeFactor` handles finite half-plane products; `ArithmeticPositiveDuality/ArbitraryMultiplicityNearUnitAnnihilatorMass` gives the contrasting boundary construction.
- **Gate:** Audit whether the specialized bound or stronger capacity law already exists; prove the exact finite-divisor result and formalize before counting. No conclusion about actual zeta zeros yet.
