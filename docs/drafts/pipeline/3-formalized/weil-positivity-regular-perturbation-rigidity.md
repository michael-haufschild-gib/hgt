# Regular rigidity of Weil positivity (oscillating perturbations)

**Status:** formalized (Lean, unconditional instances, standard axioms).
**Module:** `formal/GaloisForLFunctions/RHTower/WeilPositivityRegularPerturbationRigidity.lean`

## Statements
- General theorem: if the atoms of `w` pair with the tests through a continuous symbol of linear growth, then Weil positivity of `Λ + w` forces `w = 0`.
- Oscillating instance: `b` with bounded partial sums gives `c b = 0`.
- Character instance: `Λ + cχ₋₄` Weil-positive ⇒ `c = 0`.

## Proof
1. Concentration of spread radical tests: `P ≤ 0`.
2. Probes supported in `[−log 2/4, log 2/4]`, which see no atoms: `P ≡ 0`.
3. Two-point resonators: `w(n₀) = 0`.
4. The oscillating symbol is `2Σ_n B(n)(g_τ(n) − g_τ(n+1))`. It is absolutely convergent by a mean-value bound, continuous, and pairs with tests by Fubini and Abel summation.

## Context
This is the uniqueness half of the Minkowski split (L68). It extends uniqueness from summable (L64) and finite-measure (L67) perturbations to conditionally convergent ones.
