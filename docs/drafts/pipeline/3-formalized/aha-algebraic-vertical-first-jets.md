# Algebraic coefficients make the first vertical jet faithful

- **ID:** AHA-VERTICAL-ALG
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For a polynomial with algebraic coefficients at a nonzero algebraic prime-coordinate point, its derivative along the logarithmic prime flow vanishes exactly when all coordinate partial derivatives vanish.

## Exact statement and proof

Let `p₁,…,p_k` be distinct primes, `F∈ℚ̄[z₁,…,z_k]`, and
`x∈(ℚ̄×)^k`. Set `V(s)=F(x_i exp(s log p_i))`. The chain rule gives

`V′(0)=Σ_i x_i ∂_i F(x) log p_i`.

Each coefficient `x_i ∂_i F(x)` is algebraic. Baker's theorem forces all
of them to vanish. Since every `x_i` is nonzero, this is equivalent to
`∂_i F(x)=0` for every `i`. The converse follows from the same identity.
Also `V(0)=F(x)`, so value and first vertical jet detect full first-order
coordinate data at algebraic torus points.

This explains why the real-logarithmic counterexample in AHA-VERTICAL
does not settle integer auxiliaries. It gives no quantitative lower bound.
Higher jets with two primes should follow from AHA-LOG2; higher-degree
homogeneous relations among three or more prime logs remain a separate input.

## Lean closure

Module `ArithmeticHarmonicAnalysis/AlgebraicVerticalFirstJets.lean`,
namespace `GaloisForLFunctions.ArithmeticHarmonicAnalysis`:

- `hasDerivAt_primeLogTrace` proves the actual analytic chain rule;
- `algebraic_primeLogTrace_derivative_zero_iff` identifies the first
  logarithmic derivative with coordinate-gradient vanishing;
- `algebraic_primeLogTrace_firstJets_vanish_iff` includes the value.

The actual source passed `lake --old env lean`. These declarations and
the imported `RHTower.primeLogs_algClosure_linearIndependent` have only
`propext`, `Classical.choice`, `Quot.sound` as transitive axioms.
This is a classical Baker consequence applied to the precise coefficient
boundary of the vertical-jet obstruction; no new transcendence theorem
or quantitative estimate is claimed.
