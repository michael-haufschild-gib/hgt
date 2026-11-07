# Composite cubic reciprocity

- **ID:** composite-cubic-reciprocity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The actual cubic ideal symbol is multiplicative in both arguments, depends only on the numerator modulo the denominator, and satisfies reciprocity for primary composite elements.

For `I≠0`, define `(x/I)₃=∏_P χ_P(x)^v_P(I)`, extending bad prime values
by zero. Set `(x/0)₃=0` and `(x/y)₃=(x/(y))₃`. Ideal factorization proves
denominator multiplicativity. Each prime value is multiplicative, including
its zero extension, so numerator multiplicativity holds for every ideal.

For primary `a,b`, exact primary prime factorizations reduce `(a/b)₃=(b/a)₃`
to a double product of prime symbols. Interchange the finite products and
apply prime reciprocity to every pair. Common prime factors give zero on both
sides. Thus no squarefree or coprimality restriction is needed for reciprocity.

If `x` is coprime to primary `a`, it avoids every maximal ideal dividing `(a)`:
a Bezout relation would otherwise put one in that ideal. Each prime value is
therefore a cubic root of unity, hence `(x/a)₃³=1` and its complex norm is one.
Numerator congruence follows because every ideal prime divisor contains `(a)`.

Module: `MetaplecticMobiusDescent/CubicJacobiSymbols.lean`.
Audited endpoints: `idealSymbol_mul`, `idealSymbol_map_mul`,
`symbol_reciprocity`, `symbol_congr`, `symbol_cube_of_isCoprime`,
`symbol_norm_one`. Direct Lean audit passed; all six transitive axiom lists
contain only `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.

Adapted from external OpenAI sources listed in `NOTICE`. The ramified supplementary law and Kubota multiplier are recorded on
[cubic-jacobi-symbol-and-kubota-character](cubic-jacobi-symbol-and-kubota-character.md).
