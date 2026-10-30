# Dirichlet logarithmic derivatives have uniform conductor cost

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For each `ε>0`, there are `a,B>0`, independent of modulus and character, such that every nonprincipal `χ mod q` is nonzero and satisfies `|L'/L(s,χ)|≤B q^ε L³` on `|Re s-1|≤δ`, `|Im s|≤T`, where `L=log(q(T+5))` and `δ=a q^(-ε)/L²`.

## Proof

[PROVED HERE] The conductor-uniform zero-free region excludes nonreal zeros at distance `c/log(q(|Im ρ|+3))²` from `Re s=1`. The real-character theorem excludes real zeros at distance `d_ε q^(-ε)`. Choose `a=min(c/4,d_ε/4,1/8)`. Since `q≥1` and `L≥1`, every zero with `|Im ρ|≤T+2` has `1-Re ρ≥4δ`. Thus the stated rectangle is zero-free, and every such zero is at distance at least `3δ` from each point of the rectangle.

The actual local partial fraction about `z=2+it` uses the zeros in radius `(22/25)(91/50)<2`, with error at most `pfConst·log(q(|t|+3))`. At its center, `Re(z-ρ)>1` and `|z-ρ|<2`, so `Re(1/(z-ρ))≥1/4`. Absolute convergence gives `|L'/L(z,χ)|≤8`. Taking real parts of the partial fraction therefore bounds the total local multiplicity by `4(8+pfConst·log(q(|t|+3)))`.

For a rectangle point `s`, use the local partial fraction centered at `2+i Im s`. All its zeros satisfy the preceding height and distance bounds. Summing the absolute values of the zero terms costs at most the local multiplicity divided by `δ`. The error is at most `pfConst·L`. Since `δ≤1/8` and `L≥1`, their sum is at most `(32+5pfConst)L/δ = ((32+5pfConst)/a)q^ε L³`. Multiplicities, real characters and imprimitive characters are retained.

## Dependencies and scope

- `RHTower.uniform_zero_free_region`
- `RHTower.siegel_zero_free`
- `RHTower.L_logDeriv_partial_fraction_all`
- `RHTower.norm_character_logDeriv_le_line`

Lean source: `GaloisForLFunctions/RHTower/ConductorUniform/DirichletLConductorUniformLogDerivative.lean`.

- `exists_conductor_uniform_character_zero_gap`
- `L_partial_fraction_with_multiplicity_bound`
- `exists_conductor_uniform_character_logDeriv`

Direct `lake --old env lean` audit passed without warnings. All three declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. No zero-free, reciprocal, or prime-distribution estimate remains an assumed input. The growing-modulus prime-source theorem still requires the actual Perron contour estimate and signed unsmoothing.
