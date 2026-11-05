# The logarithmic Poisson factor has its exact normalization

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `Ψ(t)=1+(1/2)log(1+t²)` and `κ(s)=exp((1/π)∫₀∞s log(Ψ(t))/(s²+t²)dt)`, one has `κ(s)/√log(s)→1` as `s→∞`. The factor is increasing and at least one for `s>0`, with `κ(s)→1` as `s↓0`.

## Proof

Put `φ(w)=log(Ψ(exp w))`. Its derivative is

`φ′(w)=2 exp(2w)/((1+exp(2w))(2+log(1+exp(2w))))`.

The inequalities `1-x⁻¹≤log x` and `2w≤log(1+exp(2w))` give
`0≤φ′≤2` everywhere and `φ′(w)≤1/w` for `w>0`.
The mean value theorem therefore gives
`|φ(w+u)-φ(w)|≤2|u|`, and, for `w>|u|`, the sharper bound
`|u|/(w-|u|)`. Each fixed increment tends to zero.

Under `t=s exp u`, the defining Poisson integral becomes
`(1/(2π))∫φ(log s+u)/cosh u du`.
Since `∫1/cosh=π`, its difference from `(1/2)φ(log s)` is the same
average of the increments. The integrable majorant `2|u|/cosh u`
justifies dominated convergence. Thus `κ(s)/√Ψ(s)→1`.
Finally `Ψ(s)/log s→1`, using
`log(1+s²)=2log s+log(1+s⁻²)`.

At zero, `φ(log s+u)=log Ψ(s exp u)→0`. For `0<s≤1`, monotonicity gives
the majorant `φ(u)/cosh u`, integrable by the same Lipschitz bound.
Dominated convergence proves the unit limit. Positivity and monotonicity
also pass directly through the sech integral and exponential.

The complex extension is
`κ(z)=exp((1/π)∫₀∞√z Log(1+(1/2)Log(1+zt²))/(z+t²)dt)`.
For compact sets of slit-plane parameters, the segment
`(1-u)+zu`, `0≤u≤1`, stays uniformly away from zero and the cut.
This bounds the resolvent below by `c(1+t²)` and the nested logarithm
above by `C+log(1+t²)`. The resulting integrable majorant proves
holomorphy. Two positive dilations identify the real values with `κ(s)`;
conjugating the integral proves reflection across the real axis.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicPoissonFactorHasItsExactNormalization.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `logReferenceFactor_eq_poisson`
- `tendsto_logReferenceFactor_div_sqrt_symbol`
- `tendsto_logReferenceFactor_div_sqrt_log`

`TheLogarithmicFactorStartsAtOne.lean` also proves
`one_le_logReferenceFactor`, `monotoneOn_logReferenceFactor`, and
`tendsto_logReferenceFactor_at_zero`; its production audit and transitive
axiom check pass with the same standard axioms.

`TheLogarithmicFactorExtendsToTheSlitPlane.lean` proves
`differentiableOn_complexLogReferenceFactor`,
`complexLogReferenceFactor_ofReal`, and `complexLogReferenceFactor_conj`.
Its production plain audit and transitive axiom checks pass.

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
This proves the literal positive Poisson factor and its normalization.
Stieltjes representation, causal operator factorization and the half-line
Green identity remain unproved.
