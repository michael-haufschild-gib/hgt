# Levinson's gate from the two-main-term twisted moment

- **ID:** A111
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

Produce an unconditional positive critical-zero proportion through the
Levinson detector, using the proved twisted second moment for mollifier
length `T^θ`, `θ<1/2`.

## Available results

`MultiscaleMollifiedZetaField.exists_twistedMoment_power_saving` gives
the actual mollified zeta moment, uniformly in the real displacement and
bounded real coefficients, with both gcd main terms and arbitrary power saving.
`exists_interval_twistedMoment_le` transfers it to interval moments.

`RHTower.levinsonReciprocalLogMeanSquareGate_of_dyadicLaw` converts a
dyadic bound for `(ζ+ζ'/log U)Ψ` into the gate. The gate-to-zero-count
arguments and positivity of the reciprocal-log detector weight are proved.
Short-range differentiated coefficient energies are also proved, but omit
the full analytic tail and do not themselves establish the gate.

## Missing assembly

The available twisted moment concerns `ζΨ`, whereas the gate concerns
`(ζ+λζ')Ψ`. Differentiating a uniform real-parameter error estimate without
derivative control is invalid. The actual differentiated moment, its main
term, and uniform boundary errors must be derived before choosing constants.

A possible route uses `F=ζΨ` and `ζ'Ψ=F'−ζΨ'`: polarization supplies
coefficient cross terms, while the Cauchy–Riemann energy identity relates
the integrated derivative square to the second abscissa derivative and
horizontal boundary terms. This requires a proved differentiation or
positive finite-difference argument, not a new moment premise.

For holomorphic `F,G` on a rectangle, put `q_F(σ)=∫|F(σ+it)|²dt`
and `b(σ)=Re∫F(σ+it)conj(G(σ+it))dt`. Integration by parts gives

`∫|F+λF'−G|² = q_F+q_G−2b+λ(q_F'−b')+λ²q_F''/4`
`+ λ²[∂_t|F|²]/4 − λ[Im(F conj G)]`.

The brackets are upper minus lower endpoint values. Taking `G=λζΨ'`
therefore reduces the detector to real-parameter moments and explicit
horizontal boundary terms. Also `q_F''=4∫|F'|²−[∂_t|F|²]`;
applying this identity again controls the fourth derivative from below.
These positivity identities offer finite-difference control of the first
two derivatives. Their uniform bounds and the resulting gcd main-term
limits still require formalization.

The arbitrary power saving also permits a direct Taylor route. If the
moment and its main term have fourth derivatives bounded by `T^C`, use
step `h=T^(−M)`: the symmetric second difference has error
`O(T^(1−B+2M)+T^(C−2M))`. Choose `2M>C` and then `B>1+2M`.
The first derivative follows from the analogous symmetric difference.
The displacement `R/log T` stays farther than `h` from zero. Polynomial
derivative bounds suffice; differentiating the remainder is unnecessary.
For a smooth taper, integration by parts replaces endpoint terms by
taper derivatives. Bounds of size `T^(1/2+θ+ε)` for these terms would
be negligible for every fixed `θ<1/2`. These derivative and taper bounds,
and the differentiated gcd main-term limits, remain unproved here.

## Lean status

Inputs above are existing results. No unconditional detector gate from
these inputs is yet claimed.

`MultiscaleMollifiedZetaField/RealParameterErrorsKeepTheirDerivatives.lean`
proves the local estimates
`|f'|≤2E/h+M₂h/2` and
`|f''|≤4E/(hk)+M₂k/h+M₃h/2`, obtained by rescaling the existing
unit-interval Landau inequality twice. The second estimate needs only a
third-derivative bound. Direct Lean check passed; umbrella import added.

`TheTwistedMomentHasPolynomialDerivatives.lean` is an uncompiled actual-moment
continuation: replace `|F(1/2−d+it)|²` by
`F(1/2−z+it)F(1/2−z−it)`. For real coefficients these agree at real `z=d`.
On `|Re z|≤1/4`, `|Im z|≤1`, its modulus is at most
`(q−p+2η)[(2+8(q+η+1))N]²`, when `p−η≥4`.
Cauchy's radius `1/8` then bounds its order-`n` displacement jet at
`0≤d≤1/20` by `n!·8^n` times this polynomial. The source of holomorphy
is the existing Cauchy-dominated integral theorem.

For the main term, complexify the two finite gcd sums. Their norms are
at most `N²` for `0≤Re z≤1/4`. The entire residue factor `(s−1)ζ(s)`
is bounded on a fixed disk about `1`, while the proved chi-modulus formula
gives `|χ(1/2−z±it)|≤e(|t|+2)` on the relevant strip.
These yield a proposed main-term bound
`C N²(q−p+2η)(1+e²(q+η+2)²)/d` on `|z−d|≤d/2`.
Cauchy then supplies the missing polynomial derivative control for `d≥1/T`.
This main-term continuation and bound are not yet formalized.
