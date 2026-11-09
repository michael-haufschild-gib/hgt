# Simultaneous logarithm bounds with explicit collective parameters

- **ID:** CDG-SIM
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** A rank-sensitive simultaneous lower bound for independent
  integer forms in any finite family of distinct prime logarithms.

## Statement

Let `p_1,…,p_k` be distinct primes, `M∈ℤ^(r×k)` have rank `r≥1`,
`H≥1`, and `|M_ij|≤H`. Write `L_i=Σ_j M_ij log p_j` and
`W=ceil(Σ log p_j)+1`. Set `d=k−r`, `h=floor(d/r)+1` and

`L=2+h(k+1)(floor(log₂(1000Wk))+1)`,
`J=h(k+1)+k`, `R=L+2J(floor(log₂(L+J+1))+1)`,
`E=1000Wk(R+1)`, `q=E^h(R+1)`, `Q=kq`,
`M₀=1000WQ`, `S=RM₀+1`, `c=16k(R+1)Q`, `a=2cE^h`, `Z=2^R c`.

Define the explicit positive coefficient

`C′=kS(1+2Q)+4a+2kQ+c(1+QW)+2(a+1)(19+12R)`
`    +Z(18+8QW+16Q+10M₀²)+5+M₀(S+W+1)`.

Then some row satisfies

`|L_i| ≥ exp(−(C′+1)(log(r!H^r)+2))/(r·r!H^(r−1))`.

The stronger normalized statement is

`Σ_i |(B⁻¹L)_i| ≥ exp(−(C′+1)(log|det B|+2))`,

where `B` is a maximal absolute column minor. These constants depend on
rank, dimension and prime mass; coefficient height enters through `log H`
and the displayed elementary factor. The root degree `h` and parameter
polynomial degree `J` are retained throughout; `J≤3k+2` when `r≥k−r`.

## Proof

**Integral construction.** Use the normalized projection and explicit
parameters of [CDG-AUX](../3-formalized/cdg-collective-auxiliary.md).
For every `n≥1`, there is a nonzero integer auxiliary with polynomial degree
`N=an`, exponent box `[0,q)^k`, and exact initial companion-jet vanishing
at `x<cn`, for all free jet orders below `S`. Its coefficient height is
bounded by the explicit integer Siegel estimate. A true value before
`(N+1)q^k` is nonzero.

**Analytic family.** Put `D=det B`, `λ=Σ_i |(B⁻¹L)_i|`. The free projected
frequency differs from the true frequency by `u B⁻¹L`, hence by at most
`qλ`. The free-coordinate weights have size at most `(r+1)q≤2Q`.
Their logarithmic mass is at most `W`. The differential identity

`F′_(σ,τ)=(σ+1)F_(σ+1,τ)+Σ_j log p_(t_j) F_(σ,τ+e_j)`

keeps all derivatives within the `d` free directions. The scalar growth
and perturbation majorants apply with analytic box `Q`; the actual
integer system and terminal interpolation continue to use `q`.
The collective coefficient height is bounded by the scalar majorant at
`Q`, since `d≤k−1`, `r+1≤2k`, and `|D|≥1`.

**One step.** If the true jets of total order below `T` vanish at `x<X`,
the analytic jets there are bounded by their frequency perturbation.
Iterated diagonal derivatives are bounded by `(T+W)^M₀` times that error.
Hermite–Schwarz on the circle `|z|=8X` gives the contraction
`(2/7)^(M₀X)` at `x<2X`, consuming `M₀` jet orders.
Clearing `D^|τ|` makes each companion value an integer multiple of the
Fel'dman divisor. A value below that arithmetic unit must vanish.

**Numerical gain.** Take `n=ceil(log|D|)+1`. If
`λ<exp(−(C′+1)n)`, the frequency-error hypothesis holds throughout
`X≤2^R cn`, because `C′≥16ZQ`. The parameter gain inequality makes the
growth contribution at most half the divisor at every stage. The
perturbation contribution is strictly below the other half: after division
by the common divisor, its majorant is at most `λ exp(C′n)<exp(−n)≤1/2`.
All constants in this inequality are the displayed parameters; no analytic
estimate is assumed as an input.

**Contradiction and original forms.** The `R` steps leave jet order one
and zeros at all `x<2^R cn`. Since `2aq^k≤2^R c` and `an≥1`, this covers
`(an+1)q^k`, contradicting the nonzero true value. Also
`n≤log|D|+2`, proving the normalized bound. Finally,
`|D|≤r!H^r` and each adjugate entry is at most `(r−1)!H^(r−1)`.
Consequently `λ≤r·r!H^(r−1) max_i |L_i|`; substitution gives the result.

## Contribution and boundary

This completes the collective auxiliary method for simultaneous small
forms. The integer equation count is `XS^(k−r+1)` throughout, instead of
reverting to `XS^k`. The bound holds for unrestricted dimensions and
coefficient heights. The elementary full-rank floor and scalar reductions
remain separate, useful bounds near full rank.

It does not yet count return heights or prove constant-precision breadth.
A linear form acts on a return through its coefficient height times phase
error. That loss remains part of the breadth problem.

## External benchmark

For distinct primes `p_j≤y`, an integer `r×k` matrix of rank `r`, and
`|a_ij|≤H`, put `L_i=Σ_j a_ij log p_j`, where `H≥1`, `1≤r≤k`.
Theorem 1.1 of [Gaudron (2014), pp. 2–3](https://lmbp.uca.fr/~gaudron/art12.pdf)
specializes to

`max_i |L_i| ≥ exp(−G)`,

`G=(10k)^(58k²/r) A^(1/r) (max(1,log H)+A) (1+e log y)^(k/r)`,

`A=floor(log(e+1+ek log y))+1`.

Here the number field is `ℚ`, the theorem's exponential parameter is `e`,
`log a=e log y`, and `log b=max(1,log H)`.
Unique factorization supplies independence of the prime logarithms.
This is an external theorem, not a new result or a Lean dependency.
The 2012 arXiv text has different constants; the formula above uses the
published version.

## Lean

`CollectiveExtrapolation.lean` proves the actual free-direction analytic
identities, error bounds, arithmetic small-value step, and doubling.
`CollectiveLogarithmBound.lean` proves the closed bound in
`exists_explicit_collective_logarithm_bound`.

Both modules passed direct `lake --old env lean` verification. Axiom audits
of the capstone, `collective_pivot_bound_of_params`,
`collective_extrapolation`, and `collective_stage_threshold` use only
`propext`, `Classical.choice`, and `Quot.sound`.
