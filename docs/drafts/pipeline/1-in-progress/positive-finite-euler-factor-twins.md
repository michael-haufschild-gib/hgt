# Positive finite-factor twins and the Euler growth threshold

- **ID:** positive-finite-euler-factor-twins
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Γ15.
- **Target:** Positive bounded multiplicative coefficients and a scalar Selberg
  functional equation do not exclude zeros off the critical line; the logarithmic
  prime-power bound in the Euler axiom remains essential.

For a prime `p`, put
`D_A(s)=ζ(s)[1+A p⁻ˢ+p p⁻²ˢ]`, `A≥0`.
Its coefficients are `1+A·1_(p∣n)+p·1_(p²∣n)` for `n≥1`.
They are positive, bounded, multiplicative, normalized, and agree with those of
`ζ` below `p`. Its completion is
`Λ(s)[pˢ+A+p^(1−s)]`, with conductor `p²`; the bracket is reflection-even.

Writing `t=pˢ`, the new zeros solve `t²+At+p=0`.
They all lie on the critical line exactly when `0≤A≤2√p`.
At equality they are double. For `A>2√p`, two reflected vertical arithmetic
progressions leave the line. For `p=2`, `A=17/6`, the roots are `−3/2` and `−4/3`,
so both progressions lie strictly inside the critical strip.
For `A=9/2`, the roots are `−4` and `−1/2`; the zero
`2+iπ/log 2` directly contradicts the full carrier's exponential Euler identity
on `Re s>1`.

For any `ρ>1/2`, choosing `A=p^ρ+p^(1−ρ)` gives logarithmic coefficients
`b(p^k)=[1+(-1)^(k+1)(p^(ρk)+p^((1−ρ)k))]/k`.
Their exponential rate is `p^ρ`, excluding every Euler bound with exponent
`θ<1/2`. The finite-order continuation and extended-class carrier are formalized;
the Euler exclusion still requires the coefficient-identification audit.

## Exact completion target

Construct the degree-one extended Selberg carrier for every prime `p` and real
`A≥0`, including its finite-order regularization. Prove coefficient positivity,
boundedness, multiplicativity and the prescribed coefficient prefix. Classify
the zeros introduced by the quadratic factor and certify the logarithmic
Euler-coefficient growth threshold. This does not assert a counterexample to
the full Selberg axioms: the strict Euler growth axiom must be tested explicitly.

The corpus already supplies degree-three interpolation twins and a positive
degree-two Epstein twin with nonmultiplicative coefficients. Neither gives the
positive multiplicative degree-one example or its exact local Euler obstruction.

## Algebraic boundary

Let `t=pˢ`. The added zero equation is `t²+At+p=0`. For `A≥0`,
every root has `|t|=√p` exactly when `A≤2√p`: the nonreal roots are
conjugate; real roots collide at `−√p` and split into reciprocal negative
roots beyond that threshold. Thus every added zero is critical below the
threshold and every added zero is off-line above it.

For `r>0`, set `A=r+p/r`. The explicit zero is
`(log r+iπ)/log p`, with its reflected progression at real part
`1−log r/log p`. Choosing `√p<r<p` puts both progressions in the strip.
The completed factor is `pˢ+A+p^(1−s)`, so the ordinary completion has
Gamma data `Q=p/√π`, `λ=1/2`, `μ=0`, root number one, conductor `p²`.

Write `α,β` for the quadratic roots, so `αβ=p`, `α+β=−A`.
The local logarithmic coefficients are `(1−α^k−β^k)/k` at `p^k`.
Their predicted sharp exponential rate is `max(|α|,|β|)`, at least `√p`. In the real-root
case even powers give the lower bound directly. For conjugate roots,
`u_k=(α^k+β^k)/p^(k/2)` satisfies `u_(2k)=u_k²−2`, so one of
`|u_k|,|u_(2k)|` is at least one. This supplies arbitrarily large lower
bounds and excludes every strict Euler exponent `θ<1/2`.

A root-free obstruction follows from the same identity: if
`|(1−u_k)/k|≤C p^(θk)` with `θ<1/2`, then `u_k/p^(k/2)→0` and
`u_(2k)/p^k→0`. Dividing `u_(2k)=u_k²−2p^k` by `p^k` gives `0=−2`.
Thus the strict Euler bound fails even when all added zeros are critical.
Lean integration must identify these coefficients with any purported full
Selberg logarithm; the algebraic obstruction alone is not a class exclusion.

## Remaining proof obligations

Certify the critical-circle threshold, the degree-one completion and the
strict Euler-growth obstruction. Identify the computed logarithmic
coefficients with every purported full Selberg carrier before using the
obstruction. The full Euler-constrained face remains open until that audit.
