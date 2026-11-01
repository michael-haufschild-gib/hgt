# Positive finite-factor twins and the Euler growth threshold

- **ID:** positive-finite-euler-factor-twins
- **Stage:** 0-backlog
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
`θ<1/2`. Finite-order continuation and the exact rate require Lean certification;
no class-membership or novelty claim is certified yet.
