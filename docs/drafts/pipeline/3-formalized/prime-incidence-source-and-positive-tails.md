# Prime incidence source and positive tails

- **ID:** critical-rigidity-prime-incidence-source
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Identify literal prime dilation and complementary-tail sources in centered divisibility coordinates.

## Exact arithmetic coordinates

For a prime `p`, set `w_p=sqrt(p−1)/p` and `e_p=c_p/sqrt(p−1)`. The prime Ramanujan formula gives

`w_p e_p(n)=1_(p∣n)−1/p`.

Consequently the packet with coefficients `w_p b_p` has dilation jump

`F_b(kn)−F_b(n)=Σ_(p≤Q) b_p 1_(p∣k, p∤n)`.

The prime divisor jet equals `log p(c_p+1)`. Subtracting the exact adjunction diagonal therefore gives

`G_Q F_b(n)=Σ_(p≤Q) b_p log p/(p−1) · 1_(p∤n)`.

These are identities for the actual arithmetic source, with no averaging or replacement weights.

## Complementary tails

Define `r_p(y)=log p/(p−1)−Σ_(k≤y,p∣k) Λ(k)/k`. The proved reciprocal Mangoldt bound gives `r_p(y)≥0`. If `y<p`, the finite sum is empty, so `r_p(y)=log p/(p−1)`.

Subtract the finite prime head from the generator identity and exchange the two finite sums. The result is

`Tail_Q(b;y,n)=Σ_(p≤Q) b_p r_p(y) 1_(p∤n)`.

For `b_p=1`, every tail is nonnegative. If `y≤P`, the contribution of all primes above `P` is exactly their complete tower mass, while omitted terms are nonnegative. Hence

`Tail_Q(1;y,n)≥Σ_(P<p≤Q) log p/(p−1) · 1_(p∤n)≥0`.

This supplies the source-preserving lower input used in `sharp-relative-prime-residual-scale.md` to prove the matching quadratic-logarithmic residual scale. No complete-Weil obstruction follows from these source identities.

## Lean

`CriticalScaleArithmeticRigidity/PrimeCoherenceCalculus.lean`: `primeIncidencePacket_dilation_jump`, `primeIncidenceGenerator_eq`, `completedPrimeDilationTail_primeIncidence_eq`, `highPrimeCoherentSource_le_completedTail`. Direct audit passed; only `propext`, `Classical.choice`, `Quot.sound`.
