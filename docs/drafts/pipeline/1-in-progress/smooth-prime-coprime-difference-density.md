# Coprime density of compatible smooth–prime differences

- **ID:** SPL-coprime-difference-density
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM

For smooth rows `m,n`, put `g=gcd(m,n)` and `a=m/g`, `b=n/g`.
A prime-column collision `mp+h=nq` forces `g|h` and
`gcd(h/g,ab)=1`. The cumulative balanced-row bound should therefore retain

`Σ_(1≤h≤H) #C_(m,n)(h) ≤ g #{1≤v≤H/g : gcd(v,ab)=1} ≤ H`.

Unlike the uniform gcd-cancellation envelope, this remembers prime factors
of the reduced rows. A divisor `d|ab` gives the finite periodic upper bound
`g (floor((H/g)/d)+1) φ(d)`. Choosing small divisors retains arithmetic density
without a remainder depending on the full reduced product.

The exact determinant gcd identity and per-row gcd fibre bound are already
formalized. Remaining work: reduced coprimality, the actual difference census,
and a verified periodic coprime-count estimate. This does not yet supply the
random-scale prime-density factor or an all-height saving.
