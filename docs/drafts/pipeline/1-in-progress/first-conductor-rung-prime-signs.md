# The first conductor rung forces both prime signs

- **ID:** A108
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** For every `η > 0`, every sufficiently large conductor `q`, and every real
  primitive character `χ` modulo `q`, positivity of its zero form on packets of aperture
  `log log q + η` forces primes with `χ(p)=1` and `χ(p)=-1` below `exp(2η) log²q`.

## Proof obligations

Use the two polar packets at the smaller aperture `a = log log q + η/2`.
`exists_riesz_twist_le_of_nonneg` gives

`|Rχ(a)| ≤ (log q + π)(exp a + 2a) + C(1+a)³ exp a`.

If either prime sign is missing below `Y=exp(2a)`, all unramified primes there have the
opposite sign `s`. On primes the error between `Λ Re χ` and `sΛ` is supported on conductor
divisors. Their total von Mangoldt mass is at most `log q` by `vonMangoldt_sum`.
All nonprime terms cost at most twice their von Mangoldt mass. Hence

`|Rχ(a) - s RΛ(a)| ≤ 2a log q + 4a exp a (4a + 4 log 4 + 16)`.

Here the second term follows from `RHTower.sum_nonprime_vonMangoldt_div_sqrt_le`,
`sqrt n ≤ exp a`, and `log ⌊exp(2a)⌋ ≤ 2a`.
The prime number theorem gives `RΛ(a) ≥ (1-ε)exp(2a)` for any fixed `ε>0` eventually.
Choose `1-ε>exp(-η/2)`. Since `log q=exp(-η/2)exp a`, the two bounds contradict each other
for large `a`; the remaining errors are polynomial in `a` times `exp a`.
Finally `Y=exp(η)log²q<exp(2η)log²q`.

## Status

Riesz producer, prime-number-theorem floor, and proper-prime-power bound exist in Lean.
Finite character comparison, conductor-divisor bound, and final asymptotic assembly remain.
The argument retains the odd archimedean correction `π`; ramified primes do not count as
either requested sign.
