# TG: prime-only support of the complete jet fibre

- **ID:** tg-prime-only-jet-lcm-support
- **Stage:** 5-failed
- **Route:** TG, C9.12a
- **Status:** false support conjecture; exact positive survivor formalized

## Failed statement

The complete LCM self-convolution of the literal prime-count Möbius jet
`j(n)=mu(n)*omega(n)` was conjectured to have prime-only support.
The corpus divisor identity `sum_(d|n)j(d)=-1_IsPrimePow(n)` instead forces
its complete LCM self-convolution to be exactly `-j(n)`. For distinct primes
p,q, `j(p*q)=2`, so this fibre is -2, not zero. The semiprime specialization
is a paper deduction; the all-n signed identity is the audited Lean result.

## Strongest positive survivor

The complete two-coordinate incidence fibre has the exact law

`H(n;k,m)=sum_(r|n)mu(n/r)*1_IsPrimePow(gcd(r,k))*1_IsPrimePow(gcd(r,m))`.

The diagonal is `-j(n)*1_(n|k)`, and H vanishes outside n|k*m. Finite
transport to every real two-coordinate kernel retains all high LCM labels.
For the actual Sonin reciprocal-maximum kernel, the resulting centered
formula retains the original polar cell masses, all proper prime powers
and both cross terms. It equals cumulative energy plus the terminal square.

The dependency-closed paper proof and successful final Lean leaf are in
`3-formalized/tg-prime-count-jet-lcm-covariance.md` and
`formal/GaloisForLFunctions/RHTower/SoninPrimePolarJetLcmCovariance.lean`.
The argument supplies no bound on the source norm: energy finiteness is
an active hard problem. This does not retire TG or falsify RH.

- 2026-10-03 — Negative support conjecture closed together with its exact
  signed physical-kernel survivor; final leaf audit exits 0.
