# PW-B global Mellin dual-density estimate

- **Stage:** 5-failed
- **Status:** Narrow estimate excluded in Lean; targeted leaf build, all seven public-name checks and final formal lint passed. PW-B remains live and RH unproved.
- **Failed conjecture:** The literal Mellin kernel has finite squared dual mass for the reversible source norm at some complex argument, supplying a global weighted Cauchy–Schwarz constant.

For g=M/Q and w=exp(-x-1/x)/x, the kernel is k_s=x^(s-1)Q.
Its exact squared dual density is x^(2 Re s)*exp(-x+1/x). For every
complex s this density is nonintegrable on0<x<1. The full exponential
factorial bound gives a positive multiple of a nonintegrable power as a
lower bound. Thus the proposed finite global dual-mass constant never exists.

## Strongest positive survivor audited here

The [exact source-domain theorem](../3-formalized/pw-b-gamma-mellin-dual-domain.md)
proves the dual-density identity, its absolute admission on every compact
interval bounded away from zero, and finite weighted squared norm of every
complete arithmetic source g_z, for every complex z. No arithmetic source
term is discarded. This separates actual source-vector admission from the
proposed global norm estimate for spectral evaluation.

Paper proof and all seven Lean declarations are closed in the checked source.
The exact leaf is promoted and wired once; targeted build passed in57s and final formal lint passed.
This card does not assert that every Mellin reader is unbounded: a theorem
about arbitrary continuous extensions additionally needs Riesz identification
or explicit normalized test vectors. It does not exclude source-specific
endpoint bounds, compact tests, stronger domains or justified weak readers.
