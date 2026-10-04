# PM negative mixed prime-current escape

- **Status:** formalized and audited, 2026-10-04.
- **Route:** PM; complete signed prime-update compensation remains open.
- **Module:** `formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusNegativePrimeCurrent.lean`.

## Actual objects and results

Let `F_<p,epsilon` be the literal canonical core retaining all primes below p.
The actual weighted mixed density is

`m_epsilon(p,t) = p^(-epsilon)*Re(F_<p,epsilon(t)*conj(F_<p,epsilon(p*t)))`.

Define its negative part above horizon 1/N by

`Mminus_epsilon(N) = sum_(p<=N prime) integral_(1/N,infinity) max(-m_epsilon(p,t),0) dt`.

For every sufficiently small positive epsilon, positive constants satisfy:

1. Eventually for every natural P and every `4/(7P^2)<t<=2/(3P^2)`, the negative density is at least `c*P^(3-4*epsilon)/log(P)^3`.
2. The integrated negative part for each such P, above `1/(2P^2)`, is at least `c'*P^(1-4*epsilon)/log(P)^3`.
3. Eventually `Mminus_epsilon(8P^2) >= c''*(2P)^(2-4*epsilon)/log(2P)^4`.
4. For every real `kappa<1-2*epsilon`, `Mminus_epsilon(8P^2)/(8P^2)^kappa` tends to infinity.

No RH or L2-admission premise occurs. All finite-core mixed densities are
integrable; the positive-part integrals are genuine finite quantities.

## Proof

The actual square-band core is uniformly negative, of size
`P^(2-2*epsilon)/log(P)^2`. Its prime-dilated first-band partner is
uniformly positive, of size `P^(1-epsilon)/log(P)`. These sources are real,
so their product and the prime-update weight give the density bound.
The reciprocal slab has length `2/(21P^2)`, yielding the per-threshold
integral. Every prime in `(P,2P]` has its whole slab above `1/(8P^2)`.
The existing prime-shell count supplies the extra `P/log(P)` factor.
Positive powers dominate logarithms, proving all stated real exponents.

## Audit

- Eleven exports, all indexed and wired once into RHTower.
- Targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusNegativePrimeCurrent:olean` passed; only this leaf newly built.
- Final `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusNegativePrimeCurrent.lean` passed with empty output.
- Separate `/tmp` audit of all exports reports only `propext`, `Classical.choice`, `Quot.sound`.
- Global lint reports twelve unrelated unreachable modules, no PM failure; not a global lint pass.
- No numerical experiment, added axiom, placeholder, resource-limit increase, umbrella build, commit or push.

## Frontier implication

A separate subpower budget for the negative mixed current is false.
The positive survivor is the quantified actual paired-source law and its
integrated mass. The complete signed expression can cancel these large
parts; its lower bound `M-Q/2 >= -C_epsilon` is still unresolved.
