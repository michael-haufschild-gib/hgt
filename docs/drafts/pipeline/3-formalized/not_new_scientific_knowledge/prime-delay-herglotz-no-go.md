# A raw prime delay is not a passive impedance

- **ID:** `prime-delay-herglotz-no-go`
- **Stage:** `3-formalized`
- **Type:** `[PROVED] [FORMALIZED] [NO-GO] [POSITIVE SUCCESSOR] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeDelayHerglotzNoGo.lean`
- **Route:** `../../5-failed/dyadic-prime-passive-impedance-network-rh.md`

## Theorem

For every `lambda>0`, let

`D_lambda(z)=exp(i lambda z)`.

The two points

`z_+=pi/(2 lambda)+i`,
`z_-=-pi/(2 lambda)+i`

lie on the same horizontal line in the upper half-plane, while

`Im D_lambda(z_+)= exp(-lambda)>0`,
`Im D_lambda(z_-)=-exp(-lambda)<0`.

Consequently `D_lambda` does not map the upper half-plane into its closure and cannot itself be a
Herglotz/Nevanlinna driving-point impedance.  In particular, the individual Euler delay
`exp(i z log p)` is not a passive scalar channel for any prime `p`.

## Positive successor after terminal route audit

At this card's original stage, nonlinear coupling remained a possible successor.
`CCMSharpPrimeWindowPassiveNoGo.lean` now closes that possibility for any scalar response which
equals the literal source on the initial overlap: the full source itself takes both imaginary signs
above every height.  The positive Gram in `CCMComplexMellinColligation.lean` remains valid, but it
can only support a nontrivially transformed response.  A Cayley/renormalized response must prove a
new source-only inverse handoff to the literal source and therefore belongs to a new route.

## Formal certificate

Lean proves:

- `primeDelayUpperPoint_im`;
- `primeDelayMode_upperPoint_one`;
- `primeDelayMode_upperPoint_neg_one`;
- `primeDelayMode_not_upperHalfPlaneValued`.

The public declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] exact two-point sign reversal proved
- [x] upper-half-plane membership proved
- [x] raw-delay Herglotz shortcut closed
- [x] positive nonlinear colligation successor stated
- [x] Lean build and axiom audit passed
