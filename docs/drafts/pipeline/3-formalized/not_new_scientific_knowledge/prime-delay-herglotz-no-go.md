# A raw prime delay is not a passive impedance

- **ID:** `prime-delay-herglotz-no-go`
- **Stage:** `3-formalized`
- **Type:** `[PROVED] [FORMALIZED] [NO-GO] [POSITIVE SUCCESSOR] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeDelayHerglotzNoGo.lean`
- **Route:** `../../1-in-progress/dyadic-prime-passive-impedance-network-rh.md`

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

## Positive successor

The theorem retires only the termwise impedance interpretation.  It does not retire passive prime
systems.  `CCMComplexMellinColligation.lean` independently proves that the resolved von-Mangoldt
prime-power matrix is a positive semidefinite Gram on every finite complex right-half-plane packet.
Therefore passivity must be constructed after nonlinear coupling: a contractive scattering
colligation followed by a Cayley transform, an internal Schur complement, or the complete
prime--polar--critical-defect Fock response.  Raw delay modes may be internal phase channels but
not separate positive impedances.

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
