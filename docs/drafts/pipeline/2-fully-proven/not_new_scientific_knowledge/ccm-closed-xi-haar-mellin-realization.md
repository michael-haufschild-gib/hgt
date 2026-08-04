# Closed CCM--Xi Haar--Mellin realization

- **ID:** `ccm-closed-xi-haar-mellin-realization`
- **Stage:** 2-fully-proven
- **Type:** dependency-closed bridge
- **Parent:** `ccm-clifford-bivariant-weil-product.md`
- **Novelty verdict:** exact bridge between two existing local constructions; not standalone new
  scientific knowledge

## Theorem

Let `C` be degree zero of the literal closed nonunital rational CCM relative cyclic module.  For
each support point `rho` of the complete Xi divisor, Haar--Mellin evaluation at `rho` descends to a
nonzero linear functional

```text
ell_rho : C -> C.
```

For a multiplicity copy `q`, put `E(x)_q=ell_(q.support)(x)`.  Thus `E` repeats a support value
exactly according to analytic multiplicity.  Define

```text
Q_C(x,y) = sum_q E(x)_q conjugate(E(y)_(Jq)),
```

whenever the displayed series is summable, where `Jq` is critical-line reflection.  If functions
`F,G : C -> C` realize the two evaluation packets,

```text
E(x)_q = F(alpha_q),    E(y)_q = G(alpha_q),
```

then

```text
Q_C(x,y) = Weil(F,G)
```

on the actual multiplicity-exact Xi divisor.  In particular this is an equality on the literal
closed CCM quotient, not a comparison between an abstract CCM model and a separately postulated
divisor carrier.

## Proof

Fix a Xi-divisor support point `rho`.  Divisor support gives `xi(rho)=0`.  Every such point lies in
the open strip `0<Re(rho)<1`, so `rho != 1`; the standard completed-factor identity therefore gives
`zeta(rho)=0`.  The rational-adelic Meyer boundary law says that Haar--Mellin evaluation at every
positive-half-plane non-pole zeta zero annihilates the exact reduced source.  Continuity of this
functional then makes it annihilate the topological closure of the exact restriction range.
The universal property of the quotient gives `ell_rho`.

The explicit log-Gaussian target chain has nonzero Haar--Mellin value at every spectral parameter.
Consequently its quotient class is not killed by `ell_rho`, so every `ell_rho` is nonzero.  Passing
from support points to multiplicity copies by pullback along `q -> q.support` gives `E` and retains
analytic multiplicity exactly.

For the pairing identity, critical-line reflection satisfies
`alpha_(Jq)=conjugate(alpha_q)`.  Substitute the two realization identities term by term:

```text
E(x)_q conjugate(E(y)_(Jq))
 = F(alpha_q) conjugate(G(alpha_(Jq)))
 = F(alpha_q) conjugate(G(conjugate(alpha_q))).
```

Summing is precisely the definition of the multiplicity-exact Weil polarization.  No positivity,
RH, zero simplicity, spectral enumeration, or surjectivity/density of `E` is used.

## Hostile audit

- This theorem closes well-defined descent and exact numerical identification.
- It does **not** prove that `E(C)` is dense in the Weil `ell^2` domain.
- It does **not** make `Q_C(x,x)` nonnegative.
- Product-topology density of compact-open Xi jets does not imply the required `ell^2` density.
- A positivity statement on the full square-summable realization remains equivalent to RH.

## Gates

- [x] dependency-closed paper proof
- [x] exact literal recipient
- [x] multiplicity audit
- [x] circularity audit
- [ ] unconditional Lean verification
