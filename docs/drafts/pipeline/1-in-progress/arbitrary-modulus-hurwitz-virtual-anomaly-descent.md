# Arbitrary-modulus Hurwitz virtual-anomaly descent

- **ID:** `arbitrary-modulus-hurwitz-virtual-anomaly-descent`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[OUTLANDISH DETOUR]`
- **Formal no-go:** `../3-formalized/not_new_scientific_knowledge/weyl-packet-amplification-blindness.md`
- **Character-line no-go:** `../3-formalized/not_new_scientific_knowledge/weyl-common-character-line-nogo.md`
- **Tate no-go:** `../3-formalized/not_new_scientific_knowledge/cyclic-regular-tate-blindness.md`

## Claim

For each modulus `q`, the rational Hurwitz distribution packet should be lifted to its finite
clock--shift module and then reduced by a **source-defined virtual determinant anomaly**, not by
ordinary rank or projection to the scalar character.  The intended anomaly must cancel the regular
`q`-fold packet contribution while retaining the projective `q`-phase on the scalar local divisor
class.

This is deliberately a long detour.  No bound on `q`, chain length, or intermediate carrier is
assumed.  The output, however, must descend back to a source-pure statement about the scalar
completed zeta divisor.

## Two-ended RH chain

```text
rational Hurwitz distribution packets for every q
  -> affine/projective finite clock--shift packet
  -> source-defined virtual determinant anomaly on the scalar local class
       [OPEN CORE A: anomaly construction]
  -> anomaly phase detects the scalar local order modulo q
       [OPEN CORE B: local divisor identification]
  -> q divides every right-half scalar Xi order, for unbounded q
  -> every such order is zero
       [PROVED BRIDGE: LedgerTelescope.int_eq_zero_of_forall_pos_nat_dvd]
  -> no Xi zero has Re(s) > 1/2
  -> RH by functional-equation symmetry.
```

The last end is therefore closed conditionally: unbounded scalar-order divisibility is already
strong enough to prove RH.  The first end is not closed until the anomaly is constructed directly
from the Hurwitz distribution/source law and proved to descend to the scalar completed-zeta local
divisor.

## Firewalls

The route must not silently use any of the following false shortcuts.

### Full-packet divisibility

`dim Packet_q(V)=q dim(V)`, so `q | dim Packet_q(V)` holds for every scalar multiplicity.  This is
tautological amplification and contains no RH information.

### Scalar-character projection

A nontrivial Weyl pair has no common nonzero character line.  Projecting the packet to the scalar
zeta character destroys at least one generator and therefore loses the projective phase.

### Ordinary determinant or Morita rank

Ordinary determinant rank and normalized `K_0` rank permit arbitrary scalar multiplicity.  The
needed object must be virtual, relative, graded, or boundary-valued in a way fixed by the arithmetic
source—not chosen after seeing the divisor.

### Symmetry-only closure

Functional-equation and Schwarz symmetry permit arbitrary off-line quartets.  The anomaly must
read orientation or local order, not merely orbit symmetry.

### Untwisted cyclic Tate descent

Degree-zero Tate descent on the regular integral packet kills every invariant because it is a norm,
while on a fixed trivial lattice it leaves reduction modulo `q`.  This is exactly stabilizer/orbit
type.  It does not identify scalar zeta order modulo `q`, and assigning the fixed or regular lattice
to a zero germ would presuppose the desired orbit classification.  The surviving anomaly must use a
twisted/projective coefficient class with source-derived arithmetic gluing.

## Open core

`[CONJECTURE] [OPEN CORE A]` Find a canonical virtual packet class `A_q` extracted from the rational
Hurwitz distribution law such that the regular representation has virtual rank zero but the finite
Weyl commutator has order `q` on `A_q`.

`[CONJECTURE] [OPEN CORE B]` Prove that the local anomaly exponent of `A_q` at a completed-zeta zero
is exactly the scalar local order modulo `q`, with no contribution from complementary Hurwitz
characters, gamma factors, or conductor factors.

## Positive target forced by the no-go

The two no-go theorems do not retire arbitrary moduli.  They force a sharper construction:

> retain the projective phase in a virtual boundary/determinant class while quotienting the regular
> packet multiplicity, and prove that this quotient is source-defined and scalar-local.

That is the only currently visible way for the arbitrary-modulus detour to produce genuinely
unbounded divisibility rather than a restatement of packet size.

## Status

- `[PROVED]` full-packet rank divisibility is blind to scalar multiplicity;
- `[PROVED]` nontrivial Weyl action cannot survive on a common scalar character line;
- `[PROVED]` untwisted cyclic Tate descent reduces to stabilizer/orbit type;
- `[PROVED BRIDGE]` unbounded divisibility of an integer forces it to vanish;
- `[OPEN]` canonical source-defined virtual packet anomaly;
- `[OPEN]` identification of its exponent with scalar Xi local order;
- `[OPEN]` verification that complementary Hurwitz factors cancel canonically.
