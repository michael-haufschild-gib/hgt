# Route J pure-Hodge modular transgression

- **ID:** route-j-pure-hodge-modular-transgression
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) + OPEN PRODUCER
- **Source:** `route-j-principal-relative-julia-current.md` · Section 49
- **Statement:** The actual mixed Gamma/Hardy reflection coefficient is the secondary Poincare
  trace of the reflection-odd modular orbit of a source-defined pure Hodge incidence pair.  Its
  finite trace is unconditional; its cofinal graph-capacity is uniformly finite exactly at zero
  modular displacement.

## Goal

Turn the pure-sector survivor into an unsquared oriented detector without reintroducing a mixed
finite carrier.  Operation order is forced by orientation--transgression completeness:

```text
pure incidence -> odd Hodge exchange -> reflected modular transport
               -> height-weighted Poincare trace -> scalar orientation.
```

The scalar is formed only after the vector-valued pure carrier and its reflected transport exist.

## Gates

- [x] 0 -> 1 in-progress: canonical source object, exact finite identity, hostile falsifier
- [x] 1 -> 2 fully-proven: finite transgression and cofinal graph-capacity classification
- [ ] 2 -> 3 formalized: every dependency-closed theorem in unconditional Lean
- [ ] 3 -> 4 publication-ready: standalone theorem, proof, Lean certificate, novelty audit

## Frozen conjecture — `J-PHMT`

For distinct prime/depth cells `i,j`, let

```text
D_ij = d_i wedge d_j,
P_ij = w_i wedge w_j,
H(D_ij)=P_ij,
H(P_ij)=D_ij.
```

Both pure classes are nonzero actual-admitted incidences at every displacement.  Put

```text
r_ij = rate(i)+rate(j),
B_a(D_ij)=exp(-a r_ij) D_ij,
B_a(P_ij)=exp( a r_ij) P_ij.
```

Then `H B_a H=B_(-a)`.  Therefore the reflection-odd transgression of the Hodge-fixed vector is

```text
Omega_a(i,j)
 = (B_a-B_(-a))(D_ij+P_ij)/2
 = sinh(a r_ij)(P_ij-D_ij),                         (PHMT-1)
```

which is Hodge-anti-fixed and remains in actual incidence admission.  Define the canonical
source Poincare trace by pairing the packet--packet coordinate against the defect--defect leg and
weighting by

```text
A_0(i) A_0(j) (height(i)-height(j)).
```

The exact finite identity is

```text
Tr_ij(Omega_a(i,j))
 = gamma_a(i,j)
 = partial_a(E_ij)(i,j),                            (PHMT-2)
```

where `E_ij=d_i wedge w_j` is the canonical mixed witness and `partial_a` is the actual
Gamma/Hardy reflection boundary.  Hence the pure admitted source carries the missing unsquared
mixed trace as a secondary transgression, although its primary boundary is zero.

The cofinal clause is deliberately stronger.  On the source-normal depth system, equip the pure
Hodge plane with the two-component coefficient capacity.  The graph-capacity of the balanced
orbit satisfies

```text
sup_N capacity(B_a on depths <= N) < infinity
  <-> a=0.                                           (PHMT-3)
```

For fixed prime clocks `p,q` and common depth `n`, the exact local graph capacity is

```text
C_a(p,q,n)
 = exp(-2a r_(p,q,n)) + exp(2a r_(p,q,n))
 = sewing_a(p,q,n) + sewing_(-a)(p,q,n).             (PHMT-4)
```

At `a=0`, `(PHMT-4)=2` and existing global pure capacity is at most `200*289^2`.  At `a!=0`, one
reciprocal Hodge leg tends to infinity, indeed beyond every finite Rees order, so graph-capacity
diverges.  This proves `(PHMT-3)` and supplies the required hostile falsifier: any claimed bounded
off-critical completion contradicts the source sewing asymptotics.

The positive and oriented channels are related by an exact source purity-defect identity:

```text
W_ij^2 (C_a(i,j)-2) = 4 gamma_a(i,j)^2.             (PHMT-5)
```

Thus graph-capacity does not merely correlate with the mixed defect.  Its excess above the Hodge
minimum is exactly the square of the secondary unsquared trace.  The sign remains in `(PHMT-2)`;
positive capacity sees precisely its reflection-even shadow.

## Why this is not a renamed equivalence

`(PHMT-2)` is a new chain-level factorization of an existing boundary coefficient through a
different carrier.  It explains how a boundary-silent admitted pure incidence can retain the
unsquared mixed charge: not in its primary boundary, but in the commutator between modular
transport and Hodge exchange.  No closed admission set and no critical-line condition is assumed.

`(PHMT-3)` will not by itself prove RH.  It classifies the exact topology required by the
secondary trace.  Full Route-J closure still needs the arithmetic source to place the completed Xi
Green relation in this graph-bounded sector, rather than postulating that landing.

## Novelty audit

Corpus contains separately:

- pure actual-admitted incidence and two-leg source transport;
- exact mixed-boundary Kronecker law;
- reflected modular exterior and beyond-finite-Rees sewing;
- divisor-side Frobenius--Hodge purity commutator.

Search found no theorem identifying mixed Gamma boundary as the Poincare trace of the pure-Hodge
modular commutator.  `J-PHMT` composes these ingredients at chain level and exposes its exact
cofinal topology.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedPureHodgeModularTransgression.lean
```

Key unconditional declarations:

- `pureHodgeCellExchange_balanced`;
- `pureHodgeCellOddTransgressionCoefficients_antiFixed`;
- `pureHodgeCellOddTransgression_mem_actual`;
- `pureHodgeCellPoincareTrace_eq_actualMixedBoundary`;
- `pureHodgeCellPoincareTrace_oddTransgression_eq_zero_iff`;
- `pureHodgeCellPoincareTrace_sq_eq_capacityDefect`;
- `pureHodgeBalancedGraphCapacity_eq_sewing_add_reflection`;
- `pureHodgeBalancedGraphCapacity_tendsto_atTop`;
- `pureHodgeBalancedGraphCapacity_uniform_iff`.

## Exact remaining producer

The secondary trace and its topology are no longer missing.  Route J now needs one source theorem:
the completed Xi Green relation lands in the graph-bounded pure-Hodge transgression sector.  That
landing would force every divisor displacement to be zero by `(PHMT-3)`.  It must be derived from
the prime-power source/Green chain; assuming graph-boundedness would restate the RH burden.

## Log

- 2026-08-02 — Frozen after reading the current oriented source-admission,
  orientation--transgression, Hellinger--Hodge descent, and source-horizon papers.  The papers rule
  out closed admission as a construction shortcut and force a secondary exact-boundary channel.
- 2026-08-02 — Proved `(PHMT-1)`--`(PHMT-4)`.  Constructed balanced pure-Hodge modular orbit,
  Hodge-anti-fixed odd transgression, actual admission, exact equality with mixed Gamma/Hardy
  boundary, zero-displacement trace classification, reciprocal sewing-capacity identity, and
  uniform-capacity iff theorem.  Direct Lean check passes; targeted final audit remains.
- 2026-08-02 — Proved source-side purity-defect identity `(PHMT-5)`: balanced capacity excess is
  exactly squared secondary Gamma curvature.  This is chain-level analogue of divisor-side
  Frobenius--Hodge purity defect, with unsquared sign retained before the positive shadow.
