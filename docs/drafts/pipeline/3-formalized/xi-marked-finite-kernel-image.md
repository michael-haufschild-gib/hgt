# Finite images contain the full marked zero-winding kernel

- **ID:** RH-XIFK-20261007
- **Stage:** 3-formalized
- **Parent:** `../1-in-progress/xi-logarithmic-islands-monodromy.md`
- **Verdict:** BRIDGE; novelty uncertified; no RH conclusion

## Exact result

Let A be any finite real slope set, V=C minus {0,-1}, and U the actual
source excluding xi=0 and d_a=-1 for a in A, where d_a(s)=xi(s)*exp(-a*s).
Base U at0 and every V coordinate at1/2. Write mu for the actual coordinate
fundamental-group map, and w for winding about0 on pi1(V,1/2).

Every tuple q with w(q_a)=0 has f(q) in f(image(mu)) for every homomorphism
f from the product target group to any finite group. Also every tuple in
image(mu) has the same winding in every coordinate. These are unconditional
actual-source results; finite f need not be onto and A may be empty.

The stronger exact image equality with the diagonal-winding subgroup still
needs its primitive diagonal generator and final assembly in Lean.

## Proof

Choose path representatives for a finite packet in one coordinate kernel.
The actual inverse-disk packet theorem realizes them at a common source
point, at target basepoint1/2. One connecting path from source0 supplies
one conjugator for the whole packet. Other coordinates remain nullhomotopic
under transport. Apply the finite normal-packet theorem to the preimage of
the actual joint range under the coordinate embedding. Finite products of
single-coordinate kernel elements give the full product inclusion.

For the upper inclusion, the existing Bottcher winding product law and
vanishing for an exponential give w(d_a composed with p)=w(xi composed with p)
for every source loop p. NormalizedWindingHom packages that same invariant
on actual fundamental groups; PointedPacketTransport retains the exact
common conjugator, including mathlib's reverse path multiplication order.

## Formal audit

- `HTGeometry/NormalizedWindingHom.lean`: four public declarations.
- `HTGeometry/PointedPacketTransport.lean`: three public declarations.
- `RHTower/XiMarkedMonodromyMap.lean`: seven public declarations.
- `RHTower/XiMarkedConjugatePackets.lean`: three public declarations.

Targeted builds and all four actual-source checks pass. All17 public axiom
closures use only propext, Classical.choice, Quot.sound. Imports unique;
no admissions or heartbeat changes. Matching proof scratches removed.

Evidence: `/tmp/rh-NormalizedWindingHom-build.log`,
`/tmp/rh-marked-winding-build.log`, `/tmp/rh-XiMarkedConjugatePackets-build.log`,
`/tmp/rh-final-NormalizedWindingHom.log`, `/tmp/rh-final-PointedPacketTransport.log`,
`/tmp/rh-final-XiMarkedMonodromyMap.log`, `/tmp/rh-final-XiMarkedConjugatePackets.log`,
`/tmp/rh-marked-kernel-axioms.log`. The last global lint report still has the
five unrelated unreachable modules recorded on the packet child; a new
index/lint pass will follow the ongoing meridian assembly.
