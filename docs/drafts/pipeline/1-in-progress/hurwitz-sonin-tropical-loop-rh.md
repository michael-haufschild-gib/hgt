# Hurwitz--Sonin tropical closed-loop route to RH

- **ID:** `hurwitz-sonin-tropical-loop-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Consumer:** `../3-formalized/not_new_scientific_knowledge/xi-hurwitz-tropical-sonin-loop-rh-criterion.md`
- **Source normal form:** `../3-formalized/ccm-sonin-finite-word-tropical-normal-form.md`
- **Phase source:** `XiHurwitzPrincipalPhaseGrowth.lean`

## Claim

Construct, from finite separated continued prime--Gamma/Hurwitz source packets alone, a closed word
of genuine Sonin Gram factors whose canonical normal-state path has endpoints `3` and middle scale

```text
2+(1+alpha)^(-1),
```

where `alpha` is identified only in the comparison theorem with the supremal principal Hurwitz
phase.  Prove from the closed source relations that this word is compactly equal to the direct
endpoint Gram operator.  The tropical normal form then forces the interior minimum to equal the
endpoint, so `alpha=0`; the exact phase law gives RH.

This is a static inverse-semigroup constraint.  No positivity, spectral flow, or all-level
divisibility is used.

## Two-ended chain

```text
continued prime--Gamma/Hurwitz source packets
  -> genuine finite word of Sonin Gram corners
       [OPEN CORE A: source word construction]
  -> canonical closed scale path P_src
       [faithful finite-word normal form is PROVED]
  -> source relations absorb P_src to its direct endpoint operator
       [OPEN CORE B: compact endpoint absorption]

principal Hurwitz monodromy phase
  -> exact positive transverse Xi displacement
  -> supremal phase alpha
       [PROVED]
  -> comparison identifies normal state of P_src with
       3 -> 2+(1+alpha)^(-1) -> 3
       [OPEN CORE C: source/phase comparison]
  -> endpoint absorption iff alpha=0
       [PROVED LEAN]
  -> RH
       [PROVED LEAN].
```

## Why this is independent of the source-sign routes

The Calkin inverse semigroup retains an interval minimum as a tropical memory coordinate.  A
positive phase appears as a strict interior dip, and no cancellation of scalar energies can erase
it.  The desired theorem is equality of two operator classes, not nonnegativity or a growth bound.

## Candidate source words

1. `[CONJECTURE]` Use a separated two-pole continued-Cauchy packet and its FE reverse as the two
   edges of a closed Sonin word.  The middle scale should be the modulus of the normalized Hurwitz
   monodromy character after a fixed monotone reparameterization.
2. `[CONJECTURE]` Use the exact rectangular two-edge source: its two adjacent critical-Mellin tents
   give the outward and return edges, while the prime--Gamma cancellation supplies endpoint
   absorption.
3. `[CONJECTURE]` Use the Wigner--Eisenstein orientation current to choose the middle shell and the
   Sonin inverse to close the path.

The first candidate is smallest.  It must be built for a cofinal source sequence and shown to
converge in the Calkin normal-state topology without target selection.

## Firewalls and positive residues

### The formal loop is target-defined

`XiHurwitzTropicalSoninLoop.lean` deliberately defines the middle scale from the Xi phase.  This is
only the consumer end.  Reusing it as the source word is circular.

**Positive residue:** the source obligation is an explicit finite Gram word plus a comparison of
its normal-state minimum with the Hurwitz character phase.

### Arbitrary paths can encode any scalar

The Sonin inverse semigroup is faithful enough to store an arbitrary chosen minimum.  Its memory
alone supplies no arithmetic restriction.

**Positive residue:** endpoint absorption must follow from a prime--Gamma/Hurwitz word relation,
not from choosing a path with equal minima.

### Compactness of each factor is false

Every nonempty composable Sonin path operator is noncompact.  The relevant conclusion is compact
equality of the full closed word with the direct endpoint Gram entry, not compactness of the word
itself.

**Positive residue:** the exact target is the already formalized endpoint-absorption relation in
the Calkin algebra.

### Target-selected Cauchy reconstruction is insufficient

The universal continued-source reconstruction currently selects packets through the Xi divisor
Hilbert closure.  Such a selection may identify the loop after reading `alpha`, but cannot prove RH.

**Positive residue:** a source-only packet schedule or an algebraic finite-word identity is the
essential new theorem.

## Status

- `[PROVED]` the principal Hurwitz phase is the exact transverse Xi coordinate;
- `[PROVED]` the Sonin Calkin inverse semigroup faithfully remembers finite path minima;
- `[PROVED]` the phase-coded closed path is endpoint-absorbed exactly under RH;
- `[OPEN CORE]` construct a source-only genuine Gram word with that normal state;
- `[OPEN CORE]` prove source endpoint absorption and cofinal compatibility;
- `[CLOSED SHORTCUT]` arbitrary phase-to-path encoding without a source word.
