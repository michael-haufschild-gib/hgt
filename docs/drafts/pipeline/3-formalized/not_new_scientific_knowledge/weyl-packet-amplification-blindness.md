# Weyl packet-amplification blindness

- **ID:** `weyl-packet-amplification-blindness`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`, `[POSITIVE NO-GO]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/WeylPacketAmplificationBlindness.lean`
- **Successor route:** `../../1-in-progress/arbitrary-modulus-hurwitz-virtual-anomaly-descent.md`

## Theorem

Let `V` be a finite-dimensional complex vector space.  Its full `q`-component packet is

```text
Packet_q(V) = Fin(q) -> V.
```

Then

```text
dim Packet_q(V) = q dim(V),
```

so `q` divides the packet dimension for every possible scalar dimension `dim(V)=m`.

## Consequence

Divisibility of a full residue-packet dimension by `q` is packet amplification, not arithmetic
information about the scalar local divisor.  It cannot imply `q | m`.  In particular, taking larger
moduli does not force a scalar zero order to vanish merely because the unreduced packet rank is
divisible by every chosen packet size.

Together with `weyl-common-character-line-nogo`, this closes both elementary escapes:

1. keeping the full Weyl packet makes modulus divisibility tautological;
2. projecting to the scalar character line destroys the nontrivial common Weyl action.

## Positive statement from the no-go

The surviving target is precise:

> `[CONJECTURE] [OPEN CORE]` Construct a source-defined virtual determinant anomaly on the scalar
> local divisor class which cancels the regular `q`-packet amplification factor while retaining its
> projective `q`-phase.

If this anomaly forced `q` to divide the scalar local order for unbounded `q`, the existing
unbounded-divisibility lemma `LedgerTelescope.int_eq_zero_of_forall_pos_nat_dvd` would force that
order to be zero.  Ordinary packet rank, ordinary determinant rank, and Morita-normalized rank do
not supply this anomaly.

## Formal surface

- `finrank_weylPacketAmplification`
- `modulus_dvd_finrank_weylPacketAmplification`
- `packetDivisibility_holds_for_every_scalarRank`

## Verification

`lake env lean GaloisForLFunctions/RHTower/WeylPacketAmplificationBlindness.lean` passes on the
repository toolchain.

## Novelty and significance gate

The rank computation is standard finite-dimensional linear algebra.  No claim of new scientific
knowledge is made.  Its role is to isolate the exact non-tautological descent required by the
outlandish arbitrary-modulus route.

## Gates

- [x] 0 -> 1: full-packet modulus-divisibility shortcut stated
- [x] 1 -> 2: amplification formula and arbitrary-rank counterfamily proved
- [x] 2 -> 3: theorem formalized and checked
- [ ] 3 -> 4: not promoted; virtual anomaly descent remains open
