# CCM Guinand--Weil strict-positive source nonselection

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / source selection before finite quotient
- **Novelty scope:** corpus-new strict-positive strengthening of full-observer ambiguity and
  nonlinear no-decoder consequence; positive/negative decomposition and rank--nullity are classical
- **External anchor:** Akiva Groskin, arXiv:2607.02828, Corollary 2.4 supplies the exact finite
  source quotient but does not state this positive-cone nonselection theorem
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilPositiveSourceNonselection.lean`

## Strict-positive ambiguity

At level `N`, let `R>2N+1` event horizons be arbitrary. The full finite source observer has a
nonzero kernel vector `alpha`. Write its pointwise positive and negative parts as `alpha^+` and
`alpha^-`, and add a common positive baseline:

```text
left_i  = 1 + alpha_i^+,
right_i = 1 + alpha_i^-.                                         (1)
```

Then every `left_i` and `right_i` is strictly positive, while

```text
left-right=alpha!=0.                                               (2)
```

Linearity of the full observer and whole event-packet formation gives

```text
observer(left)=observer(right),
Packet(left)=Packet(right).                                        (3)
```

Thus overcomplete ambiguity is not confined to artificial signed directions or the boundary of a
positive cone. Distinct points in the cone's interior can lie in the same complete finite-matrix
fibre. If horizons are injective, these weight vectors represent distinct positive atomic sources
on the same finite support.

## Nonlinear no-decoder theorem

Lean proves that no function from finite CCM matrices to event weights can recover every source:

```text
not exists recover, LeftInverse recover Packet.                    (4)
```

More strongly, `(4)` remains true when the decoder's target and packet domain are restricted to
strictly positive weights. No linearity, continuity, measurability, equivariance, or naturality
assumption is placed on `recover`; equal matrices in `(3)` contradict any left inverse directly.

## CCM-FU consequence

Source positivity cannot be the missing canonical selector after quotienting. Four-unit central
normalization, all codiagonal coordinates, all weighted-cosine diagonals, and strict positivity of
every event weight still leave distinct representatives. A viable CCM-FU producer must select the
literal prime--pole--archimedean source before finite matrix formation and transport its provenance
through a source-native connection to the continued Xi Ward column.

This does not construct that transport and does not prove RH.

## Lean declarations

- `ccmGuinandWeilFiniteEventPacketMatrix_sub`
- `ccmGuinandWeilFiniteSource_exists_distinct_strictlyPositive_same_observation`
- `ccmGuinandWeilFiniteEventPacketMatrix_no_source_decoder`
- `CCMGuinandWeilStrictlyPositiveWeights`
- `ccmGuinandWeilFiniteEventPacketMatrix_no_strictlyPositive_source_decoder`

Targeted `lake env lean` and `lake build
GaloisForLFunctions.RHTower.CCMGuinandWeilPositiveSourceNonselection` pass. `#print axioms` reports
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`,
`admit`, `opaque`, or `unsafe` declaration is used.
