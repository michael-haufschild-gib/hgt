# Sectoral Kolchin signature of quantum fields — formalized

- **ID:** `sectoral-kolchin-signature-quantum-fields-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `sectoral-kolchin-signature-quantum-fields.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/KolchinSlopeDichotomy.lean` | the finite jet packet, the Kolchin jet rank `(1)`, the exact rank dichotomy `(2)`, and the normalized slope `(3)` with both characterizations |
| `HTGeometry/HypertranscendentalHorizonFunctionField.lean` | algebraic independence of every finite jet packet of an HT element |
| `HTGeometry/WickKolchinProfile.lean` | finite relative connected-sector rank; embedding and algebraic-counterterm invariance |
| `HTGeometry/SourceLogarithmicBoundary.lean` | HT equivalence for a nonzero reporter and its logarithmic derivative |
| `HTGeometry/DifferentialAdjoinMobiusGenerator.lean` | Möbius change of reporter generates the same differential field |
| `HTGeometry/GeometricCDDConstraint.lean`, `HTGeometry/GeometricCDDBoundarySelection.lean` | the finite CDD algebra and the unique one-sided shell response |
| `HTGeometry/KolchinExchangeGaugeObstruction.lean` | the exchange-law forcing used by the wedge-local and compact-local transfers |
| `HTGeometry/CollisionPhaseKolchinProduction.lean` | the collision phase-complexity production law and probability blindness |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `(1)` `kolchinJetRank` — the transcendence rank of the packet `{f, Df, …, D^r f}`, defined as the
  ordinary algebraic-matroid rank of the finite jet packet, so it needs no cardinal arithmetic;
- `(2)`, HT half: `kolchinJetRank_eq_of_hypertranscendentalOver` — for a hypertranscendental
  reporter the rank is exactly `r + 1`, the number of visible jet layers;
- `(2)`, DA half: `exists_kolchinJetRank_le_of_differentialAlgebraicOver` — a differentially
  algebraic reporter has one jet algebraic over its strict predecessors, every jet is then algebraic
  over that fixed finite prefix, and the rank is uniformly bounded;
- `(3)` `tendsto_kolchinSlope_one_of_hypertranscendentalOver`,
  `tendsto_kolchinSlope_zero_of_differentialAlgebraicOver` — the normalized slope converges, to `1`
  in the HT case and to `0` in the DA case;
- the exact dichotomy: `tendsto_kolchinSlope_one_iff_hypertranscendentalOver` and
  `tendsto_kolchinSlope_zero_iff_differentialAlgebraicOver` — slope `1` **characterizes**
  hypertranscendence and slope `0` **characterizes** differential algebraicity, so the signature is
  a genuine invariant and not merely a sufficient marker;
- reporter invariance item 1: `differentialAdjoin_mobius_generator`;
- reporter invariance items 2–3: `HTGeometry.transcendenceRank_image_algHom`,
  `connectedJetPacket_mono_sectors` and `hypertranscendentalOver_deriv_div_self_iff`;
- the sectoral inputs already certified elsewhere:
  `finiteDifferentialJet_algebraicIndependent_of_hypertranscendentalOver`,
  `geometricCDDLogPhaseSlope_pos`, `section_hypertranscendental_of_exchangeLaw`,
  `hypertranscendentalOver_outgoingPacket_iff`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/KolchinSlopeDichotomy.lean
lake build GaloisForLFunctions.HTGeometry.KolchinSlopeDichotomy
```

## What closed last

The differentially algebraic half of `(2)`.  Hypertranscendence gives the rank `r + 1` immediately
from algebraic independence of the jet sequence, but the bounded-rank half needs the classical
separant argument: a differentially algebraic element has a first jet algebraic over the field its
strict predecessors generate, and from there every jet is algebraic over that one fixed prefix.
Those two steps existed in the corpus only as private lemmas of the differential-algebraic
transitivity file; they are now public, and the matroid rank of any jet packet is bounded by the
cardinality of the prefix packet.  Combining the two halves with uniqueness of limits turns the
sufficient conditions into the exact characterization: convergence of the normalized slope is
automatic, and its value is a complete invariant of the DA/HT class.

## Boundary

The card's remaining gates are its own labelled open core `(18)` — the LSZ/Haag–Ruelle transfer
from local matrix elements to the face-complete higher connected response — and external novelty
and physics review.  Those are onward theorems and literature obligations, not formalization
obligations for the content proved here.  The card's item 4 of reporter invariance (invariance of
the physical S-matrix under local field redefinition) is cited standard physics, and is stated on
the card as such.
